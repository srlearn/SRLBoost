package edu.wisc.cs.will.Boosting.MLN;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import edu.wisc.cs.will.Boosting.RDN.*;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.FOPC.AllOfFOPC;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/*
 * MLN-Boost specific code for learning and inference
 * For e.g. RDN-Boost learns all the trees for one predicate at a time whereas MLN-Boost learns
 * one tree at a time for every predicate
 * Also sets the required flags for MLN-Boost.
 * @author tkhot
 *
 */
public class RunBoostedMLN extends RunBoostedModels {

	private JointRDNModel fullModel = null;
	
	public void learn() {
		fullModel = new JointRDNModel();
		Map<String, LearnBoostedRDN> learners = new HashMap<>();
		int minTreesInModel = Integer.MAX_VALUE;
		
		
		for (String pred : cmdArgs.getTargetPredVal()) {
			fullModel.put(pred, new ConditionalModelPerPredicate(setup));
			fullModel.get(pred).setTargetPredicate(pred);
			
			LearnBoostedRDN learner = new LearnBoostedRDN(cmdArgs, setup);
			learner.setTargetPredicate(pred);
			learners.put(pred, learner);
			if( cmdArgs.useCheckPointing()) {
				learner.loadCheckPointModel(fullModel.get(pred));
			}
			minTreesInModel = Math.min(fullModel.get(pred).getNumTrees(), minTreesInModel);
		}
		MLNInference sampler = new MLNInference(setup, fullModel);
		
		int iterStepSize = 1;
		if (cmdArgs.getTargetPredVal().size() == 1) {
			// TODO(hayesall): This should always be true.
			iterStepSize = cmdArgs.getMaxTreesVal();
		}

		for (int i=0; i < cmdArgs.getMaxTreesVal(); i+=iterStepSize) {
			for (String pred : cmdArgs.getTargetPredVal()) {

				if (fullModel.get(pred).getNumTrees() >= (i+iterStepSize)) {
					continue;
				}
				int currIterStep =  (i+iterStepSize) - fullModel.get(pred).getNumTrees();
				Utils.println("% Learning " + currIterStep + " trees in this iteration for " + pred);
				learners.get(pred).learnNextModel(sampler, fullModel.get(pred), currIterStep);
			}
		}
		
		for (String pred : cmdArgs.getTargetPredVal()) {
			String saveModelName = BoostingUtils.getModelFile(cmdArgs, pred, true);
			fullModel.get(pred).saveModel(saveModelName); // Do a final save since learnModel doesn't save every time (though we should make it do so at the end).
			// No need for checkpoint file anymore
			clearCheckPointFiles(saveModelName);
		}
	
	}
	@Override
	protected void afterLearn() {
		super.afterLearn();
		if (cmdArgs.isLearningMLNClauses()) {
			saveModelAsMLN();			
		}
	}

	private void saveModelAsMLN() {

		String mlnFile=setup.getOuterLooper().getWorkingDirectory() + "/"+
		(cmdArgs.getModelFileVal() == null ? "" : cmdArgs.getModelFileVal()) + ".mln";
		BufferedWriter writer = null;
		try {
			writer = new BufferedWriter(new CondorFileWriter(mlnFile));
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		AllOfFOPC.printUsingAlchemyNotation = true;
		boolean oldSTD = setup.getHandler().usingStdLogicNotation();
		boolean oldAnon = setup.getHandler().underscoredAnonymousVariables;
		setup.getHandler().underscoredAnonymousVariables=false;
		setup.getHandler().prettyPrintClauses=false;
		setup.getHandler().useStdLogicNotation();
		
		Set<String> modes = setup.getInnerLooper().getAlchemyModeStrings(setup.getInnerLooper().getBodyModes());
		modes.addAll(setup.getInnerLooper().getAlchemyModeStrings(setup.getInnerLooper().getTargetModes()));
		for (String str : modes) {
			try {
				writer.write(str);
				writer.newLine();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		
		for (ConditionalModelPerPredicate model : fullModel.values()) {
			for (Entry<Clause, Double> entry : model.convertToSingleMLN().entrySet()) {
				try {
					entry.getKey().setWeightOnSentence(entry.getValue());
					writer.write(entry.getKey().toString());
					writer.newLine();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
		if (!oldSTD) {
			setup.getHandler().usePrologNotation();
		}
		setup.getHandler().underscoredAnonymousVariables = oldAnon;
		AllOfFOPC.printUsingAlchemyNotation = false;
		try {
			writer.close();
		} catch (IOException e) {
			e.printStackTrace();
		}

	}
	
	public void loadModel() {

		if (fullModel == null) {
			fullModel = new JointRDNModel();
		}

		Utils.println("\n% Getting bRDN's target predicates.");

		for (String pred : cmdArgs.getTargetPredVal()) {
			ConditionalModelPerPredicate rdn;
			if (fullModel.containsKey(pred)) {
				rdn = fullModel.get(pred);
				rdn.reparseModel(setup);
			} else {
				Utils.println("% Did not learn a model for '" + pred + "' this run.");
				rdn = new ConditionalModelPerPredicate(setup);

				rdn.loadModel(BoostingUtils.getModelFile(cmdArgs, pred, true), setup, cmdArgs.getMaxTreesVal());
				rdn.setNumTrees(cmdArgs.getMaxTreesVal());
				fullModel.put(pred, rdn);
			}
		}
	}
	
	public void infer() {
		InferBoostedRDN infer = new InferBoostedRDN(cmdArgs, setup);
		infer.runInference(fullModel, 0.5);
	}

}

