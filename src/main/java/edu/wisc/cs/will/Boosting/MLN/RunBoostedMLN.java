package edu.wisc.cs.will.Boosting.MLN;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import edu.wisc.cs.will.Boosting.EM.HiddenLiteralSamples;
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
		Map<String, LearnBoostedRDN> learners = new HashMap<String, LearnBoostedRDN>();
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
			iterStepSize = cmdArgs.getMaxTreesVal();
		}

		if ((cmdArgs.getHiddenStrategy().equals("EM") || cmdArgs.getHiddenStrategy().equals("MAP"))
				&& setup.getHiddenExamples() != null) {
			iterStepSize = 2;
		}
		if (cmdArgs.getRdnIterationStep() != -1) {
			iterStepSize  = cmdArgs.getRdnIterationStep();
		}
		boolean newModel=true;
		for (int i=0; i < cmdArgs.getMaxTreesVal(); i+=iterStepSize) {
			if ((cmdArgs.getHiddenStrategy().equals("EM") || cmdArgs.getHiddenStrategy().equals("MAP"))  
					&& setup.getHiddenExamples() != null && newModel) {
					long sampleStart = System.currentTimeMillis();
					JointModelSampler jtSampler = new JointModelSampler(fullModel, setup, cmdArgs, false);
					HiddenLiteralSamples sampledStates = new HiddenLiteralSamples();
					setup.addAllExamplesToFacts();
					if ( i > minTreesInModel) { minTreesInModel = i; } 
					
					
					
					int maxSamples = 30*((minTreesInModel/iterStepSize) + 1);
					maxSamples = 500;
					// TODO (tvk) Get more samples but pick the 200 most likely states.
					if (cmdArgs.getHiddenStrategy().equals("MAP")) { 
						maxSamples = -1; 
					}
					boolean returnMap = false;
					if (cmdArgs.getHiddenStrategy().equals("MAP")) {
						returnMap = true;
					}
					jtSampler.sampleWorldStates(setup.getHiddenExamples(), sampledStates, false, maxSamples, returnMap);
					if (sampledStates.getWorldStates().size() == 0) { Utils.waitHere("No sampled states");}
					// This state won't change anymore so cache probs;
					Utils.println("Building assignment map");
					sampledStates.buildExampleToAssignMap();
					
					if (cmdArgs.getHiddenStrategy().equals("EM")) {
						// Build the probabilities for each example conditioned on the assignment to all other examples
						Utils.println("Building probability map");
						sampledStates.buildExampleToCondProbMap(setup, fullModel);
						if (cmdArgs.getNumberOfHiddenStates() > 0 ) {
							Utils.println("Picking top K");
							sampledStates.pickMostLikelyStates(cmdArgs.getNumberOfHiddenStates());
						}
					}
					setup.setLastSampledWorlds(sampledStates);
					newModel = false;
					long sampleEnd = System.currentTimeMillis();
					Utils.println("Time to sample world state: " + Utils.convertMillisecondsToTimeSpan(sampleEnd-sampleStart));
				}
			for (String pred : cmdArgs.getTargetPredVal()) {

				if (fullModel.get(pred).getNumTrees() >= (i+iterStepSize)) {
					continue;
				}
				int currIterStep =  (i+iterStepSize) - fullModel.get(pred).getNumTrees();
				Utils.println("% Learning " + currIterStep + " trees in this iteration for " + pred);
				newModel = true;
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
		Set<String> modelPreds = cmdArgs.getLoadPredModelVal();
		if (modelPreds == null) {
			modelPreds = cmdArgs.getTargetPredVal();
		}
		for (String pred : modelPreds) {
			ConditionalModelPerPredicate rdn;
			if (fullModel.containsKey(pred)) {
				rdn = fullModel.get(pred);
				rdn.reparseModel(setup);
			} else {
				Utils.println("% Did not learn a model for '" + pred + "' this run.");
				// YapFile doesn't matter here.
				rdn = new ConditionalModelPerPredicate(setup);
			
				if (useSingleTheory(setup)) {
					rdn.setHasSingleTheory(true);
					rdn.setTargetPredicate(pred);
					rdn.loadModel(LearnBoostedRDN.getWILLFile(cmdArgs.getModelDirVal(), cmdArgs.getModelFileVal(), pred), setup, cmdArgs.getMaxTreesVal());
				} else {
					rdn.loadModel(BoostingUtils.getModelFile(cmdArgs, pred, true), setup, cmdArgs.getMaxTreesVal());
				}
				rdn.setNumTrees(cmdArgs.getMaxTreesVal());
				fullModel.put(pred, rdn);
			}
		}
	}
	
	public void infer() {
		InferBoostedRDN infer = new InferBoostedRDN(cmdArgs, setup);
		infer.runInference(fullModel, 0.5);
	}
	
	private boolean useSingleTheory(WILLSetup setup2) {
		String lookup;
		if ((lookup =  setup2.getHandler().getParameterSetting("singleTheory")) != null) {
			return Boolean.parseBoolean(lookup);
		}
		return false;
	}
}

