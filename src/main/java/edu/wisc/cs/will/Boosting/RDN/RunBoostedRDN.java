package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Utils.Utils;

import java.util.HashMap;
import java.util.Map;

/*
 * @author Tushar Khot
 */
public class RunBoostedRDN extends RunBoostedModels {

	private JointRDNModel fullModel;
	public RunBoostedRDN() {
		fullModel = null;
	}
	
	public void runJob() {
		if (cmdArgs.isLearnVal()) {
			Utils.println("\n% Starting a LEARNING run of bRDN.");
			long start = System.currentTimeMillis();
			learnModel();
			long end = System.currentTimeMillis();
			Utils.println("\n% Total learning time ("  + Utils.comma(cmdArgs.getMaxTreesVal()) + " trees): " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
		}
		if (cmdArgs.isInferVal()) {
			Utils.println("\n% Starting an INFERENCE run of bRDN.");
			long   start    = System.currentTimeMillis();
			inferModel();
			long end = System.currentTimeMillis();
			Utils.println("\n% Total inference time (" + Utils.comma(cmdArgs.getMaxTreesVal()) + " trees): " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
		}
	}

	// TODO(?): Allow this to be settable.
	// 		Each 'tree' in the sequence of the trees is really a forest of this size.
	static final int numbModelsToMake = 1;

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
			if (cmdArgs.useCheckPointing()) {
				learner.loadCheckPointModel(fullModel.get(pred));
			}
			minTreesInModel = Math.min(fullModel.get(pred).getNumTrees(), minTreesInModel);
		}

		int iterStepSize = cmdArgs.getMaxTreesVal();

		for (int i=0; i < cmdArgs.getMaxTreesVal(); i+=iterStepSize) {

			for (String pred : cmdArgs.getTargetPredVal()) {
				SingleModelSampler sampler = new SingleModelSampler(fullModel.get(pred), setup, fullModel);
				if (cmdArgs.getTargetPredVal().size() > 1) {
					throw new RuntimeException("Multiple targets is deprecated.");
				}
			
				if (fullModel.get(pred).getNumTrees() >= (i+iterStepSize)) {
					continue;
				}
				int currIterStep =  (i+iterStepSize) - fullModel.get(pred).getNumTrees();
				Utils.println("% Learning " + currIterStep + " trees in this iteration for " + pred);
				learners.get(pred).learnNextModel(sampler, fullModel.get(pred), currIterStep);
			}
		}

		// Only clear checkpoint after all models are learned.
		for (String pred : cmdArgs.getTargetPredVal()) {
			String saveModelName = BoostingUtils.getModelFile(cmdArgs, pred,  true);
			// Do a final save since learnModel() doesn't save every time (though we should make it do so at the end).
			fullModel.get(pred).saveModel(saveModelName);

			// No need for checkpoint file anymore.
			clearCheckPointFiles(saveModelName);
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

				rdn.setTargetPredicate(pred);
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


