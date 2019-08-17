package edu.wisc.cs.will.Boosting.OneClass;

import java.util.HashMap;
import java.util.Map;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author tkhot
 */
public class RunOneClassModel extends RunBoostedModels {

	private Map<String, PropositionalizationModel> fullModel;

	public RunOneClassModel() {
		fullModel = new HashMap<>();
	}

	@Override
	public void learn() {
		Map<String, LearnOCCModel> learners = new HashMap<>();
		int minTreesInModel = Integer.MAX_VALUE;
		
		
		for (String pred : cmdArgs.getTargetPredVal()) {
			fullModel.put(pred, new PropositionalizationModel());
			fullModel.get(pred).setTargetPredicate(pred);
			
			LearnOCCModel learner = new LearnOCCModel(cmdArgs, setup);
			learner.setTargetPredicate(pred);
			learners.put(pred, learner);
			if( cmdArgs.useCheckPointing()) {
				learner.loadCheckPointModel(fullModel.get(pred));
			}
			minTreesInModel = Math.min(fullModel.get(pred).getNumTrees(), minTreesInModel);
		}
	
	
		int iterStepSize = 1;
		iterStepSize = cmdArgs.getMaxTreesVal();

		if (cmdArgs.getRdnIterationStep() != -1) {
			iterStepSize  = cmdArgs.getRdnIterationStep();
		}
		for (int i=0; i < cmdArgs.getMaxTreesVal(); i+=iterStepSize) {
		
			for (String pred : cmdArgs.getTargetPredVal()) {

				if (fullModel.get(pred).getNumTrees() >= (i+iterStepSize)) {
					continue;
				}
				int currIterStep =  (i+iterStepSize) - fullModel.get(pred).getNumTrees();
				Utils.println("% Learning " + currIterStep + " trees in this iteration for " + pred);
				learners.get(pred).learnNextModel(this, fullModel.get(pred), currIterStep);
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
	public void loadModel() {
		if (fullModel == null) {
			fullModel = new HashMap<>();
		}

		Utils.println("\n% Getting occ's target predicates.");
		for (String pred : cmdArgs.getTargetPredVal()) {
			PropositionalizationModel propModel = null;
			if (fullModel.containsKey(pred)) {
				propModel = fullModel.get(pred);
				propModel.reparseModel(setup);
			} else {
				Utils.println("% Did not learn a model for '" + pred + "' this run.");
				// YapFile doesn't matter here.
				propModel = new PropositionalizationModel();
				propModel.setTargetPredicate(pred);
				propModel.loadModel(BoostingUtils.getModelFile(cmdArgs, pred, true), setup, cmdArgs.getMaxTreesVal());
				
				propModel.setNumTrees(cmdArgs.getMaxTreesVal());
				fullModel.put(pred, propModel);
			}
		}
		

	}

	@Override
	public void infer() {
		InferOCCModel infer = new InferOCCModel(cmdArgs, setup);
		infer.runInference(fullModel);

	}

}
