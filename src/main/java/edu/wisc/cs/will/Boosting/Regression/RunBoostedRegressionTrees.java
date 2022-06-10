package edu.wisc.cs.will.Boosting.Regression;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.LearnBoostedRDN;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Utils.Utils;

/*
 * MLN-Boost specific code for learning and inference
 * For e.g. RDN-Boost learns all the trees for one predicate at a time whereas MLN-Boost learns
 * one tree at a time for every predicate
 * Also sets the required flags for MLN-Boost.
 * @author tkhot
 *
 */
public class RunBoostedRegressionTrees extends RunBoostedModels {

	private JointRDNModel fullModel = null;
	
	public void learn() {

		fullModel = new JointRDNModel();

		for (String pred : cmdArgs.getTargetPredVal()) {
			if (cmdArgs.getTargetPredVal().size() > 1) {
				Utils.error("Yap is not available.");
			}

			LearnBoostedRDN      learner       = new LearnBoostedRDN(cmdArgs, setup);
			String               saveModelName = BoostingUtils.getModelFile(cmdArgs, pred, true);
			learner.setTargetPredicate(pred);

			ConditionalModelPerPredicate model = new ConditionalModelPerPredicate(setup);

			SRLInference sampler = new RegressionTreeInference(model, setup);
			learner.learnNextModel(sampler, model, cmdArgs.getMaxTreesVal());
			model.saveModel(saveModelName);
			// Do a final save since learnModel doesn't save every time (though we should make it do so at the end).
			// No need for checkpoint file anymore
			clearCheckPointFiles(saveModelName);
			fullModel.put(pred, model); 
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
		InferRegressionTrees infer = new InferRegressionTrees(cmdArgs, setup);
		infer.runInference(fullModel);
	}

}

