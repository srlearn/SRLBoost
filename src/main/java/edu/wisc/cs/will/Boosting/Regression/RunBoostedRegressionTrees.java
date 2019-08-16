package edu.wisc.cs.will.Boosting.Regression;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.LearnBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.Utils.Utils;

/**
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
		String yapFile = cmdArgs.getYapBiasVal();

		for (String pred : cmdArgs.getTargetPredVal()) {
			if (cmdArgs.getTargetPredVal().size() > 1) {
				yapFile = getYapFileForPredicate(pred, cmdArgs.getYapBiasVal());
				Utils.println("% Using yap file:" + yapFile);
			}

			LearnBoostedRDN      learner       = new LearnBoostedRDN(cmdArgs, setup);
			String               saveModelName = BoostingUtils.getModelFile(cmdArgs, pred, true);
			learner.setYapSettingsFile(yapFile);
			learner.setTargetPredicate(pred);

			ConditionalModelPerPredicate model = new ConditionalModelPerPredicate(setup);

			SRLInference sampler = new RegressionTreeInference(model, setup);
			learner.learnNextModel(this, sampler, model, cmdArgs.getMaxTreesVal());
			model.saveModel(saveModelName);
			// Do a final save since learnModel doesn't save every time (though we should make it do so at the end).
			// No need for checkpoint file anymore
			clearCheckPointFiles(saveModelName);
			fullModel.put(pred, model); 
		}
	
	}

	private String getYapFileForPredicate(String target, String yapFile) {
		if (yapFile.isEmpty()) { return ""; }
		int pos = yapFile.lastIndexOf("/");
		return yapFile.substring(0, pos+1) + target + "_" + yapFile.substring(pos + 1);
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
				// YapFile doesn't matter here.
				rdn = new ConditionalModelPerPredicate(setup);
			
				if (useSingleTheory(setup)) {
					rdn.setHasSingleTheory(true);
					rdn.setTargetPredicate(pred);
					rdn.loadModel(LearnBoostedRDN.getWILLFile(cmdArgs.getModelDirVal(), cmdArgs.getModelFileVal(), pred), setup, cmdArgs.getMaxTreesVal());
				} else {
					rdn.setTargetPredicate(pred);
					rdn.loadModel(BoostingUtils.getModelFile(cmdArgs, pred, true), setup, cmdArgs.getMaxTreesVal());
				}
				rdn.setNumTrees(cmdArgs.getMaxTreesVal());
				fullModel.put(pred, rdn);
			}
		}
	}
	
	public void infer() {
		InferRegressionTrees infer = new InferRegressionTrees(cmdArgs, setup);
		infer.runInference(fullModel);
	}
	
	private boolean useSingleTheory(WILLSetup setup2) {
		String lookup;
		if ((lookup =  setup2.getHandler().getParameterSetting("singleTheory")) != null) {
			return Boolean.parseBoolean(lookup);
		}
		return false;
	}

	public static void main(String[] args) {
		// TODO(@hayesall): This can most likely be removed since edu.wisc.cs.will.Boosting.Common.RunBoostedModels is the main class.

		args = Utils.chopCommentFromArgs(args);
		CommandLineArguments cmd = RunBoostedModels.parseArgs(args);
		if (cmd == null) {
			Utils.error(CommandLineArguments.getUsageString());
		}
		RunBoostedModels runClass;
		runClass = new RunBoostedRegressionTrees();
		if (!cmd.isLearnRegression()) {
			Utils.waitHere("Set \"-reg\"  in cmdline arguments to ensure that we intend to learn regression trees. Will now learn regression trees.");
			cmd.setLearnRegression(true);
		}
		runClass.setCmdArgs(cmd);
		runClass.runJob();
	}
}

