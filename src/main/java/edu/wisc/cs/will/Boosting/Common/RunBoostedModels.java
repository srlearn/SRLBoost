package edu.wisc.cs.will.Boosting.Common;

import edu.wisc.cs.will.Boosting.MLN.RunBoostedMLN;
import edu.wisc.cs.will.Boosting.RDN.RunBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.Regression.RunBoostedRegressionTrees;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;

import java.io.File;

/**
 * Generic code to call MLN-Boost and RDN-Boost
 * @author tkhot
 */
public abstract class RunBoostedModels {

	protected CommandLineArguments cmdArgs;

	private void setCmdArgs(CommandLineArguments cmdArgs) {
		this.cmdArgs = cmdArgs;
	}

	protected WILLSetup  setup;
	
	protected RunBoostedModels() {
		
	}
	
	private static CommandLineArguments parseArgs(String[] args) {
		CommandLineArguments cmdArgs = new CommandLineArguments();
		if (cmdArgs.parseArgs(args)) {
			return cmdArgs;
		}
		return null;
	}
	
	protected void runJob() {
		if (cmdArgs.isLearnVal()) {
			long start = System.currentTimeMillis();
			learnModel();
			long end = System.currentTimeMillis();
			Utils.println("\n% Total learning time ("  + Utils.comma(cmdArgs.getMaxTreesVal()) + " trees): " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
		}
		
		if (cmdArgs.isInferVal()) {
			long   start    = System.currentTimeMillis();
			inferModel();
			long end = System.currentTimeMillis();
			Utils.println("\n% Total inference time (" + Utils.comma(cmdArgs.getMaxTreesVal()) + " trees): " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
		}
		
	}

	protected abstract void learn();
	
	protected void learnModel() {
		setupWILLForTrain();
		beforeLearn();
		learn();
		afterLearn();
	}

	private void setupWILLForTrain() {
		setup     = new WILLSetup();
		Utils.println("\n% Calling SETUP.");
		setup.setup(cmdArgs, cmdArgs.getTrainDirVal(), true);
	}
	
	/**
	 * Override this method if you want to take some steps before calling learn.
	 */
	private void beforeLearn() {
		Utils.println(cmdArgs.getModelDirVal());
		File dir = new CondorFile(cmdArgs.getModelDirVal());
		Utils.ensureDirExists(dir);
		
		// Rename old model files to prevent accidental re-use.
		renameOldModelFiles();
	}

	/**
	 * Override to call methods after learning.
	 */
	protected void afterLearn() {
		Utils.println("cached groundings hit: " + setup.getInnerLooper().num_hits + "\nMisses: " +setup.getInnerLooper().num_misses);
	}
	
	protected void clearCheckPointFiles(String saveModelName) {
		if (Utils.fileExists(BoostingUtils.getCheckPointFile(saveModelName))) {
			Utils.delete(BoostingUtils.getCheckPointFile(saveModelName));
		}
		if (Utils.fileExists(BoostingUtils.getCheckPointExamplesFile(saveModelName))) {
			Utils.delete(BoostingUtils.getCheckPointExamplesFile(saveModelName));
		}
		if (Utils.fileExists(BoostingUtils.getCheckPointFlattenedLitFile(saveModelName))) {
			Utils.delete(BoostingUtils.getCheckPointFlattenedLitFile(saveModelName));
		}
		
	}
	private void renameOldModelFiles() {
		int numbModelsToMake = 1;
		for (int i = 0; i < numbModelsToMake; i++) {
			// Rename model files.
			for (String pred : cmdArgs.getTargetPredVal()) {
				String filename = BoostingUtils.getModelFile(cmdArgs, pred, true);
				File f = new CondorFile(filename);
				if (f.exists()) {
					renameAsOld(f);
				}
			}
		}		
	}

	
	public static void renameAsOld(File f) {
		String justFileName = f.getName();
		File   parent       = f.getParentFile();
		File   newF         = new CondorFile(parent, "old_" + justFileName);
	
		if (newF.exists()) {
			if (!newF.delete()) {
				Utils.error("Couldn't delete the file: " + newF.getAbsolutePath());
			}
		}
		if (!f.renameTo(newF)) {
			Utils.error("Couldn't rename from " + f.getAbsolutePath() + " to " + newF.getAbsolutePath());
		}
	}
	
	protected abstract void loadModel();
	
	protected abstract void infer();
	protected void inferModel() {
		if(!setupWILLForTest()) {
			return;
		}
		beforeInfer();
		infer();
	}

	private void beforeInfer() {
		loadModel();
	}

	private boolean setupWILLForTest() {
		setup = new WILLSetup();
		if(!setup.setup(cmdArgs, cmdArgs.getTestDirVal(), false)) {
			Utils.println("\nSetup failed (possibly because there are no examples), so will not infer anything.");
			return false;
		}
		return true;
	}

	public static void main(String[] args) {
		
		args = Utils.chopCommentFromArgs(args); 
		CommandLineArguments cmd = RunBoostedModels.parseArgs(args);
		if (cmd == null) {
			Utils.error(CommandLineArguments.getUsageString());
		}
		RunBoostedModels runClass;
		if (cmd.isLearnMLN()) {
			runClass = new RunBoostedMLN();
		} else {
			if (cmd.isLearnRegression()) {
				runClass = new RunBoostedRegressionTrees();
			}
			else {
				runClass = new RunBoostedRDN();
			}
		}
		runClass.setCmdArgs(cmd);
		runClass.runJob();
	}
	
}
