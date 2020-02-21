package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import edu.wisc.cs.will.Boosting.EM.HiddenLiteralSamples;
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
	public static final int numbModelsToMake = 1;

	// "Run1"; // NOTE: file names will look best if this starts with a capital letter.  If set (ie, non-null), will write testset results out.
	static final String nameOfCurrentModel = null;

	public void learn() {
		fullModel = new JointRDNModel();
		String yapFile;
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
				// Setup facts based on the true data
				setup.addAllExamplesToFacts();
				if ( i > minTreesInModel) { minTreesInModel = i; }

				// TODO(@hayesall): Which is it?
				int maxSamples = 30*((minTreesInModel/iterStepSize) + 1);
				maxSamples = 500;

				// TODO(@tushar): Get more samples but pick the 200 most likely states.

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
						Utils.println("Picking top K=" + cmdArgs.getNumberOfHiddenStates());
						sampledStates.pickMostLikelyStates(cmdArgs.getNumberOfHiddenStates());
					}
				}
				double cll = BoostingUtils.computeHiddenStateCLL(sampledStates, setup.getHiddenExamples());
				Utils.println("CLL of hidden states:" + cll);
				//Utils.println("Prob of states: " + sampledStates.toString());
				setup.setLastSampledWorlds(sampledStates);
				newModel = false;
				long sampleEnd = System.currentTimeMillis();
				Utils.println("Time to sample world state: " + Utils.convertMillisecondsToTimeSpan(sampleEnd-sampleStart));
			}
			for (String pred : cmdArgs.getTargetPredVal()) {
				SingleModelSampler sampler = new SingleModelSampler(fullModel.get(pred), setup, fullModel, false);
				if (cmdArgs.getTargetPredVal().size() > 1) {
					yapFile = getYapFileForPredicate(pred, cmdArgs.getYapBiasVal());
					Utils.println("% Using yap file:" + yapFile);
				}
			
				if (fullModel.get(pred).getNumTrees() >= (i+iterStepSize)) {
					continue;
				}
				int currIterStep =  (i+iterStepSize) - fullModel.get(pred).getNumTrees();
				newModel=true;
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


