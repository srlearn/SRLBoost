package edu.wisc.cs.will.Boosting.OneClass;

import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.DataSetUtils.ComputeAUC;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author tkhot
 */
class InferOCCModel {

	private final WILLSetup setup;
	
	private final CommandLineArguments cmdArgs;

	InferOCCModel(CommandLineArguments cmdArgs, WILLSetup setup) {
		this.cmdArgs = cmdArgs;
		this.setup = setup;
	}

	void runInference(Map<String, PropositionalizationModel> fullModel) {
		Map<String,List<RegressionRDNExample>> jointExamples = setup.getJointExamples(cmdArgs.getTargetPredVal());
		subsampleNegatives(jointExamples);
		Utils.println("\n% Starting inference in OCC.");
		
		for (String pred : jointExamples.keySet()) {
			List<RegressionRDNExample> examples = jointExamples.get(pred);
			PropositionalizationModel propModel = fullModel.get(pred);
			
			if (propModel == null) {
				Utils.error("No model learned for " + pred);
				return;
			}
			
			for (RegressionRDNExample example : examples) {
				propModel.getFeatureVector(example);
				double prob = getExampleProb(example, propModel);
				example.setProbOfExample(new ProbDistribution(prob));
			}
			ComputeAUC auc = computeAUCFromEg(examples, pred);
			Utils.println(   "\n%   AUC ROC   = " + Utils.truncate(auc.getROC(), 6));
			Utils.println(     "%   AUC PR    = " + Utils.truncate(auc.getPR(),  6));
			Utils.println(     "%   CLL	      = " + Utils.truncate(auc.getCLL(),  6));
	
		}
	}

	private double getExampleProb(RegressionRDNExample example,
		PropositionalizationModel propModel) {
			FeatureVector egVec = propModel.getFeatureVector(example);
			KernelEstimator kEst = new KernelEstimator();
			List<Double> dists = new ArrayList<>();
			for (FeatureVector fvec : propModel.getOneClassExamples()) {
				double dist = egVec.getDistance(fvec);
				dists.add(dist);
			}
			return kEst.getProbabilityFromDistance(dists);
	}

	private void subsampleNegatives(Map<String, List<RegressionRDNExample>> jointExamples) {
		if (cmdArgs.getTestNegsToPosRatioVal() < 0) {
			return; // No subsampling.
		}
		Map<String,Integer> numpos = new HashMap<>();
		Map<String,Integer> numneg = new HashMap<>();
		for (String  pred : jointExamples.keySet()) {
			numpos.put(pred, 0);
			numneg.put(pred, 0);
			for (RegressionRDNExample rex : jointExamples.get(pred)) {
				if (rex.isOriginalTruthValue()) {
					numpos.put(pred, numpos.get(pred) + 1);  // JWS: should count then do one PUT at the end.
				} else {
					numneg.put(pred, numneg.get(pred) + 1);
				}
			}
		}		
		
		// Subsample negative examples.
		for (String target : jointExamples.keySet()) {
			int pos = numpos.get(target);
			int neg = numneg.get(target);
			Utils.println("% Initial size of testset negs: " + Utils.comma(neg) + " for " + target);
			double sampleNeg = cmdArgs.getTestNegsToPosRatioVal();
			// get the sampling prob
			double sampleProb = sampleNeg * ((double)pos / (double)neg);

			// Don't sample if sampleProb is negative.
			if (sampleProb > 0) {

				// Rather than randomly sampling, we sample deterministically so that all runs get the same testset examples
				// Since the seed is fixed,the random number generator would return the same values.
				Random rand = new Random(1729);

				// Reverse order so that we can delete it.
				neg=0;
				for (int i = jointExamples.get(target).size()-1; i>=0 ; i--) {
					RegressionRDNExample rex = jointExamples.get(target).get(i);
					if (!rex.isOriginalTruthValue()) {
						// Remove this example, as we are subsampling.
						if (rand.nextDouble() >= sampleProb) {
							jointExamples.get(target).remove(i);
						} else {
							neg++;
						}
					}
				}
				Utils.println("% Final size of negs: " + Utils.comma(neg) + " for " + target);
			}
		}
	}


	private ComputeAUC computeAUCFromEg(List<RegressionRDNExample> examples, String target) {
		Utils.println("\n% Computing Area Under Curves.");
		List<Double> positiveProbs = new ArrayList<>(); // TODO - need to handle WEIGHTED EXAMPLES.  Simple approach: have a eachNegRepresentsThisManyActualNegs and make this many copies.
		List<Double> negativeProbs = new ArrayList<>();
		for (RegressionRDNExample regressionRDNExample : examples) {
			// This code should only be called for single-class examples
			double  prob  = regressionRDNExample.getProbOfExample().getProbOfBeingTrue();
			boolean isPos = regressionRDNExample.isOriginalTruthValue();
			if (isPos) {
				positiveProbs.add(prob);
			} else {
				negativeProbs.add(prob);
			}
		}
		// If models are being written somewhere, then also write AUC's there (this allows us to avoid writing in a dir that only contains INPUT files) - hence, multiple runs can simultaneously use the same input dir, yet write to different output dirs.
		String aucTempDirectory;

		aucTempDirectory = setup.getOuterLooper().getWorkingDirectory() + "/AUC/";
		if (cmdArgs.getTargetPredVal().size() > 1) {
			aucTempDirectory += target + "/";
		}
		ComputeAUC.deleteAUCfilesAfterParsing = false;
		double minRecallForAUCPR = 0;
		return new ComputeAUC(positiveProbs, negativeProbs, aucTempDirectory, cmdArgs.getAucPathVal(), "", minRecallForAUCPR, true);
	}
}
