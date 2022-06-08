package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.MLN.MLNInference;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.Boosting.Utils.ThresholdSelector;
import edu.wisc.cs.will.DataSetUtils.ComputeAUC;
import edu.wisc.cs.will.ILP.CoverageScore;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.util.*;


public class InferBoostedRDN {

	private final boolean writeQueryAndResults = true;

	private final CommandLineArguments cmdArgs;
	private final WILLSetup setup;

	public InferBoostedRDN(CommandLineArguments args, WILLSetup setup) {
		this.cmdArgs = args;
		this.setup = setup;
	}
	
	public void runInference(JointRDNModel rdns) {

		// TODO(hayesall): threshold was constant, so I'm inlining the 0.5 value.
		double thresh = 0.5;

		Map<String,List<RegressionRDNExample>> targetExamples = setup.getJointExamples(cmdArgs.getTargetPredVal());
		Map<String,List<RegressionRDNExample>> jointExamples;
		jointExamples = new HashMap<>(targetExamples);
		boolean negativesSampled = false;
		
		Utils.println("\n% Starting inference in bRDN.");
		SRLInference sampler;
		if (cmdArgs.isLearnMLN()) {
			if (jointExamples.keySet().size() > 1) {
				sampler = new JointModelSampler(rdns, setup, true);
			} else {
				Utils.println("\n% Subsampling the negative examples.");
				subsampleNegatives(jointExamples);
				negativesSampled = true;
				sampler = new MLNInference(setup, rdns);
			}
		} else {
			sampler = new JointModelSampler(rdns, setup);
			// We can sub sample negatives if no recursion or joint inference.
			if (!sampler.getRdn().needsJointInference() &&
				!sampler.getRdn().hasRecursion()) {
				subsampleNegatives(jointExamples);
				negativesSampled = true;
			}
		}
			
		int startCount = cmdArgs.getMaxTreesVal();
		int increment = 1;
		for(; startCount <= cmdArgs.getMaxTreesVal();startCount+=increment) {
			sampler.setMaxTrees(startCount);
			Utils.println("% Trees = " + startCount);
			sampler.getMarginalProbabilities(jointExamples);
			HashMap<String, List<RegressionRDNExample>> backupJointExamples = null;
			if (startCount != cmdArgs.getMaxTreesVal()) {
				backupJointExamples = new HashMap<>();
				for (String targ : jointExamples.keySet()) {
					backupJointExamples.put(targ, new ArrayList<>(jointExamples.get(targ)));
				}
			}

			// Subsample the negatives for reporting.
			if (!negativesSampled) {
				Utils.println("\n% Subsampling the negative examples for reporting.");
				subsampleNegatives(jointExamples);
				negativesSampled=true;
			}

		
			// clear the query file.
			if (writeQueryAndResults) {
				for (String target : jointExamples.keySet()) {
					File f = new File(getQueryFile(target));
					if (f.exists()) {
						f.delete();
					}
				}
			}
			processExamples(jointExamples, thresh, startCount);
			jointExamples = backupJointExamples;
		}
	}

	private void processExamples(
			Map<String, List<RegressionRDNExample>> jointExamples,
			double thresh, int startCount) {
		for (String pred : jointExamples.keySet()) {
			// clear the results file for each predicate
			if (writeQueryAndResults) {
				File f = new File(getResultsFile(pred));
				if (f.exists()) {
					f.delete();
				}
			}
			getF1ForEgs(jointExamples.get(pred), thresh, pred, startCount);
		}
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

	private String getQueryFile(String target) {
		return setup.getOuterLooper().getWorkingDirectory() + "/query_" + target + ".db";
	}

	private String getResultsFile(String target) {
		String suff ="";
		if (cmdArgs.getModelFileVal() != null) {
			suff = cmdArgs.getModelFileVal() + "_";
		}
		return setup.getOuterLooper().getWorkingDirectory() + "/results_" + suff + target + ".db";
	}

	private String getTestsetInfoFile(String target) {
		String modelDir = cmdArgs.getResultsDirVal();
		String result   = Utils.replaceWildCards((modelDir != null ? modelDir : setup.getOuterLooper().getWorkingDirectory())
												+ "bRDNs/" + (target == null || target.isEmpty() ? "" : target + "_") 
												+ "testsetStats" + cmdArgs.getExtraMarkerForFiles(true)
												+ (cmdArgs.getModelFileVal() == null ? "" : "_" + cmdArgs.getModelFileVal()) + ".txt");
		Utils.ensureDirExists(result);
		return result;
	}

	private void getF1ForEgs(List<RegressionRDNExample> examples, double threshold,
							 String target, int trees) {
		// TODO(@hayesall): Why does this return a double when the double is never used?

		// We repeatedly loop over the examples, but the code at least is cleaner.
		// Update the probabilities here if needed, such as normalizing.
		
		// Update true positive, false positives etc.
		CoverageScore  score = new CoverageScore();
		String resultsString = "useLeadingQuestionMarkVariables: true.\n\n" + updateScore(examples, score, threshold);
		if (trees == cmdArgs.getMaxTreesVal()) {

			// Print examples and some 'context' for possible use by other MLN software.
			if (writeQueryAndResults) {
				printExamples(examples, target);
			}
		}

		ComputeAUC auc = computeAUCFromEg(examples, target);

		ThresholdSelector selector = new ThresholdSelector();
		for (RegressionRDNExample regEx : examples) {
			// This code should only be called for single-class examples
			selector.addProbResult(regEx.getProbOfExample().getProbOfBeingTrue(), regEx.isOriginalTruthValue());
		}
		double thresh = selector.selectBestThreshold();
		Utils.println("% F1 = " + selector.lastComputedF1);
		Utils.println("% Threshold = " + thresh);

		Utils.println("\n%   AUC ROC   = " + Utils.truncate(auc.getROC(), 6));
		Utils.println("%   AUC PR    = " + Utils.truncate(auc.getPR(),  6));
		Utils.println("%   CLL	      = " + Utils.truncate(auc.getCLL(),  6));

		resultsString += "\n//  AUC ROC   = " + Utils.truncate(auc.getROC(), 6);
		resultsString += "\n//  AUC PR    = " + Utils.truncate(auc.getPR(),  6);
		resultsString += "\n//  CLL       = " + Utils.truncate(auc.getCLL(),  6);
		resultsString += "\naucROC(" +  target + ", " + Utils.truncate(auc.getROC(), 6) + ").";
		resultsString += "\naucPR( " +  target + ", " + Utils.truncate(auc.getPR(),  6) + ").\n";
		String fileNameForResults = (writeQueryAndResults ? getTestsetInfoFile(target) : null);

		if (threshold != -1) {
			Utils.println("%   Precision = " + Utils.truncate(score.getPrecision(), 6) + " at threshold = " + Utils.truncate(threshold, 3));
			Utils.println("%   Recall    = " + Utils.truncate(score.getRecall(),    6));
			Utils.println("%   F1        = " + Utils.truncate(score.getF1(),        6));
			resultsString += "\n//   Precision = " + Utils.truncate(score.getPrecision(), 6) + " at threshold = " + Utils.truncate(threshold, 3);
			resultsString += "\n//   Recall    = " + Utils.truncate(score.getRecall(),    6);
			resultsString += "\n//   F1        = " + Utils.truncate(score.getF1(),        6);
			resultsString += "\nprecision(" + target + ", " + Utils.truncate(score.getPrecision(), 6) + ", usingThreshold(" + threshold + ")).";
			resultsString += "\nrecall(   " + target + ", " + Utils.truncate(score.getRecall(),    6) + ", usingThreshold(" + threshold + ")).";
			resultsString += "\nF1(       " + target + ", " + Utils.truncate(score.getF1(),        6) + ", usingThreshold(" + threshold + ")).";
			if (writeQueryAndResults) { Utils.writeStringToFile(resultsString + "\n", new CondorFile(fileNameForResults)); }
			score.getF1();
			return;
		}
		
		if (writeQueryAndResults) { Utils.writeStringToFile(resultsString + "\n", new CondorFile(fileNameForResults)); }

	}

	private ComputeAUC computeAUCFromEg(List<RegressionRDNExample> examples, String target) {
		Utils.println("\n% Computing Area Under Curves.");

		// TODO(?): need to handle WEIGHTED EXAMPLES.  Simple approach: have a eachNegRepresentsThisManyActualNegs and make this many copies.

		List<Double> positiveProbabilities = new ArrayList<>();
		List<Double> negativeProbabilities = new ArrayList<>();

		for (RegressionRDNExample regressionRDNExample : examples) {
			// This code should only be called for single-class examples
			double probability = regressionRDNExample.getProbOfExample().getProbOfBeingTrue();
			if (regressionRDNExample.isOriginalTruthValue()) {
				positiveProbabilities.add(probability);
			} else {
				negativeProbabilities.add(probability);
			}
		}

		// If models are written somewhere, then also write AUC's there
		// (This allows us to avoid writing in a dir that only contains INPUT files)
		// Hence, multiple runs can simultaneously use the same input directory, yet write to different output dirs.

		String aucTempDirectory;
		aucTempDirectory = setup.getOuterLooper().getWorkingDirectory() + "/AUC/" + (cmdArgs.getModelFileVal() == null ? "" : cmdArgs.getModelFileVal() +"/");
		if (cmdArgs.getTargetPredVal().size() > 1) {
			aucTempDirectory += target + "/";
		}
		String extraMarker = "";
		ComputeAUC.deleteAUCfilesAfterParsing = false;
		double minRecallForAUCPR = 0;
		return new ComputeAUC(positiveProbabilities, negativeProbabilities, aucTempDirectory, cmdArgs.getAucPathVal(), extraMarker, minRecallForAUCPR, cmdArgs.useLockFiles);
	}

	private void printExamples(List<RegressionRDNExample> examples, String target) {

		// TODO(hayesall): `printExamples` is a misnomer. This creates the `query_*.db` and `results_*.db` files.
		// 		The intention is for use in other software, this should probably be carefully evaluated then removed.

		// Will collect the 'context' around a fact.  Turn off until we think this is needed.  It is a slow calculation.

		// PredicateModes pmodes = new PredicateModes(setup.getInnerLooper());
		setup.getListOfPredicateAritiesForNeighboringFacts();

		// Write all examples to a query.db file
		// Results/Probs to results.db
		String resultsFileString = "?";
		String queryFileString = "?";
		String resultsFileStringLocal;
		String queryFileStringLocal = "?";

		BufferedWriter queryFile = null;
		BufferedWriter resultsFile = null;
		try {
            queryFileString        = getQueryFile(  target);
            resultsFileString      = getResultsFile(target);
            queryFileStringLocal = queryFileString;
			resultsFileStringLocal = resultsFileString;
			queryFile              = new BufferedWriter(new CondorFileWriter(queryFileStringLocal, true));
			resultsFile            = new BufferedWriter(new CondorFileWriter(resultsFileStringLocal,   true));
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in printExamples: " + e);
		}
		Utils.println("\nprintExamples: Writing out predictions (for Tuffy?) on " + Utils.comma(examples) + " examples for '" + target 
						+ "' to:\n  " + resultsFileString+ "\n and to:\n  " + queryFileString);
		
		// Write the examples to query/results files.
		for (RegressionRDNExample pex : examples) {
			// Should be called only for single class
			double prob = pex.getProbOfExample().getProbOfBeingTrue();
			String prefix = "";
			double printProb = prob;
			if (!pex.isOriginalTruthValue()) {
				prefix = "!";
				printProb = 1-prob;
			}
			try {
				queryFile.write(prefix + pex.toString() + "\n");
				resultsFile.write(prefix + pex.toString()+ " " + printProb + "\n");

			} catch (IOException e) {
				Utils.reportStackTrace(e);
				Utils.error("Something went wrong: " + e);
			}
		}

		try {
			queryFile.close();
			resultsFile.close();
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Something went wrong: " + e);
		}
		
		if (!resultsFileString.equals(queryFileStringLocal)) {
			Utils.moveAndGzip(queryFileStringLocal,   queryFileString,   true);
		}
	}

	private String getNameOfCSVFile() {
		// TODO(@hayesall): When and where is this file used?
		String modelDirectory = cmdArgs.getResultsDirVal();
		String result = Utils.replaceWildCards((modelDirectory != null ? modelDirectory : setup.getOuterLooper().getWorkingDirectory())
				+ "bRDNs/"
				+ "predictions"
				+ cmdArgs.getExtraMarkerForFiles(true)
				+ ".csv");

		Utils.ensureDirExists(result);
		return result;
	}

	/*
	 * Should be called with only single-value examples.
	 */
	private String updateScore(List<RegressionRDNExample> examples, CoverageScore score, double threshold) {

		double sum = 0;
		double count = 0;
		double countOfPos = 0;
		double countOfNeg = 0;

		StringBuilder sb = new StringBuilder();

		for (RegressionRDNExample regressionExample : examples) {

			double probability = regressionExample.getProbOfExample().getProbOfBeingTrue();
			double weightOnExample = regressionExample.getWeightOnExample();

			count += weightOnExample;


			if (regressionExample.isOriginalTruthValue()) {
				// Positive Example

				sb.append("pos,")
						.append(probability)
						.append(", ")
						.append(regressionExample)
						.append("\n");

				// Compute the weighted sum:
				sum += probability * weightOnExample;
				countOfPos += weightOnExample;

				if (probability > threshold) {
					score.addToTruePositive(weightOnExample);
				} else {
					score.addToFalseNegative(weightOnExample);
				}
			} else {
				// Negative Example

				sb.append("neg, ")
						.append(probability)
						.append(", ")
						.append(regressionExample)
						.append("\n");

				// Compute the weighted sum:
				sum += (1 - probability) * weightOnExample;
				countOfNeg += weightOnExample;

				if (probability > threshold) {
					score.addToFalsePositive(weightOnExample);
				} else {
					score.addToTrueNegative(weightOnExample);
				}
			}
		}

		Utils.writeStringToFile(sb.toString(), new CondorFile(getNameOfCSVFile()));

		// TODO(@JWS) Use geometric mean if this is over the training set.
		//		For test (or tuning) it is fine to use the expected value.

		String testSetReport1 = " (Arithmetic) Mean Probability Assigned to Correct Output Class: " + Utils.truncate(sum, 3) + "/" + Utils.truncate(count, 2) + " = " + Utils.truncate(sum / count, 6) + "\n";
		Utils.println(testSetReport1);

		String testSetReport2 = " The weighted count of positive examples = " + Utils.truncate(countOfPos, 3) + " and the weighted count of negative examples = " + Utils.truncate(countOfNeg, 3);
		Utils.println(testSetReport2);

		return "//" + testSetReport1 + "testsetLikelihood(sum(" + Utils.truncate(sum, 3) + "), countOfExamples(" + Utils.truncate(count, 2) + "), mean(" + Utils.truncate(sum / count, 6) + ")).\n\n"
				+ "//" + testSetReport2 + "\nweightedSumPos(" + Utils.truncate(countOfPos, 3) + ").\nweightedSumNeg(" + Utils.truncate(countOfNeg, 3) + ").\n";

	}
}
