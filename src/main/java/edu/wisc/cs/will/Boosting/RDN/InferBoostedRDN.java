package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.MLN.MLNInference;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.Boosting.Utils.ThresholdSelector;
import edu.wisc.cs.will.DataSetUtils.ComputeAUC;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.ILP.CoverageScore;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.util.*;


public class InferBoostedRDN {

	private boolean printExamples = false;
	private final boolean writeQueryAndResults = true;
	private boolean useOldFileLocations = true;
	private double  minRecallForAUCPR = 0;
	private double minLCTrees = 20;
	private double incrLCTrees = 2;
	
	private final CommandLineArguments cmdArgs;
	private final WILLSetup setup;

	public InferBoostedRDN(CommandLineArguments args, WILLSetup setup) {
		this.cmdArgs = args;
		this.setup = setup;
		setParamsUsingSetup(setup);

		if (Utils.getUserName().equalsIgnoreCase("tkhot")) {
			useOldFileLocations = true;	
		}
	}
	
	public void runInference(JointRDNModel rdns, double thresh) {
		Map<String,List<RegressionRDNExample>> targetExamples = setup.getJointExamples(cmdArgs.getTargetPredVal());
		Map<String,List<RegressionRDNExample>> jointExamples = setup.getHiddenExamples();
		if (jointExamples == null) {
			jointExamples = new HashMap<>();
		}
		jointExamples.putAll(targetExamples);
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
		if (cmdArgs.isPrintLearningCurve()) {
			startCount = (int)minLCTrees;
			increment = (int)incrLCTrees;
			for (String targ : jointExamples.keySet()) {
				File f = new File(getLearningCurveFile(targ, "pr"));
				if (f.exists()) { f.delete();}
				 f = new File(getLearningCurveFile(targ, "cll"));
				if (f.exists()) { f.delete();}
			}
		}
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
			boolean allExamples = false;
			processExamples(jointExamples, thresh, startCount, allExamples);
			jointExamples = backupJointExamples;
		}
	}

	private void processExamples(
			Map<String, List<RegressionRDNExample>> jointExamples,
			double thresh, int startCount, boolean usingAllEgs) {
		for (String pred : jointExamples.keySet()) {
			// clear the results file for each predicate
			if (writeQueryAndResults) {
				File f = new File(getResultsFile(pred));
				if (f.exists()) {
					f.delete();
				}
			}
			getF1ForEgs(jointExamples.get(pred), thresh, pred, startCount, usingAllEgs);
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

	private void setParamsUsingSetup(WILLSetup willSetup) {
		String lookup;
		if ((lookup =  willSetup.getInnerLooper().getStringHandler().getParameterSetting("printEg")) != null) {
			printExamples = Boolean.parseBoolean(lookup);
		}
		if ((lookup =  willSetup.getInnerLooper().getStringHandler().getParameterSetting("minRecallForAUCPR")) != null) {
			minRecallForAUCPR = Double.parseDouble(lookup);
		}
		if ((lookup =  willSetup.getInnerLooper().getStringHandler().getParameterSetting("minLCTrees")) != null) {
			minLCTrees = Double.parseDouble(lookup);
		}
		if ((lookup =  willSetup.getInnerLooper().getStringHandler().getParameterSetting("incrLCTrees")) != null) {
			incrLCTrees = Double.parseDouble(lookup);
		}
	}
	
	private void reportResultsToCollectorFile(BufferedWriter collectorBW, String category, ProbDistribution prob, double wgt, RegressionRDNExample example) throws IOException {
		if (category == null) {
			collectorBW.append("// Results of '").append("unnamedModel").append("'.\n\nuseLeadingQuestionMarkVariables: true.\n\n");
			return;
		}
		collectorBW.append("modelPrediction(model(").append(RunBoostedRDN.nameOfCurrentModel).append("), category(").append(category).append("), prob(").append(String.valueOf(prob)).append("), wgt(").append(String.valueOf(wgt)).append("), ").append(String.valueOf(example)).append(").\n").append("\n");
	}

	private String getQueryFile(String target) {
		if (useOldFileLocations) {
			return setup.getOuterLooper().getWorkingDirectory() + "/query_" + target + ".db";
		}
		return getQueryFile(target, false);
	}
	private String getFullQueryFile(String target) {
		if (useOldFileLocations) {
			return setup.getOuterLooper().getWorkingDirectory() + "/query_full_" + target + ".db";
		}
		return getQueryFile(target, false);
	}
	
	private String getQueryFile(String target, boolean getLocalFile) {
		String modelDir = cmdArgs.getResultsDirVal(); // Try to put in the place other results go.
		String result   = Utils.replaceWildCards((getLocalFile ? "MYSCRATCHDIR"
                 											   : (modelDir != null ? modelDir : setup.getOuterLooper().getWorkingDirectory()))
                 								 + "bRDNs/" + (target == null || target.isEmpty() ? "" : target + "_") 
                 								 + "query" + cmdArgs.getExtraMarkerForFiles(true) + ".db");
		Utils.ensureDirExists(result);
		return result;
	}
	
	private String getResultsFile(String target) {
		if (useOldFileLocations) {
			String suff ="";
			if (cmdArgs.getModelFileVal() != null) {
				suff = cmdArgs.getModelFileVal() + "_";
			}
			return setup.getOuterLooper().getWorkingDirectory() + "/results_" + suff + target + ".db";
		}
		return getResultsFile(target, false);
	}
	
	private String getFullResultsFile(String target) {
		if (useOldFileLocations) {
			String suff ="";
			if (cmdArgs.getModelFileVal() != null) {
				suff = cmdArgs.getModelFileVal() + "_";
			}
			return setup.getOuterLooper().getWorkingDirectory() + "/results_full_" + suff + target + ".db";
		}
		return getResultsFile(target, false);
	}
	
	private String getResultsFile(String target, boolean getLocalFile) {
		String modelDir = cmdArgs.getResultsDirVal();
		String result =  Utils.replaceWildCards((getLocalFile ? "MYSCRATCHDIR"
														      : (modelDir != null ? modelDir : setup.getOuterLooper().getWorkingDirectory()))
												+ "bRDNs/" + (target == null || target.isEmpty() ? "" : target + "_") 
												+ "results" + cmdArgs.getExtraMarkerForFiles(true)
												+ (cmdArgs.getModelFileVal() == null ? "" : "_" + cmdArgs.getModelFileVal()) + ".db");
		Utils.ensureDirExists(result);
		return result;
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

	private String getLearningCurveFile(String target, String type) {
		return setup.getOuterLooper().getWorkingDirectory() + "/curve" +
				(cmdArgs.getModelFileVal() == null ? "" : "_" + cmdArgs.getModelFileVal()) +
				(target.isEmpty() ? "" : "_"+target) + "." + type;
	}

	private void getF1ForEgs(List<RegressionRDNExample> examples, double threshold,
							 String target, int trees, boolean usingAllEgs) {
		// TODO(@hayesall): Why does this return a double when the double is never used?

		// We repeatedly loop over the examples, but the code at least is cleaner.
		// Update the probabilities here if needed, such as normalizing.
		
		// Update true positive, false positives etc.
		CoverageScore  score = new CoverageScore();
		String resultsString = "useLeadingQuestionMarkVariables: true.\n\n" + updateScore(examples, score, threshold);
		if (trees == cmdArgs.getMaxTreesVal()) {

			// Print examples and some 'context' for possible use by other MLN software.
			if (writeQueryAndResults) {
				printExamples(examples, target, usingAllEgs);
			}

			// Write to "collector file"
			if (!useOldFileLocations) {
				writeToCollectorFile(examples);
			}
		}

		
		ComputeAUC auc = computeAUCFromEg(examples, target);


		if (cmdArgs.isPrintLearningCurve()) {
			Utils.appendString(new File(getLearningCurveFile(target, "pr")), trees + " " + auc.getPR() + "\n");
			Utils.appendString(new File(getLearningCurveFile(target, "cll")), trees + " " + auc.getCLL() + "\n");
		}
		{
			ThresholdSelector selector = new ThresholdSelector();
			for (RegressionRDNExample regEx : examples) {
				// This code should only be called for single-class examples
				selector.addProbResult(regEx.getProbOfExample().getProbOfBeingTrue(), regEx.isOriginalTruthValue());
			}
			double thresh = selector.selectBestThreshold();
			Utils.println("% F1 = " + selector.lastComputedF1);
			Utils.println("% Threshold = " + thresh);
		}

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
			Utils.println("%   Precision = " + Utils.truncate(score.getPrecision(), 6)       + (threshold != -1 ? " at threshold = " + Utils.truncate(threshold, 3) : " "));
			Utils.println("%   Recall    = " + Utils.truncate(score.getRecall(),    6));
			Utils.println("%   F1        = " + Utils.truncate(score.getF1(),        6));
			resultsString += "\n//   Precision = " + Utils.truncate(score.getPrecision(), 6) + (threshold != -1 ? " at threshold = " + Utils.truncate(threshold, 3) : " ");
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

		String extraMarker = cmdArgs.getExtraMarkerForFiles(true);

		// If models are written somewhere, then also write AUC's there
		// (This allows us to avoid writing in a dir that only contains INPUT files)
		// Hence, multiple runs can simultaneously use the same input directory, yet write to different output dirs.

		String aucTempDirectory = null;
		if (useOldFileLocations) {
			aucTempDirectory = setup.getOuterLooper().getWorkingDirectory() + "/AUC/" + (cmdArgs.getModelFileVal() == null ? "" : cmdArgs.getModelFileVal() +"/");
			if (cmdArgs.getTargetPredVal().size() > 1) {
				aucTempDirectory += target + "/";
			}
			extraMarker = "";
			ComputeAUC.deleteAUCfilesAfterParsing = false;
		} else {
			Utils.replaceWildCards(Utils.isRunningWindows() ? "MYSCRATCHDIR" + "calcAUC/" + target + "/" :  cmdArgs.getDirForAUCfiles(target, setup));
		}

		return new ComputeAUC(positiveProbabilities, negativeProbabilities, aucTempDirectory, cmdArgs.getAucPathVal(), extraMarker, minRecallForAUCPR, cmdArgs.useLockFiles);
	}
	
	private String ensureThisIsaSubdir(String modelDirRaw) {
		String modelDir = Utils.replaceWildCards(modelDirRaw);
		if (modelDir == null)      { return null;     }
		if (modelDir.length() < 2) { return modelDir; }
		if (modelDir.contains(":")) {
			modelDir = modelDir.substring(modelDir.indexOf(':') + 1);
		}
		while (modelDir.length() > 0 && modelDir.charAt(0) == File.separatorChar) {
			modelDir = modelDir.substring(1); // Remove any leading (back) slashes
		}
		return modelDir;
	}

	private void writeToCollectorFile(List<RegressionRDNExample> examples) {
		String fileNamePrefix = "testSetResults/testSetInferenceResults"
				+ cmdArgs.getExtraMarkerForFiles(true);

		String localPrefix = "MYSCRATCHDIR"
				+ "bRDNs/"
				+ ensureThisIsaSubdir(cmdArgs.getResultsDirVal());
		String fileName = Utils.replaceWildCards(localPrefix + fileNamePrefix + "_unsorted" + Utils.defaultFileExtensionWithPeriod);
		String fileNameSorted = Utils.replaceWildCards(localPrefix + fileNamePrefix +   "_sorted" + Utils.defaultFileExtensionWithPeriod);

		int posCounter = 0;
		int negCounter = 0;
		try {
			File           collectorFile = Utils.ensureDirExists(fileName);
			BufferedWriter collectBuffer = new BufferedWriter(new CondorFileWriter(collectorFile)); // Clear the file if it already exists.
			
			Utils.println("\nwriteToCollectorFile: Writing out predictions on " + Utils.comma(examples) + " examples for '" + cmdArgs.getTargetPredVal()  + "'\n  " + fileName);
			if (collectorFile != null) { reportResultsToCollectorFile(collectBuffer, null, null, 0.0, null); }
			for (RegressionRDNExample pex : examples) {
				ProbDistribution prob    = pex.getProbOfExample();
				double wgtOnEx = pex.getWeightOnExample();
			
				if (pex.isOriginalTruthValue()) { posCounter++; } else { negCounter++; }
				if (collectorFile != null) { reportResultsToCollectorFile(collectBuffer, pex.isOriginalTruthValue() ? "pos" : "neg", prob, wgtOnEx, pex); }
			}
			collectBuffer.close();
			if (collectorFile != null) { sortLinesInPredictedProbsFile(fileName, fileNameSorted); }
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Something went wrong:\n   " + e);
		}
		
		Utils.moveAndGzip(fileName,       cmdArgs.getResultsDirVal() + fileNamePrefix + "_unsorted" + Utils.defaultFileExtensionWithPeriod, true);
		Utils.moveAndGzip(fileNameSorted, cmdArgs.getResultsDirVal() + fileNamePrefix +   "_sorted" + Utils.defaultFileExtensionWithPeriod, true);
		Utils.println("writeToCollectorFile:  " + fileName + "\n   |pos| = " + Utils.comma(posCounter) + "\n   |neg| = " + Utils.comma(negCounter));
	}
	
	private void sortLinesInPredictedProbsFile(String fileToRead, String fileToWrite) {
		Utils.ensureDirExists(fileToWrite);
		List<Literal> lits = setup.getInnerLooper().getParser().readLiteralsInFile(fileToRead, false, false);
		CompareProbsInModelPredictions comparator = new CompareProbsInModelPredictions();
		lits.sort(comparator);
		Utils.writeObjectsToFile(fileToWrite, lits, ". // #COUNT", "// Results of '" + RunBoostedRDN.nameOfCurrentModel + "' sorted by the predicted probability.\n\nuseLeadingQuestionMarkVariables: true.\n\n");
	}

	private void printExamples(List<RegressionRDNExample> examples, String target, boolean usingAllEgs) {

		// Will collect the 'context' around a fact.  Turn off until we think this is needed.  It is a slow calculation.

		// PredicateModes pmodes = new PredicateModes(setup.getInnerLooper());
		setup.getListOfPredicateAritiesForNeighboringFacts();

		// Should be set somewhere else
		setup.getBitMaskForNeighboringFactArguments(target);

		// Write all examples to a query.db file
		// Results/Probs to results.db
		String resultsFileString = "?";
		String queryFileString = "?";
		String resultsFileStringLocal = "?";
		String queryFileStringLocal = "?";

		BufferedWriter queryFile = null;
		BufferedWriter resultsFile = null;
		try {
			if (usingAllEgs) {
				queryFileString        = getFullQueryFile(  target);
				resultsFileString      = getFullResultsFile(target);
			} else {
				queryFileString        = getQueryFile(  target);
				resultsFileString      = getResultsFile(target);
			}
			if (!useOldFileLocations) {
				queryFileStringLocal   = getQueryFile(  target, Utils.isRunningWindows());
				resultsFileStringLocal = getResultsFile(target, Utils.isRunningWindows());
			} else {
				queryFileStringLocal = queryFileString;
				resultsFileStringLocal = resultsFileString;
			}
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
		
		if (!resultsFileString.equals(resultsFileStringLocal)) {
			Utils.moveAndGzip(resultsFileStringLocal, resultsFileString, true);
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
		// TODO(@hayesall): maxToPrintOnAve should be removed.

		double sum = 0;
		double count = 0;
		double countOfPos = 0;
		double countOfNeg = 0;
		int numberToPrint = Utils.getSizeSafely(examples);
		double maxToPrintOnAverage = 250.0;

		if (printExamples && numberToPrint > maxToPrintOnAverage) {
			Utils.println("% Note: since more than " + Utils.truncate(maxToPrintOnAverage, 0) + " examples, will randomly report.");
		}

		StringBuilder sb = new StringBuilder();

		for (RegressionRDNExample regressionExample : examples) {

			double probability = regressionExample.getProbOfExample().getProbOfBeingTrue();
			double weightOnExample = regressionExample.getWeightOnExample();

			count += weightOnExample;


			if (regressionExample.isOriginalTruthValue()) {
				// Positive Example

				if (printExamples && Utils.random() < maxToPrintOnAverage / numberToPrint) {
					Utils.println("% Pos #" + Utils.truncate(score.getTruePositives() + score.getFalseNegatives(), 0) + ": '" + regressionExample + "' prob = " + Utils.truncate(probability, 6));
				}

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
				if (printExamples && Utils.random() < maxToPrintOnAverage / numberToPrint) {
					Utils.println("% Neg #" + Utils.truncate(score.getTrueNegatives() + score.getFalsePositives(), 0) + ": '" + regressionExample + "' prob = " + Utils.truncate(probability, 6));
				}

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

class CompareProbsInModelPredictions implements java.util.Comparator<Literal> {
	
	public int compare(Literal lit1, Literal lit2) {
		if (lit1 == lit2) { return 0; }		   
		Term arg2_lit1      = lit1.getArgument(2);	
		Term arg2_lit2      = lit2.getArgument(2);
		Term arg0_arg2_lit1 = ((Function) arg2_lit1).getArgument(0);
		Term arg0_arg2_lit2 = ((Function) arg2_lit2).getArgument(0);
		NumericConstant   nc1 = (NumericConstant) arg0_arg2_lit1;
		NumericConstant   nc2 = (NumericConstant) arg0_arg2_lit2;
		double           dbl1 = nc1.value.doubleValue();
		double           dbl2 = nc2.value.doubleValue();

		// We want HIGHER numbers at the front of the sorted list.
		return Double.compare(dbl2, dbl1);
	}
}
