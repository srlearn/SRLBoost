package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.RDN.Models.PhiFunctionForRDN;
import edu.wisc.cs.will.Boosting.Trees.LearnRegressionTree;
import edu.wisc.cs.will.Boosting.Trees.RegressionTree;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.Boosting.Utils.ExampleSubSampler;
import edu.wisc.cs.will.Boosting.Utils.LineSearch;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.TreeStructuredTheory;
import edu.wisc.cs.will.ILP.ILPouterLoop;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.VectorStatistics;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileInputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

import java.io.*;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

/*
 * @author Tushar Khot
 *
 */
public class LearnBoostedRDN {
	private final static int debugLevel = 1; // Used to control output from this class (0 = no output, 1=some, 2=much, 3=all).

	private final CommandLineArguments cmdArgs;
	private final ExampleSubSampler egSubSampler;
	private final WILLSetup setup;

	private List<RegressionRDNExample> egs    = null;
	private String  targetPredicate          = null;
	private int     maxTrees                 = 10;
	private boolean resampleExamples        = true;
	private final boolean stopIfFewChanges        = false;
	private boolean performLineSearch       = false;
	private boolean learnSingleTheory 		= false;
	private boolean disableBoosting			= false;

	private long learningTimeTillNow = 0;

	public LearnBoostedRDN(CommandLineArguments cmdArgs, WILLSetup setup) {
		this.cmdArgs = cmdArgs;
		this.setup = setup;
		maxTrees = cmdArgs.getMaxTreesVal();
		setParamsUsingSetup(setup);
		if (cmdArgs.isDisabledBoosting()) {
			disableBoosting=true;
		}
		egSubSampler = new ExampleSubSampler(setup);
	}

	public void learnNextModel(SRLInference sampler, ConditionalModelPerPredicate rdn, int numMoreTrees) {

		Utils.println("\n% Learn model for: " + targetPredicate);
		long start = System.currentTimeMillis();

		// Call facts and examples the first time.
		setup.prepareFactsAndExamples(targetPredicate);

		Utils.println("% Have prepared facts.");

		learnRDN(targetPredicate, rdn, sampler, numMoreTrees);

		long end = System.currentTimeMillis();
		learningTimeTillNow += (end - start);
		if (rdn.getNumTrees() == maxTrees) {
			Utils.println("% Time taken to learn model for '" + targetPredicate + "': " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
		}
	}

	private void learnRDN(String pred, ConditionalModelPerPredicate rdn, SRLInference sampler, int numMoreTrees) {
		// Thought we needed the 'caller' but we don't - leave it here, though, in case we do end up needing it.
		String saveModelName = BoostingUtils.getModelFile(cmdArgs, pred, true);

		if(rdn.getNumTrees() == 0) {
			rdn.setTargetPredicate(pred);
			rdn.setTreePrefix(pred + (cmdArgs.getModelFileVal() == null ? "" : "_" + cmdArgs.getModelFileVal()));
			if (learnSingleTheory) {
				rdn.setHasSingleTheory(true);
				rdn.setSetup(setup);
				List<Sentence> bkClauses = setup.getInnerLooper().getParser().parse(getComputationPrologRules(maxTrees));
				rdn.addSentences(bkClauses);
			}
		}
		

		List<RegressionRDNExample> old_eg_set = null;
		long start = System.currentTimeMillis();
		if (disableBoosting) {
			maxTrees=1;
			rdn.setLog_prior(0);
			// Increase the depth and number of clauses
			// TODO : Maybe make this settable ? Or assume caller sets it ?
			ILPouterLoop outerLoop = setup.getOuterLooper();
			outerLoop.setMaxTreeDepth(10);
			outerLoop.setMaxTreeDepthInLiterals(12);
			outerLoop.maxNumberOfClauses = 20;
			outerLoop.maxNumberOfCycles = 20;
			outerLoop.setMaxAcceptableNodeScoreToStop(0.0001);
		}
		//TODO(TVK!)
		if (
			cmdArgs.isLearnRegression()) {
			rdn.setLog_prior(0);
		}
		
		if (cmdArgs.isLearnMLN() && cmdArgs.isLearningMLNClauses()) {
			setup.getOuterLooper().setMaxBodyLength(cmdArgs.getMaxMLNClauseLength());
			setup.getOuterLooper().maxNumberOfClauses = cmdArgs.getNumberOfMLNClauses();
			setup.getOuterLooper().maxNumberOfCycles = cmdArgs.getNumberOfMLNClauses();
			setup.getInnerLooper().beamWidth = 10;
		}
		
		// Learn maxTrees models.
		int i;
		if (rdn.getNumTrees() == 0 && cmdArgs.useCheckPointing()) {
			loadCheckPointModel(rdn);
		}

		// check if rdn already has some trees from checkpoint
		i=rdn.getNumTrees();
		
		int maxTreesForThisRun = Math.min(maxTrees, (i+numMoreTrees));
	
		if(i >= maxTrees) {
			rdn.setNumTrees(maxTrees);
		}
		if (i == 0) {
			dumpTheoryToFiles(null, -1);  // Print something initially in case a run dies (i.e., be sure to erase any old results right away).
		}
		for (; i < maxTreesForThisRun; i++) {
			if (i >= maxTrees/2) {
				setup.addAllTargetModes();
			}
			
			long end = System.currentTimeMillis();
			if (cmdArgs.isLearnMLN() && cmdArgs.isLearningMLNClauses()) {
				setup.getOuterLooper().setMaxBodyLength((i/4)+1);
				setup.getOuterLooper().maxNumberOfClauses = (20/(i+1));
				setup.getOuterLooper().maxNumberOfCycles = (20/(i+1));
			}
			if (i > 0 && debugLevel > 0) {
				Utils.println("% Time taken to learn " + Utils.comma(i) + " trees is " + Utils.convertMillisecondsToTimeSpan(learningTimeTillNow + end - start, 3) + ".\n");
			}
			
			// Do we need this here? It is called before executeOuterLoop and in dumpTheoryToFiles.
			setup.getOuterLooper().resetAll();
			if ((sampler instanceof SingleModelSampler) &&
				doEarlyStop(old_eg_set, (SingleModelSampler)sampler)) { // THIS NEEDS TO BE EXTENDED TO HANDLE MULTIPLE TREES.
				break;
			}

			for (int modelNumber = 0; modelNumber < RunBoostedRDN.numbModelsToMake; modelNumber++) { // This code assumes modelNumber=0 is learned first.
				// Build data set for this model in this iteration.
				long bddstart = System.currentTimeMillis();						
				List<RegressionRDNExample> newDataSet = buildDataSet(targetPredicate, sampler);
				long bbend = System.currentTimeMillis();
				Utils.println("Time to build dataset: " + Utils.convertMillisecondsToTimeSpan(bbend-bddstart));
				RegressionTree tree;
				tree = getWILLTree(newDataSet, i);
				double stepLength = 1;
				if (!disableBoosting) {
					stepLength = cmdArgs.getDefaultStepLenVal();
					// Currently can't handle line search and single theory, since we need regression values for a single tree.
					// TODO add support for single theory too.
					if (performLineSearch && !learnSingleTheory) {
						LineSearch    searcher = new LineSearch();
						PhiFunctionForRDN func = new PhiFunctionForRDN(rdn, tree, newDataSet);
						double        newAlpha = searcher.getStepLength(func);
						stepLength = (newAlpha == 0 ? stepLength : newAlpha);
					} else {
						if (performLineSearch) {
							Utils.waitHere("Can't handle both line search and single theory. Disable one.");
						}
					}
				}
				rdn.addTree(tree, stepLength, modelNumber);  // This code assume modelNumber=0 is learned first.
				old_eg_set = newDataSet;
			}
			rdn.updateSetOfTrees();
			if (cmdArgs.useCheckPointing()) {
				createCheckPointForModel(rdn, saveModelName);
			}
			if ((i + 1) % 10 == 0) { 
				rdn.saveModel(saveModelName);
			} // Every now and then save the model so we can see how it is doing.
		}
		if (stopIfFewChanges) {
			Utils.println("Stopped after " + Utils.comma(i) + " trees.");
		}
		if (i >= maxTrees) {
			addPrologCodeForUsingAllTrees(rdn, i); 
		}
	}

	public void loadCheckPointModel(ConditionalModelPerPredicate rdn) {
		String saveModelName = BoostingUtils.getModelFile(cmdArgs, targetPredicate, true);
		String chkPointFile = BoostingUtils.getCheckPointFile(saveModelName);
		File willFile = getWILLsummaryFile();
		File chkFile = new File(chkPointFile);
		if (chkFile.exists() && chkFile.length() > 0) {
			Utils.println("Loading checkpoint model from " + chkPointFile);
			rdn.loadModel(chkPointFile, setup, -1);
			Utils.println("Found " + rdn.getNumTrees() + " trees in checkpoint");
			String addString = "\n//// Loaded checkpoint from " + chkPointFile + " at " + Utils.getDateTime() + 
							  ".\n//// Number of trees loaded:" + rdn.getNumTrees() ;
			Utils.appendString(willFile, addString);
		}
		if (!resampleExamples) {
			String chkptEgFile = BoostingUtils.getCheckPointExamplesFile(saveModelName);
			if (Utils.fileExists(chkptEgFile)) {
				Utils.appendString(willFile, "\n//// Also loaded examples from " + chkptEgFile);
				try {

					ObjectInputStream ois = new ObjectInputStream(new CondorFileInputStream(chkptEgFile));

					Object obj = ois.readObject();
					while(obj != null) {
						RegressionRDNExample ex = (RegressionRDNExample)obj;
						egs.add(ex);
						obj = ois.readObject();
					}

					ois.close();
				} 
				catch(Exception e) {
					Utils.reportStackTrace(e);
					Utils.error("Problem in writing examples in createCheckPointForModel.");
				}
			}
		}
		
		String chkptLitFile = BoostingUtils.getCheckPointFlattenedLitFile(saveModelName);
		if (Utils.fileExists(chkptLitFile)) {
			List<Literal> lits = setup.getInnerLooper().getParser().readLiteralsInPureFile(chkptLitFile);
			addToFlattenedLiterals(lits);
			Utils.appendString(willFile, "\n//// Also loaded " + theseFlattenedLits.size() + " flattened literals from " + chkptLitFile);
		}
	}

	private void createCheckPointForModel(ConditionalModelPerPredicate rdn, String saveModelName) {
		String chkptFile = BoostingUtils.getCheckPointFile(saveModelName);
		rdn.saveModel(chkptFile);
		
		// Save the examples if not re-sampling e.g.s
		if (!resampleExamples) {
			String chkptEgFile = BoostingUtils.getCheckPointExamplesFile(saveModelName);
			// Need to write examples only during first iteration
			if (Utils.fileExists(chkptEgFile)) {
				try {

					ObjectOutputStream oos = new ObjectOutputStream(new CondorFileOutputStream(chkptEgFile));
					for (RegressionRDNExample eg : egs) {
						oos.writeObject(eg);
					}
					oos.close();
				} 
				catch(Exception e) {
					Utils.reportStackTrace(e);
					Utils.error("Problem in writing examples in createCheckPointForModel.");
				}
			}
		}
		
		File chkptLitFile = new CondorFile(BoostingUtils.getCheckPointFlattenedLitFile(saveModelName));
		Utils.writeStringToFile("// Checkpointed flattened literals\n", chkptLitFile);
		
		try {
			BufferedWriter ckptLitWriter = new BufferedWriter(new FileWriter(chkptLitFile));
			for (Literal lit : theseFlattenedLits) {
				ckptLitWriter.write(lit.toString() + "\n");
			}
			ckptLitWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	

	private void setParamsUsingSetup(WILLSetup willSetup) {
		String lookup;
		if ((lookup =  willSetup.getHandler().getParameterSetting("resampleEgs")) != null) {
			resampleExamples = Boolean.parseBoolean(lookup);
		}
		if ((lookup =  willSetup.getHandler().getParameterSetting("singleTheory")) != null) {
			learnSingleTheory = Boolean.parseBoolean(lookup);
		}
		if ((lookup =  willSetup.getHandler().getParameterSetting("lineSearch")) != null) {
			performLineSearch = Boolean.parseBoolean(lookup);
		}
	}

	private final Collection<Literal> theseFlattenedLits = new HashSet<>(4);
	private RegressionTree getWILLTree(List<RegressionRDNExample> newDataSet, int i) {
		TreeStructuredTheory th;
		Theory thry = null;
		try {
			// WILL somehow loses all the examples after every run.  TODO - JWS: Guess there is some final cleanup. 
			setup.getOuterLooper().setPosExamples(BoostingUtils.convertToListOfExamples(newDataSet));
			// Make sure the invented predicates (if any) have unique names.
			setup.getOuterLooper().setPrefixForExtractedRules("");
			if (learnSingleTheory) {
				setup.getOuterLooper().setPostfixForExtractedRules(getTreeSuffix(i + 1));
			} else {
				setup.getOuterLooper().setPostfixForExtractedRules("");
			}
			
			thry = setup.getOuterLooper().executeOuterLoop();

			if (thry instanceof TreeStructuredTheory) {
				th = (TreeStructuredTheory)thry;
				Collection<Literal> currentFlattenedLits = th.getUniqueFlattenedLiterals();
				addToFlattenedLiterals(currentFlattenedLits);
				dumpTheoryToFiles(th, i);
			}
		} catch (SearchInterrupted e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in getWILLTree.");
		}
		
		LearnRegressionTree learner = new LearnRegressionTree(setup);
		return learner.parseTheory(thry);
	}


	private boolean doEarlyStop(List<RegressionRDNExample> old_eg_set, SingleModelSampler sampler) {
		double minGradientForSame = 0.0002;
		if (old_eg_set != null) {
			int numOfEgSame = getNumUnchangedEx(old_eg_set, minGradientForSame, sampler);
			if (debugLevel > 0) {
				Utils.println("% Only " + numOfEgSame + " out of " + Utils.getSizeSafely(old_eg_set) + " converged.");
			}
		}
		return false;
	}

	private int getNumUnchangedEx(List<RegressionRDNExample> oldEgSet, double grad, SingleModelSampler sampler) {
		int counter=0;
		for (Example ex : oldEgSet) {
			RegressionRDNExample eg = (RegressionRDNExample)ex;
			ProbDistribution old_prob = eg.getProbOfExample();

			sampler.getExampleProbability(eg);
			ProbDistribution new_prob = eg.getProbOfExample();

			ProbDistribution diff = new ProbDistribution(old_prob);
			diff.scaleDistribution(-1);
			diff.addDistribution(new_prob);
			double eg_grad = diff.norm();
			if (eg_grad < grad) {
				counter++;
			}

		}
		return counter;
	}

	private void getSampledPosNegEx(List<RegressionRDNExample> all_exs) {

		if (egs != null) {
			for (int i = 0; i < Utils.getSizeSafely(egs); i++) {
				RegressionRDNExample eg = egs.get(i);
				eg.clearCache();
			}
		}
		if (!resampleExamples) {
			if (egs != null) {
				all_exs.addAll(egs);
				return;
				//	return numPosEx;
			}
		} else {
			// Only sample the second time onwards.
			if (egs != null) {
				setup.prepareExamplesForTarget(targetPredicate);
			}
		}
		all_exs.addAll(BoostingUtils.castToListOfRegressionRDNExamples(setup.getOuterLooper().getPosExamples()));
		Utils.println("% Dataset size: " + Utils.comma(all_exs));
		egs = all_exs;
	}

	private List<RegressionRDNExample> buildDataSet(String targetPredicate, SRLInference sampler) {
		List<RegressionRDNExample> all_exs = new ArrayList<>();

		getSampledPosNegEx(        all_exs);
		// No need to get sample probabilities as there is no \psi_0 or gradient.
		if (!disableBoosting) {
			Utils.println("Computing probabilities");
			long start = System.currentTimeMillis();
			sampler.getProbabilities(all_exs);
			long end = System.currentTimeMillis();
			Utils.println("prob time:"+Utils.convertMillisecondsToTimeSpan(end-start));
		}
		
		
		// Update facts based on the sampled states

		for (int i = 0; i < Utils.getSizeSafely(all_exs); i++) {
			
			RegressionRDNExample eg = all_exs.get(i);
			eg.clearCache();
			if(cmdArgs.isLearnRegression() || cmdArgs.isLearnProbExamples()) {
				eg.setOutputValue(eg.originalRegressionOrProbValue - eg.getProbOfExample().getProbOfBeingTrue());
				continue;
			}

			if (disableBoosting) {
				// TODO What would be the best value ?
				if (eg.isOriginalTruthValue()) {
					eg.setOutputValue(4);
					
				} else {
					eg.setOutputValue(-4);
				}
			} else {
				ProbDistribution probDistr = eg.getProbOfExample();
				if (probDistr.isHasDistribution()) {
					double[] base_prob;
					double[] distr = probDistr.getProbDistribution();
					base_prob = VectorStatistics.createIndicator(distr.length, eg.getOriginalValue());

					double[] grad  = VectorStatistics.subtractVectors(base_prob, distr);
					
					// Only update for EM
					eg.setOutputVector(grad);
				} else {
					double prob = probDistr.getProbOfBeingTrue();
					double stateProb = 1;
					// Only set for EM
					if (cmdArgs.isSoftM()){
						double alpha = cmdArgs.getAlpha();
						double beta = cmdArgs.getBeta();
						if (eg.isOriginalTruthValue()) {

							eg.setOutputValue(1 - prob/(prob + (1-prob)* Math.exp(alpha)));
						} else {

							eg.setOutputValue(1 - prob/(prob + (1-prob)* Math.exp(-beta)));
						}
					} else {
					if (eg.isOriginalTruthValue()) {
						eg.setOutputValue(stateProb * (1 - prob));
					} else {
						eg.setOutputValue(stateProb * (0 - prob));
					}
					}
				}
			}
		}
		// TODO(@hayesall): This `println` was originally conditioned on the result of the removed `isHiddenLiteral` method
		Utils.println("No hidden examples for : " + targetPredicate);
		all_exs = egSubSampler.sampleExamples(all_exs);
		return all_exs;
	}


	// ------------------------------------------------------
	// ------------------------------------------------------
	// Functions that write various useful theory/prolog files
	// ------------------------------------------------------
	// ------------------------------------------------------
	static final String LOG_PRIOR_PREDICATE = "logPrior";
	private static final String STEPLEN_PREDICATE_PREFIX = "stepLength";

	private File getWILLsummaryFile() {  // Always recompute in case 'targetPredicate' changes.
		return Utils.ensureDirExists(getWILLFile(cmdArgs.getModelDirVal(), cmdArgs.getModelFileVal(), targetPredicate));
	}
	
	public static String getWILLFile(String dir, String postfix, String predicate) {
		String filename = dir + "/WILLtheories/" + predicate + "_learnedWILLregressionTrees";
		if (postfix != null) {
			filename += "_" + postfix;
		}
		filename += Utils.defaultFileExtensionWithPeriod;
		return filename;
	}

	private void reportStats() {
		setup.reportStats();
		Utils.println("\n% Memory usage by LearnBoostedRDN:");
		Utils.println("%  |egs|                = " + Utils.comma(egs));
		Utils.println("%  |theseFlattenedLits| = " + Utils.comma(theseFlattenedLits));
	}


	private void addToFlattenedLiterals(Collection<Literal> lits) { // Written by JWS.
		if (lits == null) { return; }
		for (Literal lit : lits) {
			if (!(lit.member(theseFlattenedLits, false))) {
				theseFlattenedLits.add(lit);
			}
		}
	}
	private void dumpTheoryToFiles(Theory th, int i) {
		String stringToPrint = (i < 0 ? "" : "\n%%%%%  WILL-Produced Tree #" + (i + 1) + " @ " + Utils.getDateTime() + ".  [" + Utils.reportSystemInfo() + "]  %%%%%\n\n");
		if (debugLevel > 0 && i >= 0) { Utils.println(stringToPrint); }
		File file = getWILLsummaryFile();
		if (i >= 0) { Utils.appendString(file, stringToPrint + th.toPrettyString(), cmdArgs.useLockFiles); } 
		else { // Write a file right away in case a run crashes.
			
			// First save the old model file
			// Rename single model files.
			if (file.exists()) {
				RunBoostedRDN.renameAsOld(file);
			}
			
			
			stringToPrint = setup.getHandler().getStringToIndicateCurrentVariableNotation();  // Assume we don't change the variable indicator mid-run.
			stringToPrint += "\n% maxTreeDepthInNodes                 = " + Utils.comma(setup.getOuterLooper().getMaxTreeDepth())                        + "\n";
			stringToPrint +=   "% maxTreeDepthInLiterals              = " + Utils.comma(setup.getOuterLooper().getMaxTreeDepthInLiterals())              + "\n";
			stringToPrint +=   "% maxNumberOfLiteralsAtAnInteriorNode = " + Utils.comma(setup.getOuterLooper().getMaxNumberOfLiteralsAtAnInteriorNode()) + "\n";
			stringToPrint +=   "% maxFreeBridgersInBody               = " + Utils.comma(setup.getOuterLooper().innerLoopTask.maxFreeBridgersInBody)      + "\n";
			stringToPrint +=   "% maxNumberOfClauses                  = " + Utils.comma(setup.getOuterLooper().maxNumberOfClauses)                       + "\n";
			stringToPrint +=   "% maxNodesToConsider                  = " + Utils.comma(setup.getOuterLooper().innerLoopTask.getMaxNodesToConsider())    + "\n";
			stringToPrint +=   "% maxNodesToCreate                    = " + Utils.comma(setup.getOuterLooper().innerLoopTask.getMaxNodesToCreate())      + "\n";
			stringToPrint +=   "% maxAcceptableNodeScoreToStop        = " + Utils.truncate(setup.getOuterLooper().getMaxAcceptableNodeScoreToStop(), 3)  + "\n";
			stringToPrint +=   "% negPosRatio                         = " + Utils.truncate(cmdArgs.getSampleNegsToPosRatioVal(),3)                       + "\n";
			stringToPrint +=   "% testNegPosRatio                     = " + Utils.truncate(cmdArgs.getTestNegsToPosRatioVal(),  3)                       + "\n";
			stringToPrint +=   "% # of pos examples                   = " + Utils.comma(setup.getOuterLooper().getNumberOfPosExamples())                 + "\n";
			stringToPrint +=   "% # of neg examples                   = " + Utils.comma(setup.getOuterLooper().getNumberOfNegExamples())                 + "\n";
			Utils.writeStringToFile(stringToPrint + "\n", file); 
		}
		if (i >= 0) {
			if (debugLevel > 0) { Utils.println(th.toPrettyString()); }
			// 	Model directory is set to the working directory as the default value.
			if (th instanceof TreeStructuredTheory) {
				String tree_dotfile = cmdArgs.getModelDirVal() + "bRDNs/dotFiles/WILLTreeFor_" + targetPredicate + i + ".dot";
				Utils.ensureDirExists(tree_dotfile);
				((TreeStructuredTheory)th).writeDOTFile(tree_dotfile);
			}
		}
	}

	/*
	 * 
	 * @param i The tree index(starts from 1)
	 * @return Suffix that is used for filenames and rules.
	 */
	private static String getTreeSuffix(int i) {
		return "_tree" + i;
	}
	 
	static String stepLengthPredicate(int i) {
		return LearnBoostedRDN.STEPLEN_PREDICATE_PREFIX + getTreeSuffix(i);
	}
	
	private void addPrologCodeForUsingAllTrees(ConditionalModelPerPredicate rdn, int numberOfTrees) { // Added by JWS.
		if (numberOfTrees < 1) { return; }
		File file = getWILLsummaryFile();
		List<Literal> targets = setup.getInnerLooper().getTargets();
		Literal       target  = null;
		if (Utils.getSizeSafely(targets) == 1) { target = targets.get(0); } else { Utils.error("Should only have one target.  Have: " + targets); }
		assert target != null;
		if (!target.predicateName.name.equals(targetPredicate) && !target.predicateName.name.equals(WILLSetup.multiclassPredPrefix + targetPredicate) ) {
			Utils.error("These predicate names should match: targetPredicate = " + targetPredicate + " and target = " + target); 
		}

		StringBuilder stringToPrint = new StringBuilder("\n\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n%%%%%  Final call for computing score for " + targetPredicate + ".  %%%%%\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n\n");

		for (int i = 0; i < numberOfTrees; i++) {
			String sentence = rdn.getStepLengthSentence(i+1);
			stringToPrint.append(sentence).append("\n");
		}
		
		stringToPrint.append("\n").append(rdn.getLogPriorSentence());

		stringToPrint.append("\n").append(getComputationPrologRules(numberOfTrees));
		if (!theseFlattenedLits.isEmpty()) {
			stringToPrint.append("\nflattenedLiteralsInThisSetOfTrees(").append(targetPredicate).append(", ").append(theseFlattenedLits.size()).append(", [\n");
			boolean firstTime = true;
			for (Literal lit : theseFlattenedLits) {
				if (firstTime) { firstTime = false; } else { stringToPrint.append(",\n"); }
				stringToPrint.append("   ").append(lit);
			}
			stringToPrint.append("]).");
			theseFlattenedLits.clear();
		} else {
			stringToPrint.append("\nflattenedLiteralsInThisSetOfTrees(0, []).");
		}

		Utils.appendString(file, stringToPrint.toString(), cmdArgs.useLockFiles);
		if (debugLevel > 0) { Utils.println(stringToPrint.toString()); }
	}



	private String getComputationPrologRules(int numberOfTrees) {
		String totalStr    = setup.getInnerLooper().getStringHandler().convertToVarString("Total");
		String treeStr     = setup.getInnerLooper().getStringHandler().convertToVarString("TreesToUse");
		String stepStr     = setup.getInnerLooper().getStringHandler().convertToVarString("StepLen");
		String logPriorStr = setup.getInnerLooper().getStringHandler().convertToVarString("LogPrior");
		
		StringBuilder argsString  = new StringBuilder();
		// The error checking whether this matches the target predicate is done in addPrologCodeForUsingAllTrees.
		List<Literal> targets = setup.getInnerLooper().getTargets();
		Literal       target  = null;
		if (Utils.getSizeSafely(targets) == 1) { target = targets.get(0); } else { Utils.error("Should only have one target.  Have: " + targets); }

		assert target != null;
		for (int i = target.numberArgs() - 1; i >= 0; i--) { argsString.insert(0, target.getArgument(i) + ", "); }
		StringBuilder stringToPrint = new StringBuilder(targetPredicate + "(" + argsString + totalStr + ") :- // A general accessor. \n");
		stringToPrint.append("   ").append(targetPredicate).append("(").append(argsString).append("1000000, ").append(totalStr).append("), !.\n");
		stringToPrint.append(targetPredicate).append("(").append(argsString).append(totalStr).append(") :- waitHere(\"This should not fail\", ").append(targetPredicate).append("(").append(argsString).append(totalStr).append(")).\n\n");

		stringToPrint.append(targetPredicate).append("(").append(argsString).append(treeStr).append(", ").append(totalStr).append(") :- // A tree-limited accessor (e.g., for tuning the number of trees to use).\n");
		stringToPrint.append("   " + LOG_PRIOR_PREDICATE + "(").append(logPriorStr).append("),\n");
		for (int i = 1; i <= numberOfTrees; i++) {
			stringToPrint.append("   getScore_").append(targetPredicate).append(getTreeSuffix(i)).append("(").append(argsString).append(treeStr).append(", ").append(totalStr).append(i).append("),\n");
		}

		stringToPrint.append("   ").append(totalStr).append(" is ").append(logPriorStr);
		for (int i = 1; i <= numberOfTrees; i++) {
			stringToPrint.append(" + ").append(totalStr).append(i);
		}
		stringToPrint.append(",\n   !.\n").append(targetPredicate).append("(").append(argsString).append(treeStr).append(", ").append(totalStr).append(") :- waitHere(\"This should not fail\", ").append(targetPredicate).append("(").append(argsString).append(treeStr).append(", ").append(totalStr).append(")).\n");
		for (int i = 1; i <= numberOfTrees; i++) { 
			stringToPrint.append("\ngetScore_").append(targetPredicate).append(getTreeSuffix(i)).append("(").append(argsString).append(treeStr).append(", 0.0) :- ").append(i).append(" > ").append(treeStr).append(", !.");
			stringToPrint.append("\ngetScore_").append(targetPredicate).append(getTreeSuffix(i)).append("(").append(argsString).append(treeStr).append(", ").append(totalStr).append(i).append(") :- ").append(targetPredicate).append("_tree").append(i).append("(").append(argsString).append(totalStr).append("), ").append(stepLengthPredicate(i)).append("(").append(stepStr).append("), ").append(totalStr).append(i).append(" is ").append(totalStr).append(" * ").append(stepStr).append(".\n");
		}
		return stringToPrint.toString();
	}

	public void setTargetPredicate(String targetPredicate) {
		this.targetPredicate = targetPredicate;
	}

}