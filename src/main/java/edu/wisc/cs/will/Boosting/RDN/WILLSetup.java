package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.ILP.*;
import edu.wisc.cs.will.ResThmProver.*;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.stdAIsearch.BestFirstSearch;
import edu.wisc.cs.will.stdAIsearch.SearchStrategy;

import java.io.File;
import java.io.IOException;
import java.util.*;

/*
 *
 * @author shavlik
 * @author tushar
 */
public final class WILLSetup {

	// TODO(@hayesall): The `WILLSetup.outerLooper` ILPouterLoop is touched by quite a few functions.
	private ILPouterLoop outerLooper;

	// These are meant for ease of access and should never be modified.
	// They can also be obtained by using outerLooper.
	private LearnOneClause innerLooper;
	private HandleFOPCstrings handler;
	private HornClauseContext context;

	private Map<String, List<Example>> backupPosExamples;
	private Map<String, List<Example>> backupNegExamples;

	public boolean useMLNs = false;
	public boolean learnClauses = false;

	/**
	 * Cached list of predicate and arities for neighboring facts
	 */
	private List<PredicateNameAndArity> neighboringFactFilterList = null;
	
	public CommandLineArguments cmdArgs;
	public WILLSetup() { }

	private String getRunTypeMarker() {
		boolean learn = cmdArgs.isLearnVal();
		boolean infer = cmdArgs.isInferVal();
		
		if (learn && infer) { return "_learnPlusInfer"; } // Dribble files might overlap in this case.
		if (learn)          { return "_learn";          }
		if (infer)          { return "_infer";          }
		return                       "_runTypeIsUnknown";
	}

	public boolean setup(CommandLineArguments args, String directory, boolean forTraining) {

		this.cmdArgs = args;
		this.useMLNs = args.isLearnMLN();
		this.learnClauses = args.isLearningMLNClauses();

		Utils.Verbosity defaultVerbosity = Utils.Verbosity.Medium;

		// TODO(@hayesall): Providing a seed could be useful for replicating results.
		//	Utils.seedRandom((long) 12345); // Use this if we want to repeat runs exactly.

		Utils.seedRandom(System.currentTimeMillis() % 100000); // Only use the last few digits (though probably doesn't matter).  JWS
		Utils.setVerbosity(defaultVerbosity);

		File dir = new CondorFile(directory);

		if (!dir.isDirectory()) {
			throw new IllegalArgumentException("Unable to find task directory: " + directory + ".");
		}

		directory     = dir.getPath();
		String prefix = dir.getName();

		// Slice the '/' off the prefix if it was passed in with one ...
		if ( prefix.endsWith("/" ) ) {
			prefix = prefix.substring(0, prefix.length() - 1);
		}

		String[] file_paths = new String[4];

		file_paths[0] = directory + "/" + prefix + "_pos"   + Utils.defaultFileExtensionWithPeriod;
		file_paths[1] = directory + "/" + prefix + "_neg"   + Utils.defaultFileExtensionWithPeriod;
		file_paths[3] = directory + "/" + prefix + "_facts" + Utils.defaultFileExtensionWithPeriod;
		file_paths[2] = directory + "/" + prefix + "_bk"                                    + Utils.defaultFileExtensionWithPeriod;

		String appendToPrefix="";
		if (forTraining && cmdArgs.getModelFileVal() != null) {
			appendToPrefix = cmdArgs.getModelFileVal();
		}
		if (!forTraining && cmdArgs.getModelFileVal() != null) {
			appendToPrefix = cmdArgs.getModelFileVal();
		}

		// Try to place dribble files in the directory where RESULTS will go.
		String resultsDir = cmdArgs.getResultsDirVal();
		if (resultsDir == null) { resultsDir = directory + "/"; }

		Utils.createDribbleFile(resultsDir + prefix + getRunTypeMarker() + appendToPrefix  + "_dribble" + Utils.defaultFileExtensionWithPeriod);
		Utils.touchFile(        resultsDir + prefix + getRunTypeMarker() + appendToPrefix  + "_started" + Utils.defaultFileExtensionWithPeriod);
		createRegressionOuterLooper(file_paths, directory, prefix, cmdArgs.getSampleNegsToPosRatioVal(), cmdArgs.isLearnRegression());

		Utils.println("\n% Initializing the ILP inner looper.");
		getOuterLooper().initialize(false);

		Utils.println("% Old dir" + cmdArgs.getModelDirVal());
		if (cmdArgs.getModelDirVal() == null) {
			Utils.println("Setting model dir");	
			cmdArgs.setModelDirVal(getOuterLooper().getWorkingDirectory() + "/models/");
		}
		if (cmdArgs.getResultsDirVal() == null) { // Usually we want MODEL and RESULTS to be the same, but not if we're running on a fresh testset (i.e., one completely separate from the trainset).
			cmdArgs.setResultsDirVal(cmdArgs.getModelDirVal());
		}

		List<Literal> targets = getInnerLooper().targets;
		Set<Integer> arities = new HashSet<>(4);
		if (targets != null) for (Literal target : targets) { arities.add(target.getArity()); }

		// Use LIST since there can (legally) be duplicates.
		List<Example> posExamplesRaw = getOuterLooper().getPosExamples();
		List<Example> negExamplesRaw = getOuterLooper().getNegExamples() == null ? new ArrayList<>(): getOuterLooper().getNegExamples();
		List<Example> posExamples    = new ArrayList<>(posExamplesRaw.size());
		List<Example> negExamples    = new ArrayList<>(negExamplesRaw.size());
		
		if (targets != null) {
			for (Example pos : posExamplesRaw) {
				if (arities.contains(pos.getArity())) { 
					// If not in the list of targets, we would add to facts
					if (cmdArgs.getTargetPredVal().contains(pos.predicateName.name)) {
						posExamples.add(pos);
					} else {
						addFact(pos);
					}
				} else { 
					Utils.println(" Ignore this pos (arity not in " + arities + "): " + pos); 
				}
			}
			for (Example neg : negExamplesRaw) {
				if (arities.contains(neg.getArity())) {
					// If not in the list of targets, we would add to facts
					if (cmdArgs.getTargetPredVal().contains(neg.predicateName.name)) {
						negExamples.add(neg);
					}
				} else { 
					Utils.println(" Ignore this neg (arity not in " + arities + "): " + neg);
				}
			}

		} else {
			// If no targets (say because only testing and there are no positive examples), then simply accept all the examples.
			// If not in the list of targets, we would add to facts

			for (Example neg : negExamplesRaw) {
				// If not in the list of targets, we would add to facts
				if (cmdArgs.getTargetPredVal().contains(neg.predicateName.name)) {
					negExamples.add(neg);
				}
			}
		}

		Utils.println("\n% Have " + Utils.comma(posExamplesRaw) + " 'raw' positive examples and kept " + Utils.comma(posExamples) + ".");
		Utils.println(  "% Have " + Utils.comma(negExamplesRaw) + " 'raw' negative examples and kept " + Utils.comma(negExamples) + ".");

		// These shouldn't be RegressionRDNExamples. They are assumed to be "Example"s. 
		backupPosExamples = getExamplesByPredicateName(posExamples); // Do bagging on the outermost loop.
		backupNegExamples = getExamplesByPredicateName(negExamples);	// But only if TRAINING.
		// Needed to get examples from fact files.
		fillMissingExamples();

		if (backupPosExamples != null) for (String target : backupPosExamples.keySet()) {
			Collection<Example> posegs = backupPosExamples.get(target);
			Collection<Example> negegs = backupNegExamples.get(target);
			Example.labelTheseExamples("#pos=", posegs);  // Used in comments only.
			Example.labelTheseExamples("#neg=", negegs);  // Used in comments only.
			Utils.println("\n% processing backup's for " + target +"\n%  POS EX = " + Utils.comma(posegs) +  "\n%  NEG EX = " + Utils.comma(negegs)	);
			
		}
		if (Utils.getSizeSafely(backupPosExamples) < 1) {
			if (Utils.getSizeSafely(backupNegExamples) < 1) { Utils.println("No pos nor neg examples!"); return false; }
		}

		if (Utils.getSizeSafely(backupPosExamples) + Utils.getSizeSafely(backupNegExamples) < 1) {
			// TODO(hayesall): Refactored to remove `getDoInferenceIfModNEqualsThis()`, safe to delete?
			Utils.println("No pos nor neg examples after calling getDoInferenceIfModNequalsThis()!"); 
			return false; 
		}
		
		reportStats();

		return true;
	}

	/**
	 * This method moves facts to Examples if they are part of the joint inference task.
	 */
	private void fillMissingExamples() throws RuntimeException {
		Set<String> missingPositiveTargets = new HashSet<>();
		for (String pred : cmdArgs.getTargetPredVal()) {
			// Make sure all targets have facts
			if (!backupPosExamples.containsKey(pred) ||
				 backupPosExamples.get(pred) == null ||
				 backupPosExamples.get(pred).isEmpty()) {
				Utils.println("% No pos ex for " + pred);
				missingPositiveTargets.add(pred);
			}
			// Make sure all targets have facts
			if (!backupNegExamples.containsKey(pred) ||
				backupNegExamples.get(pred) == null ||
				backupNegExamples.get(pred).isEmpty()) {
				Utils.println("% No neg ex for " + pred);
			}
			// Initialize the hash map
			backupPosExamples.computeIfAbsent(pred, k -> new ArrayList<>());
			backupNegExamples.computeIfAbsent(pred, k -> new ArrayList<>());
		}

		if (!missingPositiveTargets.isEmpty()) {
			throw new RuntimeException("If you've reached this point, something has gone wrong.");
		}
	}

	void reportStats() {
		Utils.println("\n% Memory usage by WILLSetup (just counts # targets?):");
		Utils.println("%  |backupPosExamples| = " + Utils.comma(backupPosExamples));
		Utils.println("%  |backupNegExamples| = " + Utils.comma(backupNegExamples));
		Utils.println("%  |predicatesAsFacts| = " + Utils.comma(predicatesAsFacts));
		Utils.println("%  |addedToFactBase|   = " + Utils.comma(addedToFactBase));
	}	
	
	public void prepareFactsAndExamples(String predicate) {
		prepareFactsAndExamples(backupPosExamples, backupNegExamples, predicate, true);
	}

	// Maintain a list of predicates that are already added, so that we can save on time.
	private final HashSet<String> predicatesAsFacts = new HashSet<>();
	private final HashSet<Literal> addedToFactBase  = new HashSet<>();

	private final Set<PredicateNameAndArity> backupTargetModes=new HashSet<>();

	void addAllTargetModes() {
		if (backupTargetModes.isEmpty()) {
			return;
		}
		
		for (PredicateNameAndArity mode : backupTargetModes) {
			getInnerLooper().addBodyMode(mode);
		}
		backupTargetModes.clear();
	}
	
	void prepareFactsAndExamples(Map<String, List<Example>> posEg,
								 Map<String, List<Example>> negEg,
								 String predicate, boolean forLearning) {

		if (posEg.keySet().size() > 1 || negEg.keySet().size() > 1) {
			// JWS added the negEq check since we need to work with only NEG examples (ie, on an unlabeled testset).
			throw new RuntimeException("Should only be possible when there is more than one target.");
		}
		prepareExamplesForTarget(posEg.get(predicate), negEg.get(predicate), predicate, forLearning);
	}

	public void prepareExamplesForTarget(String predicate) {
		prepareExamplesForTarget(backupPosExamples.get(predicate), backupNegExamples.get(predicate), predicate, true);
	}	
	
	private void prepareExamplesForTarget(List<Example> newPosEg,
										  List<Example> newNegEg,
										  String predicate,
										  boolean forLearning) {

		getOuterLooper().setPosExamples(new ArrayList<>(newPosEg));
		getOuterLooper().setNegExamples(new ArrayList<>(newNegEg));

		if (forLearning) {
			// 	Move the examples into facts and get facts to predicates.
			getOuterLooper().morphToRDNRegressionOuterLoop(
					1,
					0,
					cmdArgs.getSampleNegsToPosRatioVal(),
					cmdArgs.getSamplePosProbVal(),
					cmdArgs.isLearnMLN() && cmdArgs.isLearningMLNClauses(),
					cmdArgs.isLearnRegression());
		}
		// Set target literal to be just one literal.
		getOuterLooper().innerLoopTask.setTargetAs(predicate, false, null);
		handler.getPredicateName(predicate).setCanBeAbsent(-1);

		
	}

	private Map<String,List<Example>> getExamplesByPredicateName(List<Example> examples) {
		// TODO(@TVK): remove the common stuff from `getJointExamples`

		Map<String,List<Example>> result = new HashMap<>();

		for (Example eg : examples) {
			String target = eg.predicateName.name;
			if (!result.containsKey(target)) {
				result.put(target, new ArrayList<>());
			}
			result.get(target).add(eg);
		}
		return result;
	}
	
	public HashMap<String,List<RegressionRDNExample>> getJointExamples(Set<String> targets) {
		// TODO(@hayesall): Large section of duplicated code, refactor.

		HashMap<String,List<RegressionRDNExample>> result = new HashMap<>();
		
		// TODO(?): Currently assuming they are marked as examples already.
		int counterPos = 0, counterNeg = 0;
		for (String pred : targets) {
			if (!result.containsKey(pred)) {
				result.put(pred, new ArrayList<>());
			}
			List<Example> lookupPos = backupPosExamples.get(pred);  Utils.println("\n% for " + pred + " |lookupPos| = " + Utils.comma(lookupPos));
			if (lookupPos != null) for (Example ex : lookupPos) {
				RegressionRDNExample rex = new RegressionRDNExample(getHandler(), ex.extractLiteral(), 1, ex.provenance, ex.extraLabel);
				if (cmdArgs.isLearnRegression()) {
					if (ex instanceof RegressionExample) {
						rex.originalRegressionOrProbValue = ((RegressionExample)ex).getOutputValue();
					} else {
						Utils.waitHere("Expected regression examples for learning regression trees");
					}
				}
				rex.setOriginalTruthValue(true);
				String target = ex.predicateName.name;
				if (targets.contains(target)) { 
					if (!result.containsKey(target)) {
						result.put(target, new ArrayList<>());
					}
					result.get(target).add(rex); counterPos++;

				} else {
					Utils.error("Didn't expect this example as target. Model absent: " + target);
				}
			}
			List<Example> lookupNeg = backupNegExamples.get(pred);  Utils.println("% for " + pred + " |lookupNeg| = " + Utils.comma(lookupNeg));
			if (lookupNeg != null) for (Example ex  : lookupNeg) {
				RegressionRDNExample rex = new RegressionRDNExample(getHandler(), ex.extractLiteral(), 0, ex.provenance, ex.extraLabel);
				rex.setOriginalTruthValue(false);
				if (cmdArgs.isLearnRegression()) {
					if (ex instanceof RegressionExample) {
						rex.originalRegressionOrProbValue = ((RegressionExample)ex).getOutputValue();
					} else {
						Utils.waitHere("Expected regression examples for learning regression trees");
					}
				}
				String target = ex.predicateName.name;
				if (targets.contains(target)) { 
					if (!result.containsKey(target)) {
						result.put(target, new ArrayList<>());
					}
					result.get(target).add(rex); counterNeg++;
				} else {
					Utils.error("Didn't expect this example as target. Model absent: " + target);
				}
			}	

		}

		Utils.println("% getJointExamples: |pos| = " + Utils.comma(counterPos) + ", |neg| = " + Utils.comma(counterNeg));
		return result;
	}

	public Clause convertFactToClause(String fact) {
		return getInnerLooper().getParser().parseDefiniteClause(fact);
	}

	private void setOuterLooper(ILPouterLoop outerLooper) {
		this.outerLooper = outerLooper;
		this.innerLooper = outerLooper.innerLoopTask;
		this.handler     = outerLooper.innerLoopTask.getStringHandler();
		this.context     = outerLooper.innerLoopTask.getContext();
		neighboringFactFilterList = null;
	}

	public ILPouterLoop getOuterLooper() {
		return outerLooper;
	}

	public LearnOneClause getInnerLooper() {
		return innerLooper;
	}

	public HandleFOPCstrings getHandler() {
		return handler;
	}

	public HornClauseContext getContext() {
		return context;
	}

	void removeFact(Literal eg) {
		getContext().getClausebase().retractAllClausesWithUnifyingBody(eg);
	}

	void addFact(Literal eg) {
		getContext().getClausebase().assertFact(eg);
	}

	// Pulled out by JWS (7/8/10) so could be called elsewhere for a plain regression-tree learning.
	private void createRegressionOuterLooper(String[] newArgList, String directory, String prefix, double negToPosRatio, boolean isaRegressionTaskRightAway) {

		try {
			SearchStrategy         strategy = new BestFirstSearch();
			ScoreSingleClause        scorer = new ScoreRegressionNode(cmdArgs.isLearnMLN());

			// We're (sometimes) using A SMALL INDEX HERE, since the memory needs are already very large (i.e., trade off time for space).
			// We need to keep all the literals related to a specific proof (i.e., test of a hypothesis) around, but are willing to redo between proofs.
			// TODO(?): add 'runningLargeTask' to the passed-in arguments.

			// Need to set these BEFORE creating the LazyHornClausebase.
			LazyGroundNthArgumentClauseIndex.setMaximumIndexSize(100);
			LazyGroundClauseIndex.setMaximumIndexSize(           100);
					
			HandleFOPCstrings stringHandler = new HandleFOPCstrings(true); // Let the first file read set the default.  (Are libraries read first?)
			HornClausebase clausebase;
			clausebase = new LazyHornClausebase(stringHandler);

			HornClauseContext context = new DefaultHornClauseContext(clausebase);

			// TODO(?): `runningLargeTask`? Add to pass-in arguments?
			context.getStringHandler().variantFactHandling = VariantClauseAction.SILENTLY_KEEP_VARIANTS;
			context.getStringHandler().variantRuleHandling = VariantClauseAction.WARN_AND_REMOVE_VARIANTS;

			stringHandler.keepQuoteMarks                       = true;
			stringHandler.dontComplainIfMoreThanOneTargetModes = true;
			Utils.println("\n% Calling ILPouterLoop from createRegressionOuterLooper.");
			setOuterLooper(new ILPouterLoop(directory, prefix, newArgList, strategy, scorer, new Gleaner(), context, isaRegressionTaskRightAway));
			Utils.println("\n% The outer looper has been created.");
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Encountered a problem: " + e);
		}

        getInnerLooper().maxSearchDepth     =  10000;
		getInnerLooper().verbosity          =      0;

		getInnerLooper().maxNumberOfNewVars =      7;
		getInnerLooper().maxDepthOfNewVars  =      7;
		getOuterLooper().max_total_nodesExpanded = 10000000;
		getOuterLooper().max_total_nodesCreated  = 10 * getOuterLooper().max_total_nodesExpanded;
		getInnerLooper().setMEstimatePos(0.1);
		getInnerLooper().setMEstimateNeg(0.1);
		getInnerLooper().setMaxNegCoverage(0.499);

		getInnerLooper().getProver().setMaxNodesToConsider(1000000);
		getInnerLooper().getProver().setMaxNodesToCreate( 10000000);

		// JWS: this is (sometimes) set high (multiple minutes), e.g. for a threshold calc for the breast-cancer dataset.
		getInnerLooper().getProver().setMaximumClockTimePerIterationInMillisec(300000);

		// Units are milliseconds.  So 3600000 = 1 hour.
		getInnerLooper().setMaximumClockTimePerIterationInMillisec(           7200000);

		// Sometimes we start out with a BOOLEAN task then later turn into a regression one.
		getInnerLooper().regressionTask = isaRegressionTaskRightAway;

		// This is a fraction of the current set of examples at the root.
		double minFractionOnBranches = Math.max(0.005, 0.05 / negToPosRatio);

		// If a set has less than this much VARIANCE per example, it will become a leaf.
		getOuterLooper().setMaxAcceptableNodeScoreToStop(0.0025);

		// If a recursive call involves fewer than this number of examples, make a leaf node (ALSO IMPACTS THE INITIAL CALL?)
		getOuterLooper().setOverallMinPosWeight(10);
		if (!cmdArgs.isLearnRegression()) {
			getInnerLooper().setMinPosCoverageAsFraction(minFractionOnBranches);   // For a clause to be acceptable, it needs to cover at least this fraction of the examples (and not more than 1 minus this fraction).
		}

		// The next line overrides the one immediately above this comment.
		// Need to be careful here, since data might be quite skewed.  Should really be something like 10% of the majority category.
		getInnerLooper().setMinPosCoverage(3);

		if (!cmdArgs.isLearnRegression()) {
			// And cannot cover too many of the examples.
			getOuterLooper().setMaxRecallOfAcceptableClause(1 - minFractionOnBranches);
		}
		if (cmdArgs.isLearnMLN()) {
			getOuterLooper().setLearnMLNTheory(true);
		}

		// Since WILL focuses on seeds to filter out candidate clauses, we need a good number here because some seeds will go on the "false" branch.  Want to have enough so that on average can find the maximally acceptable skew for the true/false branches.  Or maybe OK to miss these to save time by having a smaller set of seeds?
		getOuterLooper().numberPosSeedsToUse = (int) Math.ceil(5 * negToPosRatio);
		// Only require ONE to be covered (other constraints will filter clauses).
		getInnerLooper().clausesMustCoverFractPosSeeds = 0.999999 / getOuterLooper().numberPosSeedsToUse;
		// Need to cover at least 1% of the examples, even if the root.
		getOuterLooper().setMinPrecisionOfAcceptableClause(0.001);
		getOuterLooper().setMaxNumberOfLiteralsAtAnInteriorNode(1);

		// Counting is from 0 (i.e., this is really "max number of ancestor nodes").  maxNumberOfClauses might 'dominate' this setting.
		getOuterLooper().setMaxTreeDepth(2);

		// This is the body of ONE node.  By allowing more bridgers that literals we can, say, create comparators between two extracted values.
		getOuterLooper().innerLoopTask.maxFreeBridgersInBody = 0;
		// Add 1 here since the root has literals but is at depth 0.
		// We don't want the individual trees to get too complicated, so limit to 4 literals (so if 2 lits per nodes and depth is 2, instead of a max of 6 literals, the limit of 4 will be used).
		// Recall there could be some bridgers at each interior node, so this is allowing some bridgers.
		getOuterLooper().setMaxTreeDepthInLiterals(Math.max(3, (getOuterLooper().getMaxTreeDepth() + 1) * (getOuterLooper().innerLoopTask.maxFreeBridgersInBody + getOuterLooper().getMaxNumberOfLiteralsAtAnInteriorNode())));

		// Reminder: "consider" means "expand" (i.e., remove from the OPEN list and generate its children);  "create" is a counter on children.
		int matLitsAtNode = 1 + getOuterLooper().innerLoopTask.maxFreeBridgersInBody;
		// For reasons of time, don't want to expand too many nodes (does this setting matter if maxLits=1?).  Eg, expand the root, pick the best child, expand it, then pick the overall best unexpanded child, and repeat a few more times.
		getInnerLooper().setMaxNodesToConsider(matLitsAtNode > 1 ?     10 :     50);
		// This can be high since we want the # of expansions to be the limiting factor.
		getInnerLooper().setMaxNodesToCreate(  matLitsAtNode > 1 ?  10000 :  50000);
		// This is the maximum number of non-leaf nodes (tree building is via BEST-FIRST search).  MaxTreeDepth might 'dominate' this setting.
		getOuterLooper().maxNumberOfClauses =  matLitsAtNode > 1 ?     12 :     16 ;
		getOuterLooper().maxNumberOfCycles  =     2 * getOuterLooper().maxNumberOfClauses;

		if (cmdArgs.isLearnRegression()) {
			// This should be zero since we really don't have any negatives here (we instead are doing regression).
			getInnerLooper().minNumberOfNegExamples = 0;
		} else {
			// TVK : This SHOULDN'T be zero here, it is set later in morph. This is used to create negative examples.
			getInnerLooper().minNumberOfNegExamples = 10;
		}

		// Other constraints say that at least half the examples must be covered, and sometimes we need to use the negation to do that.

		// TODO(?): is this time PER TREE?  I think so ...
		// TODO(?): determine if when time runs out, a reasonable model results. JWS: I think that sometimes timing out makes a NOT_* seem better than it should.
		double maxHoursToRunPerTree = getOuterLooper().getMaxTreeDepth() * 4.0;
		// TODO - should also have a maxTime for learning ALL N trees.  Maybe write the remaining trees as adding zero to the wgt'ed sum, since other code looks for maxTrees.
		getOuterLooper().setMaximumClockTimeInMillisec((long) (maxHoursToRunPerTree * 60 * 60 * 1000));
	}

	void getListOfPredicateAritiesForNeighboringFacts() {
		if (neighboringFactFilterList == null) {
			Set<PredicateNameAndArity> pars = new HashSet<>(BoostingUtils.convertBodyModesToPNameAndArity(getInnerLooper().getBodyModes()));
			neighboringFactFilterList = new ArrayList<>(pars);
		}
	}

}
