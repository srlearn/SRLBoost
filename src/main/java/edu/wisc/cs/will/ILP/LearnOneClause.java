package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.Boosting.OneClass.PairWiseExampleScore;
import edu.wisc.cs.will.DataSetUtils.ArgSpec;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.DataSetUtils.TypeManagement;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolderForMLN;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolderForRDN;
import edu.wisc.cs.will.ILP.Regression.RegressionVectorInfoHolderForRDN;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.ResThmProver.HornClausebase;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.stdAIsearch.*;

import javax.swing.event.EventListenerList;
import java.io.*;
import java.util.*;
 
/*
 * @author shavlik
 *
 * This is the ILP inner loop.  See broad-based comments in ILPouterLoop.java
 *
 *
 * TODO list: (not meant to be understood by users - this is simply a place to collect local notes)
 *
 *
 *
 *  check for other uses of cached files (other than neg examples?)
 *    document all the cached files in one place!
 *
 *
 * 	post-pruning code: drop one literal (if legal to do so?) and repeat as long as progress made
 * 		- maybe say unacceptable if ANY pos are lost?  Are using F1 as the heuristic to hill climb?
 *
 * 		figure out how to avoid too many outer parents when printString'ing
 *
 * List<Example> coveredPosExamplesThisCycle = innerLoopTask.collectPosExamplesCovered(bestNode); NEED TO DO THIS MORE EFFICIENTLY!
 *
      Handle these (for both pos and neg)
:- jws_set(positive_examples_filtered_out,        25).
:- jws_set(inverse_sampling_rate_of_neg_examples, 4.0000).

		if something is no good in RRR for one set of seeds,
		it will also be no good for restarts in that seed
			- keep a hashmap for these  KEEP SAME ROOT

			save gleaner after every N outer loops?


 *        no hits to these (not even 2x)
 *          between_args_frequencies.b:mode: phrase_contains_several_between_10x_word(+phrase, #arg, #pos,        +fold). %  +fold was #fold
            between_args_frequencies.b:precompute1: phrase_contains_several_between_10x_word(Phrase, Arg, POS,        Fold) :-
 *
 *        need to figure out to deal with CLAUSES during parsing (for now, 'canPrune(Literal lit)' does not allow pruning with such cases).
 *
 *        infer modes through deduction and not just from basic facts?  or too cpu-complicated?
 *
 *        in 'precompute:' allow a file name to be provided?  leave for later, since complicated bookkeeping
 *
 *
 *        allow other specs about predicates:
 *
 *        	symmetric: p/2  <-- use this in creating neg examples
 *          symmetric: p(s,s,s,_,_) <-- any permutation of the s's equivalent
 *          etc
//:- symmetric(different_phrases/2).  <-- automatically create prune rules
// :- symmetric(different_words/2).
 *
 *        allow inference of types to be turned off - with some sort of parser command
 *
 *        handle a fact like (where X is a variable):   s(1, X).
 *
 *        make use of 'target' in modes - can put on hold
 * *
 *        accept Aleph's spec for modes?  and for determinations?  - can put on hold
 *   *
 *  	  have an argument that means: clear all cached files (gleaner, precomputed, etc)
 *
 *  	  have a "checkpoint" facility
 *  	  need gleaner to also do this (write and read)
 *
 *
 *  	  here's a Prolog benchmark: http://www.sics.se/sicstus/bench.pl
 *
 *       add Vitor's trick to see if current clause same as previous (maybe hold N such clauses?)
 *          - index by parent node (don't want to "reuse" two nodes with different parents)
 *          - doesn't happen w/o the bottom clause, though confirm current code removes duplicates
 *
 *      think through the Exists stuff and MLNs
 *
 *		allow facts to include lessThan(small, medium) <- assume transitivity [this allows "tiles" to be used on symbolic constants]
 *
 *		if facts have variables in then, is the naming done properly?  probably not ...
 * *
 */

public class LearnOneClause extends StateBasedSearchTask {

	final boolean             whenComputingThresholdsWorldAndStateArgsMustBeWorldAndStateOfAcurrentExample = true; // This will prevent test sets bleeding unto train set (if these stringHandler.locationOfWorldArg or stringHandler.locationOfStateArg are -1, then matching is not required).

	private boolean             createCacheFiles                  = false;   // Create files that cache computations, to save time, for debugging, etc.
	private boolean             useCachedFiles                    = false;   // Files cached (if requested):
	                                                                           //    prune.txt (or whatever Utils.defaultFileExtensionWithPeriod is)
																			   //    types.txt
	                                                                           //    gleaner.txt (users can name this whatever they wish)
																			   //    the generated negative examples (same file name as used for negatives)

	Object              caller     = null;                           // The instance that called this LearnOneClause instance.
	String              callerName = "unnamed caller";               // Used to annotate printing during runs.

	private final FileParser          parser;

	private   boolean             isaTreeStructuredTask = false; // For a tree-structured task, we don't want to generalize the heads (e.g., p(X,X) might be a good rule - will need to learn this via sameAs() calls ...).
	SingleClauseNode    currentStartingNode   = null;  // For some calculations we want to stop at this node.

	public    boolean			  regressionTask    = false; // Is this a REGRESSION task?
	boolean			  mlnRegressionTask	= false;
    private boolean             learnMultiValPredicates             = false;
    boolean			  oneClassTask		= false;
    public 	  PairWiseExampleScore occScorer			= null;
	final boolean 			  sampleForScoring  = false;
	final int				  maxExamplesToSampleForScoring = 300;

	final int                 maxCrossProductSize               =1000;     // When generating candidate groundings of a literal in the child-generator, randomly seleect if more than this many.
	int                 maxBodyLength                     =   9;     // Max length for the bodies of clauses.
	public    int                 maxFreeBridgersInBody             = maxBodyLength; // Bridgers can run amok so limit them (only has an impact when countBridgersInLength=true).  This is implemented as follows: the first  maxBridgersInBody don't count in the length, but any excess does.
	public    int                 maxNumberOfNewVars                =  10;     // Limit on the number of "output" variables used in a rule body.
	public    int        		  maxDepthOfNewVars                 =   7;     // The depth of variables in the head is 0.  The depth of a new variable is 1 + max depth of the input variables in the new predicate.
	public    int                 maxPredOccurrences                =   5;     // Maximum number of times a given predicate can appear in a clause (REGARDLESS of whether or not the input variables differ).  Ccn be overwritten on a per-predicate basis.
	int                 maxConstantBindingsPerLiteral     = 100;     // When trying to fill #vars in a new literal, don't create more than this many candidates (if more than randomly discard - note, if more than 1000 collected, the collecting process terminates, so if more than 1000 possibilities, selection will NOT be random).  If this is not a positive number, it is ignored.  Note: this can also be accomplished via maxPredOccursPerInputVars, though that does not solely deal with #vars and that is a DEPTH limit whereas this is a BREADTH limit.  TODO allow this to be done on a per-literal basis?
	private   double              minPosCoverage                    =   2.0;   // [If in (0,1), treat as a FRACTION of totalPosWeight].  Acceptable clauses must cover at least this many positive examples.  NOTE: this number is compared to SUMS of weighted examples, not simply counts (which is why this is a 'double').
	private   double              maxNegCoverage                    =  -1.0;   // [If in (0,1), treat as a FRACTION of totalNegWeight].  Acceptable clauses must cover no  more this many negative examples.  NOTE: this number is compared to SUMS of weighted examples, not simply counts (which is why this is a 'double').  IGNORE IF A NEGATIVE NUMBER.
	double              minPrecision                      =   0.501; // Acceptable clauses must have at least this precision.
	double              maxRecall                         =   1.01;  // When learning trees, don't want to accept nodes with TOO much recall, since want some examples on the 'false' branch.
	double              stopExpansionWhenAtThisNegCoverage =  0.0;   // Once a clause reaches this negative coverage, don't bother expanding it further.
	boolean             stopIfPerfectClauseFound          =   true;  // Might want to continue searching if a good SET of rules (eg, for Gleaner) is sought.
	public    double              clausesMustCoverFractPosSeeds     =   0.499; // ALL candidate clauses must cover at least this fraction of the pos seeds.  If performing RRR, these sets are used when creating the starting points.
	double              clausesMustNotCoverFractNegSeeds  =   0.501; // And all must NOT cover at least this fraction of the negative seeds (if any).
	boolean             allowPosSeedsToBeReselected       =  false;  // Can a positive seed be used more than once (in the ILP outer loop)?
	boolean             allowNegSeedsToBeReselected       =  false;  // Ditto for negatives?
	boolean             stopWhenUnacceptableCoverage      =   true;  // If set to  true, don't continue to prove examples when impossible to meet the minPosCoverage and minPrecision specifications.
	private boolean	          collectTypedConstants             =   true;  // Checks for errors in the data.
	int                 minChildrenBeforeRandomDropping   =  10;     // Before randomly discarding children, there must be this many.
	double              probOfDroppingChild               =  -1.0;   // If not negative, probability of dropping a child.
	private int                 maxSizeOfClosed                   =  100000;     // Limit the closed list to 100K items.  Note that items aren't placed here until EXPANDED, but items wont be placed in OPEN if already in CLOSED.
	public    int                 minNumberOfNegExamples            =  10;     // If less than this many negative examples, create some implicit negative examples.
	public    double              fractionOfImplicitNegExamplesToKeep = 0.10;  // NEW: if > 1.1, then count this NUMBER of examples, otherwise when generating implicit negatives, keep this fraction (but first make sure the min neg's number above is satisfied).
	boolean             requireThatAllRequiredHeadArgsAppearInBody         = false;  // If true, then a clause will not be considered accepted unless all required variables in the head appear in the body.
	boolean             allTargetVariablesMustBeInHead                     = false;
	boolean             dontAddNewVarsUnlessDiffBindingsPossibleOnPosSeeds = true;  // If have p(x) :- q(x,y) but if over all positive seeds can never get x and y to bind to different constants, then use p(x) :- q(x,x).  Similar (equivalent?) to "variable splitting" = false in Aleph.
	long                maxResolutionsPerClauseEval    = 10000000;     // When evaluating a clause, do not perform more than this many resolutions.  If this is exceeded, a clause is said to cover 0 pos and 0 neg, regardless of how many have been proven and it won't be expanded.
	public final boolean             createdSomeNegExamples                  = false; // Record if some negative examples were created (caller might want to write them to a file).
	////////////////////////////////////////////////////////////
	//  Variables for controlling random-rapid-restart searches (i.e., repeatedly randomly create an initial clause, then do some local search around each).
	//    The initial clause randomly created will meet the specification on the positive and negative seeds.
	////////////////////////////////////////////////////////////
	boolean             performRRRsearch      = false;
	int                 beamWidthRRR          =     1; // When doing RRR, use this beam width (if set too low, might not find a starting point for local search of the requested length).
	private int                 minBodyLengthRRR      =     1; // Uniformly choose body lengths from minBodyLengthRRR to maxBodyLengthRRR (inclusive).
	private int                 maxBodyLengthRRR      =    10;
	public    int                 restartsRRR           =   100; // Do this many RRR restarts per "ILP inner loop" call.
	private int                 maxNodesToConsiderRRR =   100; // These are per each RRR iteration.
	private int                 maxNodesToCreateRRR   =  1000;

	////////////////////////////////////////////////////////////
	boolean             stillInRRRphase1      =  true; // In the first phase of RRR, build a random clause that covers the required fraction of POS seeds.
	int                 savedBeamWidth;                // Save the old beam width so it can be restored when in phase 2 of RRR.
	int                 thisBodyLengthRRR;             // The chosen body length for this RRR iteration.
	private List<Example>         posExamples;
    private List<Example>         negExamples;
	double              totalPosWeight = -1.0;   // Sum of the weights on the positive examples.
	double              totalNegWeight;          // Ditto for negative examples.
	double              totalWeightOnPosSeeds  = -1;
	double              totalWeightOnNegSeeds  = -1;
	private List<PredicateNameAndArity> targetModes;     // The modes for the target.
	Set<PredicateNameAndArity>  bodyModes;       // Should we keep as a list so user can impact order they are considered (though that might not matter much ...)?  But if we do then we need to check for duplicates.

	List<Example>       seedPosExamples;
	List<Example>       seedNegExamples;

	PredicateName       procDefinedEnoughDiffMatches   = null;  // This is a built-in predicate that tests if a new literal being added to a clause being grown can be matched in a unique way on some POS seeds.
	PredicateName       procDefinedForConstants        = null;  // This is used to see which constants in the positive seeds can fill some arguments in a new literal.
	PredicateName       procDefinedNeedForNewVariables = null;  // See if these new variables ever bind in the positive seeds to some thing new in the clause (otherwise they aren't needed).  Only used if dontAddNewVarsUnlessDiffBindingsPossibleOnPosSeeds=true.
	List<List<Term>>    collectedConstantBindings;    // This is used as a temporary variable by a method below.
	final BindingList         bindings = new BindingList(); // Only recreate theta if needed, in order to save on creating new lists.

	private boolean              allowMultipleTargets       = true;

	private   List<PredicateNameAndArity>  examplePredicates          = null; // These store the positive example predicates that are eventually turned into targets.
	private   List<List<Term>>     examplePredicateSignatures = null; // Something like [constant, function(constant), constant].

    public    List<Literal>        targets                    = null; // These are the actual targets determined from the examplePredicates.
	List<List<ArgSpec>>  targetArgSpecs             = null; // The info about the target argument being used and the variables matched with their types.
	List<List<Term>>     variablesInTargets         = null; // These are really 'arguments' since it is possible a mode specifies a constant be used.

    final HornClauseContext    context;

	HandleFOPCstrings    stringHandler;
	final Unifier              unifier; // Make instances out of some things that could be 'statics' so the code is safer.
	private   HornClauseProver     prover; // This is initialized by getProver() so please don't use this variable directly.
	PruneILPsearchTree   pruner = null;  // Used to prune search trees that are unlikely to pan out (called by ChildrenClausesGenerator and its extensions).
	private final Precompute           precomputer;
	private   ThresholdManager     thresholdHandler;
	private   InlineManager        inlineHandler; // Handle the in-lining of literal bodies (should only be applied to literals that are only defined by ONE clause).
	private final TypeManagement       typeManager;

	//private   HornClauseProverChildrenGenerator ruleAndFactsHolder;
	private final Reader               posExamplesReader; // We now also delay this in case we want to specify this is a regression task.
	private final Reader               negExamplesReader; // Needed in case implicit negatives need to be created (we delay doing this to allow the caller to set parameters related to this neg-generation process).

	// Clarification on how m-estimates are currently used in this code:
	//  All clauses are assumed to also match mEstimateNeg negative examples
	//  The set of positive examples is assumed to have mEstimatePos examples added to it, but these examples are NOT covered the clause.
	//  So if a clause covers 3 of 7 positive and 2 of 10 negative examples, and these two m-estimates are 1, then
	//    precision = 3 of 3+2+1 and recall = 3 of 7+1
	private   double               mEstimatePos = 0.1; // When computing coverage of a rule use these "m estimates."  NOTE these are also used when examples are weighted, so if total weight is small, might want to change these.
	private   double               mEstimateNeg = 0.1; // Note: these are used in recall as well as precision.

	private final EventListenerList searchListenerList = new EventListenerList();

    private List<Sentence> facts = null; // This temporarily stores the facts between construction and initialization.  After initialization it will be null.

	// Precompute filename : precompute_file_prefix + PRECOMPUTED_FILENAME  + number +  precompute_file_postfix
    // The following values can be set using
    // setParam: precomputePostfix = ".txt".
    // setParam: precomputePrefix = "../../".
    // setParam: numberOfPrecomputes = 100.

    private boolean initialized = false;


	/*
	 * Constructs a new LearnOneClause search.
     */
	public LearnOneClause(String workingDir, String prefix,
						  Reader posExamplesReader, Reader negExamplesReader,
						  Reader backgroundClausesReader, Reader factsReader,
						  SearchStrategy strategy, ScoreSingleClause scorer,
						  SearchMonitor monitor,
						  HornClauseContext context, boolean deferLoadingExamples) {

        taskName = "LearnOneClause";
        this.stringHandler = (context == null ? null : context.getStringHandler());
        if ( stringHandler == null ) stringHandler = new HandleFOPCstrings();
        if ( strategy == null ) strategy = new BestFirstSearch();
        if ( scorer   == null ) scorer   = new ScoreSingleClauseByAccuracy();
        if ( monitor  == null ) monitor  = new Gleaner();

		this.unifier       = Unifier.UNIFIER;
        this.stringHandler = context.getStringHandler();
		this.parser        = context.getFileParser();
		this.setDirectoryName(workingDir);
		this.setPrefix(prefix);
        this.context       = context;

		this.precomputer   = new Precompute();
		this.typeManager   = new TypeManagement(stringHandler);
        
		verbosity = 1;

        setInlineManager(new InlineManager(   stringHandler, getProver().getClausebase()));
        setThresholder(  new ThresholdManager(this, stringHandler, inlineHandler));

        // TODO(@hayesall): AdviceProcessor reads the current `context` and `this`, but does not appear to do anything with it.
		// new AdviceProcessor(context, this);

		// Load BK first since it is the place where 'usePrologVariables' etc is typically set.
		if (backgroundClausesReader != null) { context.assertSentences(readBackgroundTheory(backgroundClausesReader)); }

		Initializer              init        = new InitializeILPsearchSpace();
		ChildrenClausesGenerator nodeGen     = new ChildrenClausesGenerator();
		VisitedClauses           c           = new VisitedClauses(maxSizeOfClosed);
		initalizeStateBasedSearchTask(init, null, monitor, strategy, scorer, nodeGen, c);
		nodeGen.initialize();
		setGleaner(monitor);
		
		// Currently we automatically loading all 'basic' modes unless overridden - this might use a lot of cycles, so use with care.
		String mStr = stringHandler.getParameterSetting("loadAllBasicModes");
		// TODO - these should be lower than the features used for the task; currently handled via cost.
		if (mStr == null || !mStr.equalsIgnoreCase("false")) {
			
			List<Sentence> modeSentences = null;
			try {
				modeSentences = parser.loadAllBasicModes();
			} catch (Exception e) {
				Utils.reportStackTrace(e);
				Utils.error("Problem loading basic mode files.");
			}

            context.assertSentences(modeSentences);
		}
		
		// Currently we automatically loading all libraries unless overridden - only a few and if no modes added, these won't impact run time anyway.
		String vStr = stringHandler.getParameterSetting("loadAllLibraries");
		if (vStr == null || !vStr.equalsIgnoreCase("false")) {
			List<Sentence> librarySentences = null;
			try {
				librarySentences = parser.loadAllLibraries();
			} catch (Exception e) {
				Utils.reportStackTrace(e);
				Utils.error("Problem loading library files.");
			}

            context.assertSentences(librarySentences);
		}

		Utils.println("\n%  Read the facts.");

		if (factsReader != null) {
        	facts = readFacts(factsReader, workingDir);
        	context.assertSentences(facts);
			Utils.println("%  Have read " + Utils.comma(facts) + " facts.");
		}

		// NO LONGER BEING DONE.  checkBKforFacts(); // See if some facts were in the BK file.  If so, move them without complaint.
		if (Utils.getSizeSafely(stringHandler.getKnownModes()) < 1) { Utils.severeWarning("Need to have at least one mode: " + stringHandler.getKnownModes()); }

		this.posExamplesReader = posExamplesReader; // Hold on to in case we want to say this is a regression task.
		this.negExamplesReader = negExamplesReader; // Hold on to this to allow the caller a chance to set parameters (e.g., sampling rate).

        // Wait until initialize() is called, in case some things need to be set.  
		if (!deferLoadingExamples && posExamplesReader != null) { 
			readExamples(posExamplesReader, negExamplesReader);
			closeWithoutException(posExamplesReader);
			if (negExamplesReader       != null) closeWithoutException(negExamplesReader);
		}
        if (factsReader             != null) closeWithoutException(factsReader);
        if (backgroundClausesReader != null) closeWithoutException(backgroundClausesReader);
		Utils.println("\n%  LearnOneClause initialized.");
	}

    private void readExamples(Reader positiveReader, Reader negativeReader) {
		// TODO(@hayesall): `skewMaxNegToPosUse` is always -1, dropping the code related to this.
        if (posExamples == null) {
            setPosExamples(positiveReader == null ? null : readExamples(positiveReader, getDirectoryName()));
        }
        if (negExamples == null && !regressionTask) {
            setNegExamples(negativeReader == null ? null : readExamples(negativeReader, getDirectoryName())); // Negative examples can be EXPLICIT (or absent).
        }
        if (posExamples == null && positiveReader != null) {
            Utils.error("You should provide some positive examples.  None were found in reader '" + positiveReader + "'.");
        }

	}
    // cth: Added so that previous gleaner can be grabbed from the LearnOneClause object
    // needed to make Gleaner setting persistent
    final SearchMonitor getGleaner() {
    	return this.searchMonitor;
    }

	final void setGleaner(SearchMonitor monitor) {

       this.searchMonitor = monitor;

		if (monitor != null) {
			monitor.setSearchTask(this); // Connect the search monitor (if one) to this search task.
		}
	}


	private void checkForSetParameters() {

		// TODO(@hayesall): Are any of these parameters mentioned in the public documentation?
		// 		Anything removed from here will potentially free up other methods for removal.

		String vStr;

		vStr = stringHandler.getParameterSetting("discardIfBestPossibleScoreOfNodeLessThanBestSeenSoFar");
		if (vStr != null) {                       discardIfBestPossibleScoreOfNodeLessThanBestSeenSoFar = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("createCacheFiles");
		if (vStr != null) {                       createCacheFiles                                      = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("requireThatAllRequiredHeadArgsAppearInBody");
		if (vStr != null) {                       requireThatAllRequiredHeadArgsAppearInBody            = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("allTargetVariablesMustBeInHead");
		if (vStr != null) {                       allTargetVariablesMustBeInHead                        = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("stopIfPerfectClauseFound");
		if (vStr != null) {                       stopIfPerfectClauseFound                              = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("useCachedFiles");
		if (vStr != null) {                       useCachedFiles                                        = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("allowPosSeedsToBeReselected");
		if (vStr != null) {                       allowPosSeedsToBeReselected                           = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("allowNegSeedsToBeReselected");
		if (vStr != null) {                       allowNegSeedsToBeReselected                           = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("stopWhenUnacceptableCoverage");
		if (vStr != null) {                       stopWhenUnacceptableCoverage                          = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("collectTypedConstants");
		if (vStr != null) {                       collectTypedConstants                                 = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("dontAddNewVarsUnlessDiffBindingsPossibleOnPosSeeds");
		if (vStr != null) {                       dontAddNewVarsUnlessDiffBindingsPossibleOnPosSeeds    = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("performRRRsearch");
		if (vStr != null) {                       performRRRsearch                                      = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("allowMultipleTargets");
		if (vStr != null) {                       allowMultipleTargets                                  = Boolean.parseBoolean(vStr); }

		vStr = stringHandler.getParameterSetting("minPosCoverage");
		if (vStr != null) {
			double value_minPosCoverage = Double.parseDouble(vStr);  if (value_minPosCoverage < 1) { Utils.waitHere("minPosCoverage expressed as a FRACTION no longer supported.  Use minPosCovFraction instead."); }
			setMinPosCoverage(              value_minPosCoverage); 
		}
		vStr = stringHandler.getParameterSetting("minPosCovFraction");
		if (vStr != null) {
			double value_minPosCovFraction = Double.parseDouble(vStr);  if (value_minPosCovFraction > 1) { Utils.waitHere("minPosCovFraction should not be given numbers greater than 1."); }
			setMinPosCoverageAsFraction    (value_minPosCovFraction);
		}
		vStr = stringHandler.getParameterSetting("minPrecision");
		if (vStr != null) {                    setMinPrecision(  Double.parseDouble(vStr));  }
		vStr = stringHandler.getParameterSetting("mEstimatePos");
		if (vStr != null) {                    setMEstimatePos(  Double.parseDouble(vStr));  }
		vStr = stringHandler.getParameterSetting("mEstimateNeg");
		if (vStr != null) {                    setMEstimateNeg(  Double.parseDouble(vStr));  }
		vStr = stringHandler.getParameterSetting("maxNegCoverage");
		if (vStr != null) {                    setMaxNegCoverage( Double.parseDouble(vStr)); }
		vStr = stringHandler.getParameterSetting("fractionOfImplicitNegExamplesToKeep");
		if (vStr != null) {                       fractionOfImplicitNegExamplesToKeep = Double.parseDouble(vStr); }
		vStr = stringHandler.getParameterSetting("stopExpansionWhenAtThisNegCoverage");
		if (vStr != null) {                       stopExpansionWhenAtThisNegCoverage  = Double.parseDouble(vStr); }
		vStr = stringHandler.getParameterSetting("clausesMustCoverFractPosSeeds");
		if (vStr != null) {                       clausesMustCoverFractPosSeeds       = Double.parseDouble(vStr); }
		vStr = stringHandler.getParameterSetting("clausesMustNotCoverFractNegSeeds");
		if (vStr != null) {                       clausesMustNotCoverFractNegSeeds    = Double.parseDouble(vStr); }
		vStr = stringHandler.getParameterSetting("probOfDroppingChild");
		if (vStr != null) {                       probOfDroppingChild                 = Double.parseDouble(vStr); }
		vStr = stringHandler.getParameterSetting("minNumberOfNegExamples");
		if (vStr != null) {                       minNumberOfNegExamples          = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxBodyLength");
		if (vStr != null) {                       maxBodyLength                   = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxNumberOfNewVars");
		if (vStr != null) {                       maxNumberOfNewVars              = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxDepthOfNewVars");
		if (vStr != null) {                       maxDepthOfNewVars               = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxPredOccurrences");
		if (vStr != null) {                       maxPredOccurrences              = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxNodesToCreate");
		if (vStr != null) {                                     setMaxNodesToCreate(Integer.parseInt(vStr)); }
		vStr = stringHandler.getParameterSetting("maxResolutionsPerClauseEval");
		if (vStr != null) {                       maxResolutionsPerClauseEval     = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxSizeOfClosed");
		if (vStr != null) {                       maxSizeOfClosed                 = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("minChildrenBeforeRandomDropping");
		if (vStr != null) {                       minChildrenBeforeRandomDropping = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxConstantBindingsPerLiteral");
		if (vStr != null) {                       maxConstantBindingsPerLiteral   = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("beamWidthRRR");
		if (vStr != null) {                       beamWidthRRR                    = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("minBodyLengthRRR");
		if (vStr != null) {                       minBodyLengthRRR                = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxBodyLengthRRR");
		if (vStr != null) {                       maxBodyLengthRRR                = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("restartsRRR");
		if (vStr != null) {                       restartsRRR                     = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxNodesToConsiderRRR");
		if (vStr != null) {                       maxNodesToConsiderRRR           = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxNodesToCreateRRR");
		if (vStr != null) {                       maxNodesToCreateRRR             = Integer.parseInt(vStr); }
		
	}

	public final int num_hits = 0;
	public final int num_misses = 0;

	public void setMEstimateNeg(double mEstimateNeg) {
		if (mEstimateNeg < 0.0) Utils.error("The 'm' for neg examples covered needs to be a non-negative number.  You provided: " + mEstimateNeg);
		this.mEstimateNeg = mEstimateNeg;
	}
	double getMEstimateNeg() {
		return mEstimateNeg;
	}
	public void setMEstimatePos(double mEstimatePos) {
		if (mEstimatePos < 0.0) Utils.error("The 'm' for pos examples covered needs to be a non-negative number.  You provided: " + mEstimatePos);
		this.mEstimatePos = mEstimatePos;
	}
	double getMEstimatePos() {
		return mEstimatePos;
	}

	// Some accessor functions.
	public List<Example> getPosExamples() {
		return posExamples;
	}
	public List<Example> getNegExamples() {
	       return negExamples;
	}

	Iterable<Clause> getBackgroundKnowledge() {
        return context.getClausebase().getBackgroundKnowledge();
    }

	public HandleFOPCstrings getStringHandler() {
		return stringHandler;
	}
	public final HornClauseProver getProver() {
        if ( prover == null ) {
            prover = new HornClauseProver( context );
        }
		return prover;
	}

	private void initialize() throws SearchInterrupted {
		initialize(false);
	}
	public void initialize(boolean creatingConjunctiveFeaturesOnly) throws SearchInterrupted { // Make this a separate call so that caller can set some public variables if it wants to do so.
		if (!initialized) {
			long istart = System.currentTimeMillis();
            initialized = true;

            if (regressionTask) {
                stopIfPerfectClauseFound = false;
                // This causes the posExamplesThatFailedHere to be incomplete, if not set to false.
                stopWhenUnacceptableCoverage = false;
            }
            readExamples(posExamplesReader, negExamplesReader);
            if (posExamplesReader       != null) closeWithoutException(posExamplesReader);
			if (negExamplesReader       != null) closeWithoutException(negExamplesReader);
            checkForSetParameters();
			// Will be set to true when using this code to create features.
			savedBeamWidth = beamWidth;  // To be safe, grab this even if not doing RRR search.

            targetModes = new ArrayList<>(1);
            bodyModes   = new LinkedHashSet<>(Utils.getSizeSafely(stringHandler.getKnownModes()) - 1);
            for (PredicateNameAndArity pName : stringHandler.getKnownModes()) {
				// Note: we are not allowing recursion here since P is either a head or a body predicate.
				if (examplePredicates != null && examplePredicates.contains(pName)) {
                	targetModes.add(pName);
                }
                else bodyModes.add(pName);
            }

        ProcedurallyDefinedPredicateHandler procHandler   = new ILPprocedurallyDefinedPredicateHandler(this);
		procDefinedEnoughDiffMatches   = stringHandler.getPredicateName("differentlyBoundOutputVars");
		procDefinedForConstants        = stringHandler.getPredicateName("collectContantsBoundToTheseVars");
		procDefinedNeedForNewVariables = stringHandler.getPredicateName("newTermBoundByThisVariable");
        context.getClausebase().setUserProcedurallyDefinedPredicateHandler(procHandler);

		if (Utils.getSizeSafely(posExamples) + Utils.getSizeSafely(negExamples) > 0) { // Sometimes we just want to use the precompute facility.
			chooseTargetMode();
		}

		/* for each precompute file to output, precompute all the corresponding rules... */
		for (int i = 0; i < getParser().getNumberOfPrecomputeFiles(); i++) {
			// TODO(@hayesall): This appears to be where precomputes are handled.
			List<Sentence> precomputeThese = getParser().getSentencesToPrecompute(i); // Note that this is the set of ALL precompute's encountered during any file reading.
			if (Utils.getSizeSafely(precomputeThese) > 0) {
				String precomputeFileNameToUse = replaceWildCardsForPrecomputes(getParser().getFileNameForSentencesToPrecompute(i));
				//add working dir to all files
				Utils.ensureDirExists(precomputeFileNameToUse);
				// The method below will check if the precompute file already exists, and if so, will simply return.
				Utils.println("% Processing precompute file: " + precomputeFileNameToUse);
				File f = new File(precomputeFileNameToUse);
				Utils.println("Writing to file: " + f.getAbsolutePath());
				/* Actually do the precomputes, writing precompute facts out to file*/
				precomputer.processPrecomputeSpecifications(getContext().getClausebase(), precomputeThese, precomputeFileNameToUse);
				Utils.println("% Loading: " + precomputeFileNameToUse);
				addToFacts(precomputeFileNameToUse); // Load the precomputed file.
			}
		}

		// TODO(@hayesall): What is `prune.txt`?
		String pruneFileNameToUse = Utils.createFileNameString(getDirectoryName(), "prune.txt");

		// The method below will check if the prune file already exists, and if so, will simply return true.
		boolean pruneFileAlreadyExists = lookForPruneOpportunities(useCachedFiles, getParser(), pruneFileNameToUse);

		if (pruneFileAlreadyExists && useCachedFiles) {
			// Load the prune file, if it exists.
			addToFacts(pruneFileNameToUse);
		}

		Utils.println("\n% Started collecting constants");
		long start = System.currentTimeMillis();
		// The following will see if the old types file exists.
		if (collectTypedConstants) {
			String  typesFileNameToUse     = Utils.createFileNameString(getDirectoryName(), "types.txt");
			Boolean typesFileAlreadyExists = typeManager.collectTypedConstants(createCacheFiles, useCachedFiles, typesFileNameToUse, targets, targetArgSpecs, bodyModes, getPosExamples(), getNegExamples(), facts); // Look at all the examples and facts, and collect the typed constants in them wherever possible.
			if (typesFileAlreadyExists) {
				addToFacts(typesFileNameToUse); // Load the types file, if it exists.
			}
		}
		long end = System.currentTimeMillis();
		Utils.println("% Time to collect constants: " + Utils.convertMillisecondsToTimeSpan(end - start));

		if (stringHandler.needPruner) {
			this.pruner = (pruner == null ? new PruneILPsearchTree(this) : pruner);
		}
		else if (pruner != null) {
			Utils.warning("A pruner was supplied but not needed.");
			this.pruner = null;
		}
		if (!creatingConjunctiveFeaturesOnly && minNumberOfNegExamples > 0 && getNegExamples() == null) { Utils.severeWarning("Have ZERO negative examples!  Variable 'minNumberOfNegExamples' is currently set to " + minNumberOfNegExamples + "."); }
			Utils.println("\n% Read " + Utils.comma(getPosExamples()) + " pos examples and " + Utils.comma(getNegExamples()) + " neg examples.");

			processThresholds();

        facts = null; // Release the temporarily stored facts so we aren't wasting memory.
        long iend = System.currentTimeMillis();
        Utils.println("% Time to init learnOneClause: " + Utils.convertMillisecondsToTimeSpan(iend-istart));
        }
	}

    private boolean lookForPruneOpportunities(Boolean useCachedFiles, FileParser parser, String fileName) { // Be sure to do this AFTER any precomputing is done.
        // See if any 'prune' rules can be generated from this rule set.
        // For example, if 'p :- q, r' is the ONLY way to derive 'p,' then if 'p' in a clause body, no need to consider adding 'q' nor 'r.'

        //  Could simply redo this each time, since the calculation is simple, but this design allows the user to EDIT this file.
        File file = new CondorFile(fileName);
        StringBuilder parseThisString = new StringBuilder();
        if (useCachedFiles && file.exists()) {
            Utils.warning("\n% The automatic creation of 'prune:' commands has previously occurred.  If this is incorrect, delete:\n%   '" + file.getPath() + "'", 3);
            Utils.waitHere("\n% The automatic creation of 'prune:' commands has previously occurred.  If this is incorrect, delete:\n%   '" + file.getPath() + "'");
            return true;
        }
        try {
            CondorFileOutputStream outStream = null; // Don't create unless needed.
            PrintStream printStream = null;
            for (DefiniteClause definiteClause : getContext().getClausebase().getAssertions()) {
                if (definiteClause instanceof Clause) {
                    Clause clause = (Clause) definiteClause;

                    Literal clauseHead = clause.posLiterals.get(0);
                    PredicateName clauseHeadName = clauseHead.predicateName;

                    if (clauseHeadName.getTypeOnlyList(clauseHead.numberArgs()) == null) {
                        continue;
                    } // Need to have some mode.  NOTE: this means modes need to be read before this method is called.
                    Collection<Variable> boundVariables = clauseHead.collectFreeVariables(null);
                    boolean canPrune = (clause.negLiterals != null); // Should always be true, but need to test this anyway.

                    if (canPrune) { // If ANY fact has the matches the clause head, cannot prune since cannot be sure this clause was used to deduce the head.
                        canPrune = (matchingFactExists(getContext().getClausebase(), clauseHead) == null);
                    }

                    // See if there are any other ways clauseHead can be derived.  If so, set canPrune=false.
                    if (canPrune) {
                        canPrune = (matchingClauseHeadExists(getContext().getClausebase(), clauseHead, clause) == null);
                    }

                    // Can only prune predicates that are DETERMINED by the arguments in the clauseHead.  ALSO SEE Precompute.java
                    // Note: this code is 'safe' but it misses some opportunities.  E.g., if one has 'p(x) :- q(x,y)' AND THERE IS ONLY ONE POSSIBLE y FOR EACH x, then pruning is valid.  (Called "determinate literals" in ILP - TODO handle such cases.)
                    if (canPrune) {
                        for (Literal prunableLiteral : clause.negLiterals) {
                            if (prunableLiteral.predicateName.getTypeOnlyList(prunableLiteral.numberArgs()) != null && canPrune(prunableLiteral) && prunableLiteral.collectFreeVariables(boundVariables) == null) { // Could include 'if (!canPrune) then continue;' but this code should be fast enough.
                                if (useCachedFiles && outStream == null) {
                                    outStream = new CondorFileOutputStream(fileName);
                                    printStream = new PrintStream(outStream, false); // (Don't) Request auto-flush (can slow down code).
                                    printStream.println("////  This file contains inferred pruning that can be done during ILP (i.e., 'structure') search.");
                                    printStream.println("////  It can be hand edited by the knowledgeable user, but the file name should not be changed.");
                                    printStream.println("////  Note that the file 'precomputed.txt' - if it exists - might also contain some 'prune:' commands.");
                                    printStream.println("////  'Prune:' commands can also appear in BK and facts files, though including them in facts files isn't recommended.");
                                }
                                String newStringLine = "prune: " + prunableLiteral + ", " + clauseHead + ", warnIf(2)."; // Use '2' here, since if more than one rule, the inference is incorrect.
                                parseThisString.append(newStringLine).append("\n");
                                if (useCachedFiles) {
                                    printStream.println("\n" + newStringLine + " % From: " + clause.toString(Integer.MAX_VALUE) + "."); // TODO clean up so no need for this MAX_VALUE here.
                                }
                            }
                        }
                    }
                }
            }
        } catch (FileNotFoundException e) {
            Utils.reportStackTrace(e);
            Utils.error("Unable to successfully open this file for writing: '" + fileName + "'.  Error message: " + e.getMessage());
        }
        parser.readFOPCstream(parseThisString.toString());
        return false;
    }

    /* Returns whether a literal can be pruned.
     *
     * Filter some things we don't want to add to the list of prunable items.
     * Wouldn't hurt to include these, but might confuse/distract the user.
     */
    private boolean canPrune(Literal lit) {
        if (lit.predicateName == getStringHandler().standardPredicateNames.cutMarker) {
            return false;
        }
        if (lit.numberArgs() > 0) {
            for (Term term : lit.getArguments()) {
                if (term instanceof SentenceAsTerm) {
                    return false;
                }
            } // Cannot handle clauses in the parser.
        }
        return true;
    }

    /* Does an item in the fact base match (i.e., unify with) this query?
     * @return The matching fact, if one exists. Otherwise null.
     */
	private Literal matchingFactExists(HornClausebase clausebase, Literal query) {
		assert query != null;

        BindingList aBinding = new BindingList(); // Note: the unifier can change this.  But save on creating a new one for each fact.
        Iterable<Literal> factsToUse = clausebase.getPossibleMatchingFacts(query, null);

        if (factsToUse != null) {
            for (Literal fact : factsToUse) {
                aBinding.theta.clear(); // Revert to the empty binding list.
                if (Unifier.UNIFIER.unify(fact, query, aBinding) != null) {
                    return fact;
                }
            }
        }
        return null;
    }

    /*
     * Does this query unify with any known clause, other than the one to ignore?  (OK to set ignoreThisClause=null.)
     * @return The matching clause head if one exists, otherwise null.
     */
	private Clause matchingClauseHeadExists(HornClausebase clausebase, Literal query, Clause ignoreThisClause) {
        Iterable<Clause> candidates = clausebase.getPossibleMatchingBackgroundKnowledge(query, null);
        if (candidates == null) {
            return null;
        }
        return matchingClauseHeadExists(query, ignoreThisClause, candidates);
    }

    /*
     * Does this query unify with the head of any of these clauses, other than the one to ignore?  (OK to set ignoreThisClause=null.)
     * @return The matching clause head if one exists, otherwise null.
     */
	private Clause matchingClauseHeadExists(Literal query, Clause ignoreThisClause, Iterable<Clause> listOfClauses) {
        if (query == null) {
            Utils.error("Cannot have query=null here.");
        }
        if (listOfClauses == null) {
            return null;
        }

        BindingList aBinding = new BindingList(); // Note: the unifier can change this.
        for (Clause clause : listOfClauses) {
            if (!clause.isDefiniteClause()) {
                Utils.error("Call clauses passed to the method must be Horn.  You provided: '" + clause + "'.");
            }
            if (clause != ignoreThisClause) {
				aBinding.theta.clear();
				if (Unifier.UNIFIER.unify(clause.posLiterals.get(0), query, aBinding) != null) {
                    return clause;
                }
            }
        }
        return null;
    }
	
	private String replaceWildCardsForPrecomputes(String precomputeFileNameString) {
		if (precomputeFileNameString.charAt(0) == '@') { precomputeFileNameString = stringHandler.getParameterSetting(precomputeFileNameString.substring(1)); }

		assert precomputeFileNameString != null;
		String result = precomputeFileNameString.replace("PRECOMPUTE_VAR1", Utils.removeAnyOuterQuotes(stringHandler.precompute_assignmentToTempVar1));
		result        =                   result.replace("PRECOMPUTE_VAR2", Utils.removeAnyOuterQuotes(stringHandler.precompute_assignmentToTempVar2));
		result        =                   result.replace("PRECOMPUTE_VAR3", Utils.removeAnyOuterQuotes(stringHandler.precompute_assignmentToTempVar3));
		result         =                  result.replace("PRECOMP",         Utils.removeAnyOuterQuotes(stringHandler.PRECOMP)); // Note: this matches "PRECOMPUTE_VAR3"
		result         =                  result.replace("TASK",            Utils.removeAnyOuterQuotes(stringHandler.TASK));
		return Utils.replaceWildCards(result);
	}

    private void processThresholds() throws SearchInterrupted {

		/* Override to disable thresholding.
		 *
		 * If set to false, thresholding will be skipped.  This is particularly useful
		 * when we are only using the LearnOneClause to evaluate a learned theory.
		 */
		if (getThresholder() != null) {
            Collection<LiteralToThreshold> thresholdThese = getParser().getLiteralsToThreshold(); // Note that this is the set of ALL thresholds's encountered during any file reading.

            // We have to make sure that we don't try to threshold the actual target predicate
            if ( targets != null && thresholdThese != null) {
                for (Iterator<LiteralToThreshold> it = thresholdThese.iterator(); it.hasNext();) {
                    LiteralToThreshold literalToThreshold = it.next();
                    PredicateNameAndArity pnaa = literalToThreshold.getPredicateNameAndArity();
                    for (Literal literal : targets) {
                        if ( pnaa.equals(literal.getPredicateNameAndArity()) ) {
                            it.remove();
                            break;
                        }
                    }
                }
            }

            if (Utils.getSizeSafely(thresholdThese) > 0) {
            	// NOTE: currently this is all done in memory and the writing to a file is only a debugging aid.
            	// So no big deal if the file is corrupted due to two runs writing at the same time (though we should still fix this).
                String thresholdFileNameToUse = (Utils.doNotCreateDribbleFiles ? null : Utils.createFileNameString(getDirectoryName(), getPrefix() + "_thresholdsNEW" + Utils.defaultFileExtensionWithPeriod)); // TODO allow user to name 'thresholded' files (i.e., by a directive command).
                getThresholder().processThresholdRequests(thresholdFileNameToUse, thresholdThese); 
            }
        }
    }

	public void addBodyMode(PredicateNameAndArity pName) {
        bodyModes.add(pName);
        stringHandler.addKnownMode(pName);
    }

	private int countOfSearchesPerformedWithCurrentModes = 0;  // Trevor - if you wish to see getSearchParametersString, feel free to add some reportFirstNsearches variable.  Jude

    @Override
    public SearchResult performSearch() throws SearchInterrupted {

        SearchResult result = null;

        ILPSearchAction action = fireInnerLoopStarting(this);
 
        if ( action == ILPSearchAction.PERFORM_LOOP ) {

			// Limit number of reports.
            if (++countOfSearchesPerformedWithCurrentModes < 2) { Utils.print(getSearchParametersString()); }
			result = super.performSearch();

			fireInnerLoopFinished(this);
        }
        else if (action == ILPSearchAction.SKIP_ITERATION) {
            Utils.println("ILPSearchListener skipped inner-loop.");
        }
        else {
            Utils.println("ILPSearchListener terminated further inner-loop execution.");
            throw new SearchInterrupted("ILPSearchListener terminated further inner-loop execution.");
        }

        return result;
    }

    void performSearch(SingleClauseNode bestNodeFromPreviousSearch) throws SearchInterrupted {
        if (!initialized) { initialize(); }
        ((InitializeILPsearchSpace) initializer).setBestNodeFromPreviousSearch(bestNodeFromPreviousSearch);
		performSearch();
	}

    private String getSearchParametersString() {
        StringBuilder stringBuilder = new StringBuilder();
        stringBuilder.append("\n% LearnOneClause Parameters:\n");
        
        Set<String> theTargets = getModeStrings(targetModes);
        stringBuilder.append("%   Targets (").append(Utils.comma(theTargets)).append("):\n%    ");
        stringBuilder.append(Utils.toString(theTargets, ",\n%    "));
        stringBuilder.append("\n");

        Set<String> modes = getModeStrings(bodyModes);
        stringBuilder.append("%  Modes (").append(Utils.comma(modes)).append("):\n%    ");
        stringBuilder.append(Utils.toString(modes, ",\n%    "));

        stringBuilder.append("\n");
        return stringBuilder.toString();
    }

    private Set<String> getModeStrings(Collection<PredicateNameAndArity> modes) {

        Set<String> set = new LinkedHashSet<>();

        for (PredicateNameAndArity predicateName : modes) {

            List<PredicateSpec> types = predicateName.getPredicateName().getTypeList();
            for (PredicateSpec predicateSpec : types) {
                StringBuilder stringBuilder = new StringBuilder();
                stringBuilder.append(predicateName.getPredicateName().name).append("(");

                List<TypeSpec> typeSpecs = predicateSpec.getTypeSpecList();
                boolean first = true;
                for (TypeSpec typeSpec : typeSpecs) {
                    if (!first) {
                        stringBuilder.append(", ");
                    }

                    stringBuilder.append(typeSpec);
                    first = false;
                }
                stringBuilder.append(")");
                set.add(stringBuilder.toString());
            }
        }

        return set;
    }

    public Set<String> getAlchemyModeStrings(Collection<PredicateNameAndArity> pnameArities) {

        Set<String> set = new LinkedHashSet<>();

        for (PredicateNameAndArity predicateName : pnameArities) {

            List<PredicateSpec> types = predicateName.getPredicateSpecs();
            for (PredicateSpec predicateSpec : types) {
                StringBuilder stringBuilder = new StringBuilder();
                stringBuilder.append(predicateName.getPredicateName().name).append("(");

                List<TypeSpec> typeSpecs = predicateSpec.getTypeSpecList();
                boolean first = true;
                for (TypeSpec typeSpec : typeSpecs) {
                    if (!first) {
                        stringBuilder.append(", ");
                    }

                    stringBuilder.append(typeSpec.isaType.toString().toLowerCase());
                    first = false;
                }
                stringBuilder.append(")");
                set.add(stringBuilder.toString());
                break;
            }
        }

        return set;
    }

	void checkIfAcceptableClausePossible() throws IllegalArgumentException {
		checkMinPosCoverage();
		checkMinPrecision();
	}

    /* Sets the min weight of covered positive example for a clause to be valid.
     *
     * If 0 &gte minPosCoverage &gt 1, it is considered the fraction of positive
     * examples required.  If minPosCoverage &gte 1, it is used directly.
     *
     * Note, the actual value returned by getMinPosCoverage() is always the
     * computed value after the above conversion has been done.  Thus, getMinPosCoverage()
     * may return a different value than the one set via this method.
     *
     * @param minPosCoverage The minimum weighted positive values to cover, 0 &gte minPosCoverage &gte totalPosWeight.
     */
	public void setMinPosCoverage(double minPosCoverage) {
        // I left the "out of range" warnings here, but I moved
        // the logic for determining the actual value into getMinPosCoverage.
        // I did this so that if totalPosWeight is set or updated after
        // setMinPosCoverage is call, we still get same values (although we
        // might miss the warnings in that case). -Trevor

		// Actually, I moved the error checking up to checkMinPosCoverage().
        // It should have the same functionality as before...
        checkMinPosCoverage();

		this.minPosCoverage = minPosCoverage;
	}
	
	public void setMinPosCoverageAsFraction(double minPosCoverageAsFractionOfPosExamples) {
		if (posExamples == null) { Utils.error("Calling setMinPosCoverageAsFraction when posExamples == null."); } // Setting posExamples will set totalPosWeight.
		setMinPosCoverage(minPosCoverageAsFractionOfPosExamples * totalPosWeight);
	}

    /* Returns the minPosCoverage value.
     *
     * If minPosCoverage is between 0 and 1, it will be considered a fraction
     * of the total positives and the computed value will be returned.
     */
	double getMinPosCoverage() {
		double result = help_getMinPosCoverage();
		return Math.max(result, Double.MIN_VALUE); // Make sure we never allow zero.
	}
	private double help_getMinPosCoverage() {
        if ( minPosCoverage > totalPosWeight ) {
            return maxPossiblePrecision() * totalPosWeight;
        }
        else if ( minPosCoverage < 0) {
            return 0;
        }
        else return minPosCoverage;
	}

    /* Checks if the value of minPosCoverage is valid for this run.
     *
     * @return True if the value was valid, false otherwise.  If false, getMinPosCoverage() will probably
     * fix the value to a reasonable value anyway.
     */
	private void checkMinPosCoverage() {
		// TODO(@hayesall): This function prints warnings, but does not do anything.
        // Check the min pos coverage values...
		if (totalPosWeight > 0 && minPosCoverage > totalPosWeight) {  // Anything odd happen here if totalPosWeight < 1?
			Utils.warning("% Should not set minPosCoverage (" + Utils.truncate(minPosCoverage) + ") to more than the total weight on the positive examples (" + Utils.truncate(totalPosWeight) + ").  Will use the maximum possible value.");
		}
        else if (minPosCoverage < 0) {
			Utils.warning("% Should not set minPosCoverage (" + Utils.truncate(minPosCoverage) + ") to a negative value.");
		}
	}

    /* Sets the max weight of covered negative example for a clause to be valid.
     *
     * If 0 &gte maxNegCoverage &gt 1, it is considered the fraction of negative
     * examples required.  If maxNegCoverage &gte 1, it is used directly.
     *
     * Note, the actual value returned by getMaxNegCoverage() is always the
     * computed value after the above conversion has been done.  Thus, getMaxNegCoverage()
     * may return a different value than the one set via this method.
     *
     * @param maxNegCoverage The maximum weighted negative values to cover, 0 &gte minPosCoverage &gte totalPosWeight.
     */
	public void setMaxNegCoverage(double maxNegCoverage) {
        // I moved the logic for determining the actual value into getMaxNegCoverage.
        // I did this so that if totalNegWeight is set or updated after
        // setMinPosCoverage is call, we still get sane values (although we
        // might miss the warnings in that case). -Trevor
		this.maxNegCoverage = maxNegCoverage;

	}

    /* Returns the maximum negative coverage value.
     *
     * If maxNegCoverage is between 0 and 1, it will be considered a fraction
     * of the total negative and the computed value will be returned.
     */
	double getMaxNegCoverage() {
        if (maxNegCoverage > 0 && maxNegCoverage < 1 && totalNegWeight > 0) {
			return maxNegCoverage * totalNegWeight; // In this situation, interpret maxNegCoverage as a FRACTION.
		}
		return maxNegCoverage;
	}

	void setMinPrecision(double minPrecision) {
		checkMinPrecision();
		this.minPrecision = minPrecision;
	}

	double getMinPrecision() {
		return minPrecision;
	}


	void setMaxRecall(double maxRecall) {
		checkMaxRecall();
		this.maxRecall = maxRecall;
	}

	/* Checks the value of the minPrecision.
     *
     * @throws IllegalArgumentException Throws an IllegalArgumentException if the parameter is out of range.
     */
	private void checkMinPrecision() throws IllegalArgumentException {
        if (minPrecision < 0) {
        	minPrecision = 0.0;
        	Utils.warning("Should not set minPrecision (" + Utils.truncate(minPrecision) + ") to a negative value.  Will use 0.");
		}

		if (minPrecision > 1) {
			minPrecision = maxPossiblePrecision();
			Utils.warning("Should not set minPrecision (" + Utils.truncate(minPrecision) + ") to a value above 1.  Will use the maxPossiblePrecision().");
		}

		if (totalPosWeight > 0 && minPrecision > maxPossiblePrecision()) {
			minPrecision= maxPossiblePrecision();
			Utils.warning("Should not set minPrecision (" + Utils.truncate(minPrecision) + ") to a value above the max possible precision (" + maxPossiblePrecision() + ").  Will use this max value instead.");
		}
    }

    private void checkMaxRecall()  throws IllegalArgumentException {
        if (maxRecall <= 0.0) {
        	maxRecall = 0.000001;
        	Utils.warning("Should not set maxRecall (" + Utils.truncate(maxRecall) + ") to a non-positive value.  Using " + maxRecall);
		}
    }

	private double maxPossiblePrecision() {
		return totalPosWeight / (totalPosWeight +  getMEstimateNeg());
	}

	void performRRRsearch(SingleClauseNode bestNodeFromPreviousSearch) throws SearchInterrupted { //TODO: add some early-stopping criteria

		int hold_maxNodesToExpand = getMaxNodesToConsider(); // Save these so they can be restored.
		int hold_maxNodesToCreate = getMaxNodesToCreate();
		int hold_nodesExpanded    = 0;
		int hold_nodesCreated     = 0;

		performRRRsearch   = true;
		setMaxNodesToConsider(maxNodesToConsiderRRR); // Switch to the RRR-specific settings.
		setMaxNodesToCreate(maxNodesToCreateRRR);
		for (int i = 1; i <= restartsRRR; i++) {
			if (hold_nodesExpanded >= hold_maxNodesToExpand) {
				searchMonitor.searchEndedByMaxNodesConsidered(hold_nodesExpanded);
				break;
			}
			if (hold_nodesCreated    >= hold_maxNodesToCreate) {
				searchMonitor.searchReachedMaxNodesCreated(   hold_nodesCreated);
				break;
			}
			stillInRRRphase1  = true;
			thisBodyLengthRRR = minBodyLengthRRR + Utils.random1toN(maxBodyLengthRRR - minBodyLengthRRR);
			performSearch(bestNodeFromPreviousSearch);  // No need to do a open.clear() since performSearch() does that.
			hold_nodesExpanded += nodesConsidered;
			hold_nodesCreated  += nodesCreated;
		}
		nodesConsidered    = hold_nodesExpanded; // Set the search totals to count ALL the RRR iterations.
		nodesCreated       = hold_nodesCreated;
		setMaxNodesToConsider(hold_maxNodesToExpand); // Revert to the old settings for these.
		setMaxNodesToCreate(hold_maxNodesToCreate);
	}

	List<Example> collectPosExamplesCovered(SingleClauseNode node) throws SearchInterrupted {
		return collectExamplesCovered(getPosExamples(),node);
	}
	List<Example> collectNegExamplesCovered(SingleClauseNode node) throws SearchInterrupted {
		return collectExamplesCovered(getNegExamples(),node);
	}


	/* Attempts to prove a single example given clause <code>clause</code> and returns
    * the bindings if finds a proof.
    * If an error occurs, this method silently catches the error and returns
    * false.
    *
    * @param clause Clause to evaluate.
    * @param ex Example to prove.
    * @return binding list for head, if the example is true, null otherwise.
    */
   public BindingList proveExampleAndReturnBindingList(Clause clause, Example ex) {

       try {
           Literal head = clause.posLiterals.get(0);
           List<Literal> clauseBody = clause.negLiterals;
           BindingList bindingList = unifier.unify(head, ex);

           if (bindingList == null) {
           		Utils.println("% proveExampleAndReturnBindingList: " + head + ":" + ex + ":" + clause);
           		Utils.error("%%%%%%%%%%%%%%%%% COULDNT FIND BINDING %%%%%%%%%%%%");
           		return null;
           }
           else if (clauseBody == null) {
           		Utils.error("%%%%%%%%%%%%%%%%% EMPTY BODY %%%%%%%%%%%%");
               return null;
           }
           else {
               List<Literal> query = bindingList.applyTheta(clauseBody);
			   return proveAndReturnBindings(query);
           }
       } catch (SearchInterrupted ignored) {
       }
       return null;
   }
    /* Attempts to prove a single example given clause <code>clause</code>.
     *
     * If an error occurs, this method silently catches the error and returns
     * false.
     *
     * @param clause Clause to evaluate.
     * @param ex Example to prove.
     * @return True if the example is true, false otherwise.
     */
	boolean proveExample(Clause clause, Example ex) {

        try {
            Literal head = clause.posLiterals.get(0);
            List<Literal> clauseBody = clause.negLiterals;
            BindingList bindingList = unifier.unify(head, ex);

            if (bindingList == null) {
            	Utils.println("%%%%%% NO BINDINGS %%%%%% for clause head (" + head.numberArgs() + " [head] vs. " + ex.numberArgs() + " [example] args)\n  '" + head + "'\n and example\n  '" + ex + "'.");
                return false;
            }
            else if (clauseBody == null) {
                return true;
            }
            else {

                if ( prover.getTraceLevel() == 0 && prover.getSpyEntries().includeElement(head.predicateName, head.numberArgs())) {
                    Utils.println("Spy point encountered on " + head.predicateName + "/" + head.numberArgs() + ".  Enabling tracing.");
                    prover.setTraceLevel(1);
                }
                List<Literal> query = bindingList.applyTheta(clauseBody);
				return prove(query);
			}
        } catch (SearchInterrupted ignored) {
        }
        return false;
    }

	/*
	 * If fewer than minWgtedCoverage or more than maxWgtedCoverage, can
	 * stop and return null since this node is unacceptable.
	 */
	private List<Example> collectExamplesCovered(List<Example> examples, SingleClauseNode node) throws SearchInterrupted {
		if (examples == null) { return null; }
		List<Example> results    = null;
		List<Literal> clauseBody = node.getClauseBody();
		Literal       target     = node.getTarget();
		for (Example ex : examples) {
			if (node.proveExample(this, target, clauseBody, ex, bindings)) { // AT LEAST LOOK AT THE EX'S ALREADY CANCELED.
				if (results == null) { results = new ArrayList<>(32); }
				results.add(ex);
			}
		}
		return results;
	}

	// Allow the user to choose which seeds (eg, might want to use Condor and let the Condor run # deterministically indicate which seed(s) to select.
	void selectTheseSeedsByIndex(int[] posSeedIndices, Set<Example> seedPosExamplesUsed, Set<Example> seedNegExamplesUsed) {
		selectTheseSeedsByIndex(posSeedIndices, null, true, seedPosExamplesUsed, seedNegExamplesUsed);
	}
	void selectTheseSeedsByIndex(int[] posSeedIndices, int[] negSeedIndices, boolean complainIfPreviouslyUsed, Set<Example> seedPosExamplesUsed, Set<Example> seedNegExamplesUsed) {
		int numberOfPosEx = Utils.getSizeSafely(getPosExamples());
		int numberOfNegEx = Utils.getSizeSafely(getNegExamples());

      if ( seedPosExamplesUsed == null || seedNegExamplesUsed == null ) {
           throw new NullPointerException("seedPosExamplesUsed and seedNegExamplesUsed must be non-null.");
       }

		if (allowPosSeedsToBeReselected ) {
			seedPosExamplesUsed.clear();
		}
		if (allowNegSeedsToBeReselected ) {
			seedNegExamplesUsed.clear();
		}
		if (posSeedIndices != null && posSeedIndices.length > 0) {
			seedPosExamples = new ArrayList<>(posSeedIndices.length);
			for (int index : posSeedIndices) {
				if (index < 0 || index >= numberOfPosEx) { Utils.error("Pos seed index " + index + " must be in [0," + (numberOfPosEx - 1) + "]"); }
				Example chosenExample = getPosExamples().get(index);

            // TAW: There seems to be a little logic problem here.
            // It seems like allowPosSeedsToBeReselected and complainIfPreviouslyUsed do the same thing.
				if (complainIfPreviouslyUsed && seedPosExamplesUsed.contains(chosenExample)) {
					Utils.error("Pos seed #" + index + " has already been used.");
				}
				    seedPosExamplesUsed.add(chosenExample);
				seedPosExamples.add(    chosenExample);
			}
		}
		if (negSeedIndices != null && negSeedIndices.length > 0) {
			seedNegExamples = new ArrayList<>(negSeedIndices.length);
			for (int index : negSeedIndices) {
				if (index < 0 || index >= numberOfNegEx) { Utils.error("Neg seed index " + index + " must be in [0," + (numberOfNegEx - 1) + "]"); }
				Example chosenExample = getNegExamples().get(index);

				if (complainIfPreviouslyUsed && seedNegExamplesUsed.contains(chosenExample)) {
					Utils.error("Neg seed #" + index + " has already been used.");
				}
				    seedNegExamplesUsed.add(chosenExample);
				seedNegExamples.add(    chosenExample);
			}
		}
		setSeedWgtedCounts();
	}


	private void setSeedWgtedCounts() {
		totalWeightOnPosSeeds = Example.getWeightOfExamples(seedPosExamples);
		totalWeightOnNegSeeds = Example.getWeightOfExamples(seedNegExamples);
	}

	private BindingList proveAndReturnBindings(List<Literal> negatedConjunctiveQuery) throws SearchInterrupted {
		if (negatedConjunctiveQuery == null) {
			Utils.error("Called for null query");
			return new BindingList();
		} // The empty list is really a body that equals the built-in predicate 'true()'.
		return getProver().proveConjunctiveQueryAndReturnBindings(negatedConjunctiveQuery);
	}

	boolean prove(List<Literal> negatedConjunctiveQuery) throws SearchInterrupted {
		if (negatedConjunctiveQuery == null) { return true; } // The empty list is really a body that equals the built-in predicate 'true()'.
		return getProver().proveConjunctiveQuery(negatedConjunctiveQuery);
	}

	private int warningCountAboutExamples = 0;

	public boolean confirmExample(Literal lit) {
		// TODO(@hayesall): This method always returns `true`, but also prints warnings.
		//		The `VARIABLEs in examples` warning could be good to have, but might be better treated as an error.

		int litSize = lit.numberArgs();
        PredicateNameAndArity pnaa = lit.getPredicateNameAndArity();

		if (litSize > 0 && Utils.getSizeSafely(lit.collectAllVariables()) > 0) {  // TODO - could just like to see if any variables and same some cpu cycles and memory.
			Utils.severeWarning("Do you really want to have VARIABLEs in examples?  If so, WILL code needs updating (e.g, in terms of counting coverage, etc.)\n " + lit);
		}

		if (examplePredicates == null) {
			examplePredicates          = new ArrayList<>(1);
			examplePredicateSignatures = new ArrayList<>(1);
		}

		if (allowMultipleTargets || examplePredicates.isEmpty()) {
			if (!matchesExistingTargetSpec(lit)) {
				examplePredicates.add(pnaa);
				examplePredicateSignatures.add(stringHandler.getSignature(lit.getArguments()));
			}
		}
		else if (!examplePredicates.contains(pnaa) && warningCountAboutExamples++ < 10) {
			Utils.severeWarning("AllowMultipleTargets = false and example '" + lit + "' does not have the predicate name of the other examples: " + examplePredicates +".");
		}
		return true;
	}

	private boolean matchesExistingTargetSpec(Literal lit) {
		if (examplePredicates == null) { Utils.error("matchesExistingTargetSpec: examplePredicates = null"); }
		for (int i = 0; i < examplePredicates.size(); i++) {
			if (examplePredicates.get(i).equals(lit.getPredicateNameAndArity()) && 
				matchingSignatures(examplePredicateSignatures.get(i), stringHandler.getSignature(lit.getArguments()))) { return true; }
		}
		return false;
	}

	private boolean matchingSignatures(List<Term> terms1, List<Term> terms2) {
		if (terms1 == terms2)                 { return true;  }
		if (terms1 == null || terms2 == null) { return false; }
		if (terms1.size() != terms2.size())   { return false; }
		for (int i = 0; i < terms1.size(); i++) {
			if (terms1.get(i) != terms2.get(i)) { // If not a direct match, then must be matching functions.
				if (terms1.get(i) instanceof Function && terms2.get(i) instanceof Function) {
					if (!matchingSignatures(((Function) terms1.get(i)).getArguments(),
											((Function) terms2.get(i)).getArguments())) {
						return false;
					}
				} else { return false; }
			}
		}
		return true;
	}

	private PredicateName annotationPredName        = null;
	private PredicateName regressionExamplePredName = null;

	private List<Example> readExamples(Reader examplesReader, String readerDirectoryName) {
		if (examplesReader == null) {
			Utils.error("Have no examples reader!");
			return null;
		}
		List<Sentence> sentences;
		sentences = getParser().readFOPCreader(examplesReader, readerDirectoryName);

		if (sentences == null) { return null; }
		List<Example> result = new ArrayList<>(Utils.getSizeSafely(sentences));

		if (annotationPredName        == null) { annotationPredName        = stringHandler.getPredicateName("annotatedExample"); }
		if (regressionExamplePredName == null) { regressionExamplePredName = stringHandler.getPredicateName("regressionExample"); }
		for (Sentence s : sentences) {
			if        (s instanceof Literal) {
				Literal lit = (Literal) s;
				Example ex = processReadExample(lit);
				if (ex != null) { result.add(ex); }
			} else if (s instanceof UniversalSentence) { // Can drop the ForAll since the clausal-form converter converts all variables to universals.
				Sentence body = ((UniversalSentence) s).body;

				// Having an Example class leads to some extra copying of literals, but seems worth having clean classes (e.g., to catch errors),
				if (body instanceof Literal) {
					Literal lit = (Literal) body;
					Example ex = processReadExample(lit);
					if (ex != null) { result.add(ex); }
				} else { Utils.error("Illegal form of an example: '" + s + "' - should be a single (unnegated) fact."); }
			} else     { Utils.error("Illegal form of an example: '" + s + "' - should be a single (unnegated) fact."); }
		}
		Utils.println("% Have read " + Utils.comma(result) + " examples from '" + readerDirectoryName + "' [" + getDirectoryName() + "/" + getPrefix() + "*].");
		return result;
	}

	// Note: for regression examples, here is how things are determined:
	//    predicate(args)   <-- uses the weight on this literal as the output (see FileParser.java) and resets weight to the default value.
	//    regressionExample(pred(args), outputValue)   <-- uses the 2nd argument
	//    annotatedPredicate(regressionExample(pred(args), outputValue), annotation)   <-- uses outputValue
	private Example processReadExample(Literal lit) {
		if (lit.predicateName.name.equals(annotationPredName.name)) { // See if this is annotation of an example.
			if (lit.numberArgs() != 2) { Utils.error("Expecting exactly two arguments here: " + lit); }
			Term arg0 = lit.getArgument(0);
			if (arg0 instanceof Function) {
				Function f = (Function) arg0;
				Literal internalLit = (f).convertToLiteral(stringHandler);
				return createExample(internalLit);
			}
			Utils.error("Should get a literal posing as a function here, but got: " + arg0);
		} else { return createExample(lit); } // Grab the outer weight.
		return null;
	}

	private Example createExample(Literal lit) {
		if (regressionTask) {
			double outputValue = lit.getWeightOnSentence();
			if (lit.predicateName.name.equals(regressionExamplePredName.name)) {
				if (lit.numberArgs() != 2 && lit.numberArgs() != 3) { Utils.error("Expecting either two or three arguments here: " + lit); }
				Term    arg0        = lit.getArgument(0);
				Literal internalLit = null;
				StringConstant   sc = null;
				if (arg0 instanceof Function) {
					Function f = (Function) arg0;
					internalLit = f.convertToLiteral(stringHandler);
				} else { Utils.error("Should get a literal posing as a function here, but got: " + arg0); }
				Term arg1 = lit.getArgument(1);
				if (arg1 instanceof NumericConstant) {
					NumericConstant nc = (NumericConstant) arg1;
					outputValue = nc.value.doubleValue();
				} else { Utils.error("Should get a number here, but got: " + arg1); }
				if (lit.numberArgs() > 2) {
					Term arg2 = lit.getArgument(2);
					if (arg2 instanceof StringConstant) {
						sc = (StringConstant) arg2;
					} else { Utils.error("Should get a string here, but got: " + arg2); }
				}
				assert internalLit != null;
				if (!confirmExample(internalLit)) { return null; }
				return new RegressionExample(stringHandler, internalLit, outputValue, "Read from file.", combineLabels(sc == null ? null : sc.getName()));
			}
			lit.setWeightOnSentence(1.0);
			if (!confirmExample(lit)) { return null; }
			return new RegressionExample(stringHandler, lit, outputValue, "Read from file.", null);
		}
		if (!confirmExample(lit)) { return null; }
		return new Example(stringHandler, lit, "Read from file.", null);
	}

	private String combineLabels(String str2) {
		return str2;
	}
	
	private Theory readBackgroundTheory(Reader bkReader) {
		if (bkReader == null) { return null; }
		List<Sentence> sentences;
		// TODO(@hayesall): Always returns null?
		Utils.println("% Reading background theory from dir: " + null);
		sentences = getParser().readFOPCreader(bkReader, null);
		if (sentences == null) { return null; } // It is possible there are no inference rules, though some modes should have been read.
		return new Theory(stringHandler, sentences);
	}

	private List<Sentence> readFacts(Reader factsReader, String readerDirectoryName) {
		return readFacts(factsReader, readerDirectoryName, false);
	}
	private List<Sentence> readFacts(Reader factsReader, String readerDirectoryName, boolean okIfNoFacts) {
		if (factsReader == null && okIfNoFacts) { return null; }
		List<Sentence> sentences;
		sentences = getParser().readFOPCreader(factsReader, readerDirectoryName);
		return sentences;
	}

	private void addToFacts(String factsFileName) {
		// TODO(@hayesall): Drop support for `.gz` files.
		try {
			boolean isCompressed = false;
			if (!Utils.fileExists(factsFileName)) {
				if (Utils.fileExists(factsFileName + ".gz")) {
					factsFileName += ".gz";
					isCompressed = true;
				} else {
					Utils.error("Cannot find this file (nor its GZIPPED version):\n  " + factsFileName);
				}
			}
			File factsFile = Utils.ensureDirExists(factsFileName);
			addToFacts(isCompressed ? new CondorFileReader(factsFileName) : new CondorFileReader(factsFile), factsFile.getParent()); // Need the String in CondorFileReader since that will check if compressed.
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Cannot find this file: " + factsFileName);
		}
	}

	private void addToFacts(Reader factsReader, String readerDirectory) {
		List<Sentence> moreFacts = readFacts(factsReader, readerDirectory, true);
		if (moreFacts == null) { return; }
		Utils.println("% Read an additional " + Utils.comma(moreFacts) + " facts from " + factsReader + ".");
		addFacts(moreFacts);
	}

	void addFacts(List<Sentence> newFacts) {
		context.assertSentences(newFacts);
	}

	void addRule(Clause rule) {
		context.assertDefiniteClause(rule);
	}

	private void chooseTargetMode() {
		chooseTargetMode(stringHandler.dontComplainIfMoreThanOneTargetModes);
		
	}

	public void chooseTargetMode(boolean dontComplainForMoreThanOneModes) {

		if (Utils.getSizeSafely(examplePredicates) < 1) {
			Utils.severeWarning("Need to have a target predicate here.");
			return;
		}
		for (PredicateNameAndArity targetPred : examplePredicates) {
			int numberOfTargetModes = Utils.getSizeSafely(targetPred.getPredicateName().getTypeList());

			if (numberOfTargetModes <= 0) {
				Utils.severeWarning("No target modes were provided for '" + targetPred + "'.");
				continue;
			}
			List<PredicateSpec> predSpecs = targetPred.getPredicateName().getTypeList();

			if (Utils.getSizeSafely(predSpecs) != 1) {
				if (!(Utils.getSizeSafely(predSpecs) > 1 && dontComplainForMoreThanOneModes)) {
					Utils.error("Should only have ONE predicate spec, but have:\n " + predSpecs);
				}
			} // TODO - what if more than 1????

			if (targets == null) {
				targets = new ArrayList<>(1);
				targetArgSpecs = new ArrayList<>(1);
				variablesInTargets = new ArrayList<>(1);
			}

			addToTargetModes(targetPred);
		}
	}

	private void addToTargetModes(PredicateNameAndArity targetPred) {

	    PredicateSpec targetArgTypes = targetPred.getPredicateName().getTypeList().get(0);

	    // The signature records the structure of the literal, including functions with arbitrary embedding.
	    // The typeSpec simply records in a list the types of the 'leaves' in the parser of the literal.
		// This is a little kludgy, but that is because it grew out of a much simpler design.
	    List<Term>     targetArguments     = new ArrayList<>(   Utils.getSizeSafely(targetArgTypes.getSignature()));
	    List<ArgSpec>  theseTargetArgSpecs = new ArrayList<>(Utils.getSizeSafely(targetArgTypes.getTypeSpecList()));
	    List<Term>     theseVars           = new ArrayList<>(   Utils.getSizeSafely(targetArgTypes.getTypeSpecList()));
	    traverseSignatureAndAddVariables(targetArgTypes.getSignature(), 0, targetArgTypes.getTypeSpecList(), targetArguments, theseVars, theseTargetArgSpecs);

	    Literal newTarget = stringHandler.getLiteral(targetPred.getPredicateName(), targetArguments);
		checkExamplesToSeeIfTargetArgSpecsShouldBeConstrained(newTarget, theseTargetArgSpecs);

        boolean targetExists = getTargetAlreadyExists(newTarget, theseTargetArgSpecs);
        if (!targetExists) {
            targets.add(newTarget);
            targetArgSpecs.add(theseTargetArgSpecs);
            variablesInTargets.add(theseVars);

			Utils.println("\n% NEW target:                 " + newTarget);
			Utils.println(  "%  targetPred:                " + targetPred);
			Utils.println(  "%  targetArgTypes:            " + targetArgTypes);
			Utils.println(  "%  targets:                   " + targets);
			Utils.println(  "%  targetPredicates:          " + examplePredicates);
			Utils.println(  "%  targetArgSpecs:            " + targetArgSpecs);
			Utils.println(  "%  variablesInTargets:        " + variablesInTargets);

		}
        else  {
        	Utils.println("\n% Target variant already exists.  Skipping target:                 " + newTarget + ".");
        	Utils.println(  "%  targetArgTypes:            " + targetArgTypes);
        	Utils.println(  "%  targetArgSpecs:            " + targetArgSpecs);
        }
	}
	
    private ArgSpec lookupInArgSpecList(List<ArgSpec> specs, Term term) {
        for (ArgSpec argSpec : specs) {
            if ( argSpec.arg == term ) {
                return argSpec;
            }
        }
        return null;
    }

    private boolean getTargetAlreadyExists(Literal newTarget, List<ArgSpec> theseTargetArgSpecs) {

        boolean found = false;

        for (int j = 0; j < Utils.getSizeSafely(targets); j++) {

            Literal existingTarget = targets.get(j);
            List<ArgSpec> existingArgSpecs = targetArgSpecs.get(j);
            List<Term> existingVariables = variablesInTargets.get(j);

            BindingList bl = new BindingList();

            if (existingTarget.variants(newTarget, bl) != null) {

                for (Term term : existingVariables) {

                    if (term instanceof Variable) {
                        Variable existingVar = (Variable) term;

                        Term matchedTerm = bl.getMapping(existingVar);

                        if (matchedTerm instanceof Variable) {
                            Variable newVariable = (Variable) matchedTerm;

                            ArgSpec existingArgSpec = lookupInArgSpecList(existingArgSpecs, existingVar);
                            ArgSpec newArgSpec = lookupInArgSpecList(theseTargetArgSpecs, newVariable);

                            if (existingArgSpec != null && newArgSpec != null && existingArgSpec.typeSpec.equals(newArgSpec.typeSpec)) {
                                found = true;
                                break;
                            }
                        }
                    }
                }
            }
        }

        return found;
    }


	// There is no need for a target argument to be more general than ALL the examples' corresponding arguments.
	private void checkExamplesToSeeIfTargetArgSpecsShouldBeConstrained(Literal target, List<ArgSpec> theseTargetArgSpecs) {
		if (Utils.getSizeSafely(theseTargetArgSpecs) < 1 || target == null) { return; }
		List<Example> posEx = getPosExamples();
		List<Example> negEx = getNegExamples();

		if (posEx == null && negEx == null) { Utils.waitHere("Have no examples yet!"); }

		int targetPredicateArity = target.numberArgs();
		for (int i = 0; i < target.numberArgs(); i++) {
			ArgSpec  aSpec = theseTargetArgSpecs.get(i);
			TypeSpec tSpec = aSpec.typeSpec;
			Type     type  = tSpec.isaType;
			Type typeToUse = null;
			boolean skipWithThisArgument = false;

			if (posEx != null) for (Example ex : posEx) {
				if (ex.numberArgs() != targetPredicateArity || ex.predicateName != target.predicateName) { continue; }

				Term argI = ex.getArgument(i);
				List<Type> types = stringHandler.isaHandler.getAllKnownTypesForThisTerm(argI);

				if (types == null)     { skipWithThisArgument = true; typeToUse = null; break; }
				if (types.size() != 1) { skipWithThisArgument = true; typeToUse = null; break; } // Not sure what to do with multiple types.
				if (typeToUse == null) { typeToUse = types.get(0); }
				else {
					Type newType = types.get(0);
					if       (stringHandler.isaHandler.isa(typeToUse, newType)) { typeToUse = newType; } // Keep the more general type.
					else if (!stringHandler.isaHandler.isa(newType, typeToUse)) {
						skipWithThisArgument = true; typeToUse = null; break; // Could not compare types.
					}
				}
			}
			if (negEx != null) for (Example ex : negEx) {
				if (skipWithThisArgument || ex.numberArgs() != targetPredicateArity || ex.predicateName != target.predicateName) { continue; }
				Term argI = ex.getArgument(i);
				List<Type> types = stringHandler.isaHandler.getAllKnownTypesForThisTerm(argI);

				if (types == null)     { skipWithThisArgument = true; typeToUse = null; break; }
				if (types.size() != 1) { skipWithThisArgument = true; typeToUse = null; break; } // Not sure what to do with multiple types.
				if (typeToUse == null) { typeToUse = types.get(0); }
				else {
					Type newType = types.get(0);
					if       (stringHandler.isaHandler.isa(typeToUse, newType)) { typeToUse = newType; } // Keep the more general type.
					else if (!stringHandler.isaHandler.isa(newType, typeToUse)) {
						skipWithThisArgument = true; typeToUse = null; break; // Could not compare types.
					}
				}
			}
			if (!skipWithThisArgument && typeToUse != type && stringHandler.isaHandler.isa(typeToUse, type)) {
				// If reached here, all the arguments in the examples are know to be more constrained than the target predicate,
				// so let's constrain the target.  TODO - should we add 'guard literals' to the learned concept?
				Utils.waitHere("Changing the type of argument #" + i + " from '" + type + "' to the more retrictive '" + typeToUse + "' because all the training examples are of this latter type.");
				tSpec.isaType = typeToUse; // NOTE: this is a destructive change, so hopefully the caller is not impacted by this ...
			}
		}
	}

	private void traverseSignatureAndAddVariables(List<Term> signature, int counter, List<TypeSpec> typeSpecs, List<Term> targetArguments, List<Term> theseVars, List<ArgSpec> theseTargetArgSpecs) {
		if (signature == null) { return; }
		for (Term arg : signature) {
			if (arg instanceof Constant) {
				int positionToFill = Utils.getSizeSafely(theseTargetArgSpecs);
				if (positionToFill != counter) { Utils.error("positionToFill = " + positionToFill + " != counter = " + counter); }
				TypeSpec typeSpec = typeSpecs.get(positionToFill);
				Term newTerm;
				if (typeSpec.mustBeThisValue()) {
					newTerm = stringHandler.getStringConstant(typeSpec.isaType.toString());
				} else {
					newTerm = stringHandler.getNewNamedGeneratedVariable();
				}
				theseTargetArgSpecs.add(new ArgSpec(newTerm, typeSpec));
				targetArguments.add(newTerm);
				theseVars.add(newTerm);
				counter++;
    		} else if (Function.isaConsCell(arg)) {
    			counter++; // We need to skip lists, since they can be of variable length.
			} else if (arg instanceof Function) {
				Function f = (Function) arg;
				List<Term> newArguments = new ArrayList<>(f.numberArgs());
				traverseSignatureAndAddVariables(f.getArguments(), counter, typeSpecs, newArguments, theseVars, theseTargetArgSpecs);
				targetArguments.add(stringHandler.getFunction(f.functionName, newArguments, f.getTypeSpec()));
				counter += f.countLeaves();
			} else { Utils.error("Unexpected argument in a signature: " + arg); }
		}
	}

	// This method helps select constants to fill arguments of type # during ILP search.
	void collectConstantBindings(List<Term> args) {
		if (collectedConstantBindings == null) { collectedConstantBindings = new ArrayList<>(8); }
		if (Utils.getSizeSafely(collectedConstantBindings) >= 1000) { return; } // In case there are a huge number of constants, limit to 1000.  Ideally would collect a random set, but that doesn't seem worth the effort.
		int len1 = Utils.getSizeSafely(args);
		for (List<Term> entry : collectedConstantBindings) {
			if (len1 != Utils.getSizeSafely(entry)) { continue; } // Should be the same size, but check anyway.
			boolean foundDifference = false;
			for (ListIterator<Term> terms1 = args.listIterator(), terms2 = entry.listIterator(); terms1.hasNext(); ) {
				Term term1 = terms1.next();
				Term term2 = terms2.next();

				if (!term1.equals(term2)) { foundDifference = true; break; }
			}
			if (!foundDifference) { return; } // Have found a matching list, so this is a duplicate and can be ignored.

		}
		collectedConstantBindings.add(args); // Should check for duplicates!
	}

	private void setDirectoryName(String dir) {
		getParser().setDirectoryName(dir);
	}
	private String getDirectoryName() {
		return getParser().getDirectoryName();
	}

	private void setPrefix(String prefix) {
		getParser().setPrefix(prefix);
	}
	private String getPrefix() {
		return getParser().getPrefix();
	}

    void setPosExamples(List<Example> posExamples) {
        this.posExamples = posExamples;
        
        if (this.posExamples == null) { this.posExamples = new ArrayList<>(0); } // Use an empty list (rather than null) so we know this has been called.

        // We should probably count the weights and stuff here...
        totalPosWeight = Example.getWeightOfExamples(posExamples);
    }

    void setNegExamples(List<Example> negExamples) {
        this.negExamples = negExamples;

        // We should probably count the weights and stuff here...
        totalNegWeight = Example.getWeightOfExamples(negExamples);
    }

    int getNumberOfPosExamples() {
        return posExamples == null ? 0 : posExamples.size();
    }

    int getNumberOfNegExamples() {
        return negExamples == null ? 0 : negExamples.size();
    }

	private void setThresholder(ThresholdManager thresholder) {
		this.thresholdHandler = thresholder;
	}

	private ThresholdManager getThresholder() {
		return thresholdHandler;
	}

	private void setInlineManager(InlineManager inliner) {
		this.inlineHandler = inliner;
	}

	InlineManager getInlineManager() {
		return inlineHandler;
	}

	List<List<Literal>> getOptimizedClauseBodies(Literal target, List<Literal> clauseBody) {
		return stringHandler.getClauseOptimizer().bodyToBodies(target, clauseBody);
	}

    public HornClauseContext getContext() {
        return context;
    }

	double getTotalPosWeight() {
		return totalPosWeight;
	}

	double getTotalNegWeight() {
		return totalNegWeight;
	}

	boolean isaTreeStructuredTask() {
		return isaTreeStructuredTask;
	}

	void  setIsaTreeStructuredTask(boolean value) {
		isaTreeStructuredTask = value;
	}

	List<ModeConstraint> getModeConstraints() {
		// TODO(@hayesall): Always returns an empty list.
		return Collections.emptyList();
	}



    private List<Literal>        backup_targets                   = null; // These are the actual targets determined from the examplePredicates.
	private List<List<ArgSpec>>  backup_targetArgSpecs            = null; // The info about the target argument being used and the variables matched with their types.
	private List<List<Term>>     backup_variablesInTargets        = null; // These are really 'arguments' since it is possible a mode specifies a constant be used.

	public void setTargetAs(String target, boolean dontAddOtherTargetModes, String addPrefix) {
		// Check if we have already backed up the literals.
		if (backup_targets == null) {
			backup_targets            = targets;
			backup_targetArgSpecs     = targetArgSpecs;
			backup_variablesInTargets = variablesInTargets;
		}
		int selectedTarget = -1;
		for (int i = 0; i < Utils.getSizeSafely(backup_targets); i++) {
			PredicateNameAndArity predName = backup_targets.get(i).getPredicateNameAndArity();
			if (predName.getPredicateName().name.equals(target)) {
				bodyModes.remove(predName);
				if (addPrefix != null) {
					if (!targetModes.contains(predName)) { targetModes.add(predName); }
				}
				selectedTarget = i;
			} else {
				if (dontAddOtherTargetModes) {
					bodyModes.remove(predName);
				} else {
					if (!bodyModes.contains(predName)) { bodyModes.add(backup_targets.get(i).getPredicateNameAndArity()); }
				}
			}
		}
		targets            = new ArrayList<>();
		targetArgSpecs     = new ArrayList<>();
		variablesInTargets = new ArrayList<>();
		
		if (addPrefix != null) {
			// TODO(?): Unknown
			String multiPred = addPrefix + target;
			for (PredicateNameAndArity pnaa : bodyModes) {
				if (pnaa.getPredicateName().name.equals(multiPred)) {
					addToTargetModes(pnaa);
					break;
				}
			}
		} else {
			if (selectedTarget == -1) {
				Utils.error("Didn't find target '" + target + "' in: " + backup_targets);
			}

			targets.add(           backup_targets.get(           selectedTarget));
			targetArgSpecs.add(    backup_targetArgSpecs.get(    selectedTarget));
			variablesInTargets.add(backup_variablesInTargets.get(selectedTarget));
		}
	}

	public List<PredicateNameAndArity> getTargetModes() {
		return targetModes;
	}

	public Set<PredicateNameAndArity> getBodyModes() {
		return bodyModes;
	}

	void setBodyModes(Set<PredicateNameAndArity> bodyModes) {
		this.bodyModes = bodyModes;
		countOfSearchesPerformedWithCurrentModes = 0; 
	}

	public List<List<ArgSpec>> getTargetArgSpecs() {
		return targetArgSpecs;
	}

	public List<List<Term>> getExamplePredicateSignatures() {
		return examplePredicateSignatures;
	}

	void resetAll() {
		resetAllForReal();
		if (seedPosExamples != null) { seedPosExamples.clear(); }
		if (seedNegExamples != null) { seedNegExamples.clear(); }
		if (collectedConstantBindings != null) { collectedConstantBindings.clear(); }
	}

    public FileParser getParser() {
        return parser;
    }

	public List<Literal> getTargets() {
		return targets;
}

	private void closeWithoutException(Reader posExamplesReader) {
        if (posExamplesReader != null) {
            try {
                posExamplesReader.close();
            } catch (IOException ignored) {
            }
        }
    }

    // See if these args are in these positions in SOME training example.
    // TODO(?): allow argumentW and argumentS to be null, meaning we dont care if they match?  Arguments should not be 'null' - but that could happen, so maybe a better indicator of 'dont care' is needed?
	boolean isWorldStateArgPairInAnExample(Term argumentW, Term argumentS) {
		return (isWorldStateArgPairInAnPosExample(argumentW, argumentS) ||
				isWorldStateArgPairInAnNegExample(argumentW, argumentS));
	}
	boolean isWorldStateArgPairInAnPosExample(Term argumentW, Term argumentS) {
		if (posExamples != null) for (Example ex : posExamples) {
			int numbArgs = ex.numberArgs();
			int wArg = stringHandler.getArgumentPosition(stringHandler.locationOfWorldArg, numbArgs);
			int sArg = stringHandler.getArgumentPosition(stringHandler.locationOfStateArg, numbArgs);	
			if (ex.getArgument(wArg).equals(argumentW) && ex.getArgument(sArg).equals(argumentS)) { return true; }
		}
		return false;
	}
	boolean isWorldStateArgPairInAnNegExample(Term argumentW, Term argumentS) {
		if (negExamples != null) for (Example ex : negExamples) {
			int numbArgs = ex.numberArgs();
			int wArg = stringHandler.getArgumentPosition(stringHandler.locationOfWorldArg, numbArgs);
			int sArg = stringHandler.getArgumentPosition(stringHandler.locationOfStateArg, numbArgs);	
			if (ex.getArgument(wArg) == argumentW && ex.getArgument(sArg) == argumentS) { return true; }
		}
		return false;
	}

	ILPSearchAction fireOuterLoopStarting(ILPouterLoop outerLoop) {
        ILPSearchAction action = ILPSearchAction.PERFORM_LOOP;

        Object[] listeners = searchListenerList.getListenerList();
        for (int i = 0; i < listeners.length; i+=2) {
            Class c = (Class)listeners[i];
            if ( ILPSearchListener.class.isAssignableFrom(c)) {
                ILPSearchListener listener = (ILPSearchListener)listeners[i+1];

                ILPSearchAction aAction = listener.outerLoopStarting(outerLoop);
                action = ILPSearchAction.getHigherPrecedenceAction(action, aAction);
            }
        }
        return action;
    }

    void fireOuterLoopFinished(ILPouterLoop outerLoop) {
        Object[] listeners = searchListenerList.getListenerList();
        for (int i = 0; i < listeners.length; i+=2) {
            Class c = (Class)listeners[i];
            if ( ILPSearchListener.class.isAssignableFrom(c)) {
                ILPSearchListener listener = (ILPSearchListener)listeners[i+1];

                listener.outerLoopFinished(outerLoop);
            }
        }
    }

    private ILPSearchAction fireInnerLoopStarting(LearnOneClause innerLoop) {
        ILPSearchAction action = ILPSearchAction.PERFORM_LOOP;

        Object[] listeners = searchListenerList.getListenerList();
        for (int i = 0; i < listeners.length; i+=2) {
            Class c = (Class)listeners[i];
            if ( ILPSearchListener.class.isAssignableFrom(c)) {
                ILPSearchListener listener = (ILPSearchListener)listeners[i+1];

                ILPSearchAction aAction = listener.innerLoopStarting(innerLoop);
                action = ILPSearchAction.getHigherPrecedenceAction(action, aAction);
            }
        }
        return action;
    }

    private void fireInnerLoopFinished(LearnOneClause innerLoop) {
        Object[] listeners = searchListenerList.getListenerList();
        for (int i = 0; i < listeners.length; i+=2) {
            Class c = (Class)listeners[i];
            if ( ILPSearchListener.class.isAssignableFrom(c)) {
                ILPSearchListener listener = (ILPSearchListener)listeners[i+1];

                listener.innerLoopFinished(innerLoop);
            }
        }
    }

	void setMlnRegressionTask(boolean val) {
		mlnRegressionTask = val;
	}

	void setLearnMultiVal(boolean val) {
		learnMultiValPredicates = val;
	}
	
	RegressionInfoHolder getNewRegressionHolderForTask() {
		if (mlnRegressionTask) {
			return new RegressionInfoHolderForMLN();
		} else {
			if (learnMultiValPredicates) {
				return new RegressionVectorInfoHolderForRDN();
			} else {
				return new RegressionInfoHolderForRDN();
			}
		}
	}

}
