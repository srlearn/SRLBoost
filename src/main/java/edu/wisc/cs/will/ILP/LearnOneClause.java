package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.ArgSpec;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.DataSetUtils.TypeManagement;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolderForMLN;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolderForRDN;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.Utils.Utils;
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
 *
 *        need to figure out to deal with CLAUSES during parsing (for now, 'canPrune(Literal lit)' does not allow pruning with such cases).
 *
 *        infer modes through deduction and not just from basic facts?  or too cpu-complicated?
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

    String              callerName = "unnamed caller";               // Used to annotate printing during runs.

	private final FileParser          parser;

	private   boolean             isaTreeStructuredTask = false; // For a tree-structured task, we don't want to generalize the heads (e.g., p(X,X) might be a good rule - will need to learn this via sameAs() calls ...).
	SingleClauseNode    currentStartingNode   = null;  // For some calculations we want to stop at this node.

	public    boolean			  regressionTask    = false; // Is this a REGRESSION task?
	boolean			  mlnRegressionTask	= false;

    int                 maxBodyLength                     =   9;     // Max length for the bodies of clauses.
	public    int                 maxFreeBridgersInBody             = maxBodyLength; // Bridgers can run amok so limit them (only has an impact when countBridgersInLength=true).  This is implemented as follows: the first  maxBridgersInBody don't count in the length, but any excess does.
	public    int                 maxNumberOfNewVars                =  10;     // Limit on the number of "output" variables used in a rule body.
	public    int        		  maxDepthOfNewVars                 =   7;     // The depth of variables in the head is 0.  The depth of a new variable is 1 + max depth of the input variables in the new predicate.
    private   double              minPosCoverage                    =   2.0;   // [If in (0,1), treat as a FRACTION of totalPosWeight].  Acceptable clauses must cover at least this many positive examples.  NOTE: this number is compared to SUMS of weighted examples, not simply counts (which is why this is a 'double').
	private   double              maxNegCoverage                    =  -1.0;   // [If in (0,1), treat as a FRACTION of totalNegWeight].  Acceptable clauses must cover no  more this many negative examples.  NOTE: this number is compared to SUMS of weighted examples, not simply counts (which is why this is a 'double').  IGNORE IF A NEGATIVE NUMBER.
	double              minPrecision                      =   0.501; // Acceptable clauses must have at least this precision.
	double              maxRecall                         =   1.01;  // When learning trees, don't want to accept nodes with TOO much recall, since want some examples on the 'false' branch.
    boolean             stopIfPerfectClauseFound          =   true;  // Might want to continue searching if a good SET of rules (eg, for Gleaner) is sought.
	public    double              clausesMustCoverFractPosSeeds     =   0.499; // ALL candidate clauses must cover at least this fraction of the pos seeds.  If performing RRR, these sets are used when creating the starting points.
    boolean             stopWhenUnacceptableCoverage      =   true;  // If set to  true, don't continue to prove examples when impossible to meet the minPosCoverage and minPrecision specifications.
    public    int                 minNumberOfNegExamples            =  10;     // If less than this many negative examples, create some implicit negative examples.
    final long                maxResolutionsPerClauseEval    = 10000000;     // When evaluating a clause, do not perform more than this many resolutions.  If this is exceeded, a clause is said to cover 0 pos and 0 neg, regardless of how many have been proven and it won't be expanded.

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

    private   List<PredicateNameAndArity>  examplePredicates          = null; // These store the positive example predicates that are eventually turned into targets.
	private   List<List<Term>>     examplePredicateSignatures = null; // Something like [constant, function(constant), constant].

    public    List<Literal>        targets                    = null; // These are the actual targets determined from the examplePredicates.
	List<List<ArgSpec>>  targetArgSpecs             = null; // The info about the target argument being used and the variables matched with their types.
	List<List<Term>>     variablesInTargets         = null; // These are really 'arguments' since it is possible a mode specifies a constant be used.

    final HornClauseContext    context;

	HandleFOPCstrings    stringHandler;
	final Unifier              unifier; // Make instances out of some things that could be 'statics' so the code is safer.
	private   HornClauseProver     prover; // This is initialized by getProver() so please don't use this variable directly.

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

		this.typeManager   = new TypeManagement(stringHandler);
        
		verbosity = 1;

        setInlineManager(new InlineManager(   stringHandler, getProver().getClausebase()));

		// Load BK first since it is the place where 'usePrologVariables' etc is typically set.
		if (backgroundClausesReader != null) { context.assertSentences(readBackgroundTheory(backgroundClausesReader)); }

		Initializer              init        = new InitializeILPsearchSpace();
		ChildrenClausesGenerator nodeGen     = new ChildrenClausesGenerator();
        // Limit the closed list to 100K items.  Note that items aren't placed here until EXPANDED, but items wont be placed in OPEN if already in CLOSED.
        int maxSizeOfClosed = 100000;
        VisitedClauses           c           = new VisitedClauses(maxSizeOfClosed);
		initalizeStateBasedSearchTask(init, null, monitor, strategy, scorer, nodeGen, c);
		nodeGen.initialize();
		setGleaner(monitor);

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

    public HandleFOPCstrings getStringHandler() {
		return stringHandler;
	}
	public final HornClauseProver getProver() {
        if ( prover == null ) {
            prover = new HornClauseProver( context );
        }
		return prover;
	}

	private void initialize() {
		initialize(false);
	}
	public void initialize(boolean creatingConjunctiveFeaturesOnly) { // Make this a separate call so that caller can set some public variables if it wants to do so.
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
			// Will be set to true when using this code to create features.

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
		// TODO(hayesall): Is the `procHandler` actually doing anything?

		if (Utils.getSizeSafely(posExamples) + Utils.getSizeSafely(negExamples) > 0) {
			chooseTargetMode();
		}

		Utils.println("\n% Started collecting constants");

		// TODO(hayesall): `typeManager` also appears to try to do type inference. This behavior should be deprecated.

		long start = System.currentTimeMillis();
		typeManager.collectTypedConstants(targets, targetArgSpecs, bodyModes, getPosExamples(), getNegExamples(), facts);
		long end = System.currentTimeMillis();

		Utils.println("% Time to collect constants: " + Utils.convertMillisecondsToTimeSpan(end - start));
        if (!creatingConjunctiveFeaturesOnly && minNumberOfNegExamples > 0 && getNegExamples() == null) {
            Utils.severeWarning("Have ZERO negative examples!  Variable 'minNumberOfNegExamples' is currently set to " + minNumberOfNegExamples + ".");
        }

        Utils.println("\n% Read " + Utils.comma(getPosExamples()) + " pos examples and " + Utils.comma(getNegExamples()) + " neg examples.");

        facts = null; // Release the temporarily stored facts so we aren't wasting memory.
        long iend = System.currentTimeMillis();
        Utils.println("% Time to init learnOneClause: " + Utils.convertMillisecondsToTimeSpan(iend-istart));
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

        if (!matchesExistingTargetSpec(lit)) {
            examplePredicates.add(pnaa);
            examplePredicateSignatures.add(stringHandler.getSignature(lit.getArguments()));
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

		for (Sentence sentence : sentences) {
			// These should all be facts, but there is really no way to enforce it.
			// However, if they are literals we will consider them as facts.
			// We add the fact predicate/arity to a set so we know that they
			// came in as facts and can be used as so later.
			if (sentence instanceof Literal) {
				Literal literal = (Literal) sentence;
				PredicateNameAndArity pnaa = literal.getPredicateNameAndArity();
			}
		}

		return sentences;
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
                newTerm = stringHandler.getNewNamedGeneratedVariable();
                theseTargetArgSpecs.add(new ArgSpec(newTerm, typeSpec));
				targetArguments.add(newTerm);
				theseVars.add(newTerm);
				counter++;
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
        // TODO(hayesall): This might explain why MLN regression has been so poorly behaved.
		mlnRegressionTask = val;
	}

    RegressionInfoHolder getNewRegressionHolderForTask() {
		if (mlnRegressionTask) {
			return new RegressionInfoHolderForMLN();
		} else {
            return new RegressionInfoHolderForRDN();
        }
	}

}
