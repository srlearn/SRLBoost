/*
 * Notes:
 * 
 *  isaStack: need to label ALL examples in each world
 *            maybe have 2-3 worlds, with 1-2 blocks in each
 *            and all (most?) data labeled
 *  
 *  me TODO
 *     make sure ok if NO negs can be created (eg, since all data is labelled)
 *      - hand edit file
 *      why isnt isablock(X) :- support(X, Y)?
 *      
 *      small penalty for 'unused' vars?
 *      
 *      clean up printing of rules?
 */
package edu.wisc.cs.will.ILP;


import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.*;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchMonitor;
import edu.wisc.cs.will.stdAIsearch.SearchStrategy;

import java.io.*;
import java.util.*;


/*
 * @author shavlik
 *
 * 
 *
 * VERSION 0.1 of the Wisconsin Inductive Logic Learner (WILL) system (name subject to change :-)
 *
 *	This class provides a mechanism for performing the traditional outer loop of ILP algorithms.
 *	The basic process is as follows:
 * 		1) do a standard ILP run
 * 		2) repeat using some new seed(s) examples until some stopping criteria met
 * 		3) return a set of clauses (a 'theory') as the final 'model'
 * 
 *  Some properties of this ILP algorithm:
 *      1) examples can be weighted
 *      2) both standard ILP heuristic search and a random-sampling method (RRR) can be performed
 *      3) the Gleaner idea (see Gleaner.java) is used to keep not only the best rule for iteration, but also the best rule per interval of recall (eg, the best rule whose recall is between 0.50 and 0,.55).
 *      4) on each cycle, multiple seed examples can be specified; a node (ie, a possible clause) needs to satisfy some fraction of the pos seeds and no more than some fraction of the negative seeds.  
 *      5) during successive iterations of the outer ILP loop, the pos examples can be down weighted and the covered neg examples can be up weighted (eg, a boosting-like mechanism, though the code currently does not compute the wgts defined by the boosting algo, but that would be a straightforward extension).
 *      6) implementation detail: in the inner loop, each node records the examples REJECTED at this node (this means that on any path to a node, examples are stored at no more than one node)
 *      7) hash tables (Java's hash maps, actually) are used for efficiency (eg, compared to linear lookups in lists)
 *      8) currently this code does NOT construct a "bottom clause" - instead if uses the multiple seed idea mentioned above to guide the search of candidate clauses
 *      9) no Prolog is needed; everything needed is provided in a set of Java projects (of course this means the code is slower than, say, Aleph+YAP Prolog, but computers get faster every year :-)
 *     10) as in Aleph and other ILP systems, arguments are typed (eg, 'human' and 'dog') to help control search; in this code the typing is hierarchical.
 *     11) as in Aleph, there is the ability for users to define prune(node), by which the user can cut off search trees.  Related to this is the built-in capability to process "intervals" such as isInThisInterval(1, value, 5).  If the previous literal is already in a clause, there is no need to add isInThisInterval(2, value, 4), since the latter will always be true given the former.  Similarly, there is no need to include isInThisInterval(7, value, 9) since it will always be false.  See PruneILPsearchTree.java for more detials. 
 * 
 * 	Note that with Gleaner as the searchMonitor, can create a theory from just one std ILP run.
 *	In this code, each std ILP run has its own Gleaner data structure, plus one Gleaner stores the best over ALL iterations.  
 *  Several different ways of returning a theory are provided (to do), as are various ways of stopping the outer loop.
 *  
 *  No support for this code is promised nor implied.  Suggestions and bug fixes may be sent to shavlik@cs.wisc.edu but please do not expect a reply.
 *  
 *  This code was heavily influenced by experience with Ashwin Srinivasan's Aleph (www.comlab.ox.ac.uk/oucl/research/areas/machlearn/Aleph/)
 *
 *  to do: count resolutions in theorem proving and throw if some max-value exceeded?
 *         add bottom clause code?
 */
public class ILPouterLoop {
	private static final String systemName = "WILL"; // See comment above for explanation.
   
	public final LearnOneClause innerLoopTask;  // LearnOnClause performs the inner loop of ILP.

	/* The state of the outer loop.
     *
     * Everything that should be checkpointed goes inside the ILPouterLoopState.  Variables
     * defined in ILPouterLoop will not be checkpointed.
     *
     */
	private final ILPouterLoopState outerLoopState;

	private String workingDirectory;

    public  int            maxNumberOfCycles             = 100;   // Call the inner loop at most this many times.
	public  int            maxNumberOfClauses            = 100;   // Same as above EXCEPT only counts if a clause was learned.
    public  int            max_total_nodesExpanded       = Integer.MAX_VALUE;
	public  int            max_total_nodesCreated        = Integer.MAX_VALUE;
    public  int            numberPosSeedsToUse           = 1;
	private int            numberNegSeedsToUse           = 0;

    ///////////////////////////////////////////////////////////////////
	// Parameters that are used when learning tree-structured theories.
	private  boolean        learningTreeStructuredTheory        = false;
	private int            maxNumberOfLiteralsAtAnInteriorNode =  2; // In calls to LearnOneClause, this is how much we are allowed to extend the current clause.  Initially it is the max body length, but since recursive calls extend the clause at the parent, we need to add this much to the current number of literals on the path to the current node (not counting the length of the tests that evaluate to false, i.e., for the FALSE branches).
    private int            maxTreeDepthInLiterals              = 25; // This is the sum of literals at all the nodes in a path from root to leaf, not just the number of interior nodes.
    private int			   maxTreeDepthInInteriorNodes         =  5; // Maximum height/depth of the tree in terms of interior nodes in the tree. NOTE: One node in the tree may have multiple literals.
    private String         prefixForExtractedRules             = "";
    private String         postfixForExtractedRules            = "";
    private boolean		   learnMLNTheory					   = false;
    private boolean        learnMultiValPredicates             = false;
    private boolean 	   learnOCCTree						   = false;
    ///////////////////////////////////////////////////////////////////

    // All of the fields below are now in the ILPouterLoopState object.
	// Any information needed to restart a run in the middle (from the chkpt)
    // must reside in the ILPouterLoopState object.
	//
	// There are accessors for all of these variable. For example, to get and set
	// numberOfCycles, there is now a getNumberOfCycles() and
	// setNumberOfCycles().
	// However, if you still want to access this variable directly, you can use
	// 'outerLoopState.numberOfCycles'.

    // These two allow one to randomly select a subset of the modes for each cycle.  (Added by JWS 6/24/10.)
	private Set<PredicateNameAndArity> holdBodyModes;
	public double randomlySelectWithoutReplacementThisManyModes = -1; // If in (0, 1), then is a FRACTION of the modes. If negative, then do not sample.	

    public ILPouterLoop(String workingDir, String prefix, String[] args,
    					SearchStrategy strategy, ScoreSingleClause scorer, SearchMonitor monitor, 
    	                HornClauseContext context, boolean useRRR, boolean deferLoadingExamples) throws IOException {
        this(workingDir, prefix, 
                getBufferedReaderFromString(ILPouterLoop.getInputArgWithDefaultValue(args, 0, "pos.txt")),
                getBufferedReaderFromString(ILPouterLoop.getInputArgWithDefaultValue(args, 1, "neg.txt")),
                getBufferedReaderFromString(ILPouterLoop.getInputArgWithDefaultValue(args, 2, "bk.txt")),
                getBufferedReaderFromString(ILPouterLoop.getInputArgWithDefaultValue(args, 3, "facts.txt")),
                strategy, scorer, monitor, context, useRRR, deferLoadingExamples);
    }

    private ILPouterLoop(String workingDir, String prefix, Reader posExamplesReader, Reader negExamplesReader, Reader backgroundReader, Reader factsReader,
                         SearchStrategy strategy, ScoreSingleClause scorer, SearchMonitor monitor, HornClauseContext context, boolean useRRR, boolean deferLoadingExamples) {

       outerLoopState = new ILPouterLoopState();
       
       setWorkingDirectory(workingDir);

       if ( prefix == null ) {
            // Oops, prefix was null.  This just means we probably used the shorter constructors.
            // Just extract it from the working directory name.
            prefix = new CondorFile(workingDirectory).getName();
        }

        Utils.println("\n% Welcome to the " + systemName + " ILP/SRL systems.\n");

        // LearnOneClause performs the inner loop of ILP.
		// TODO maybe we should send in the full outer loop instance (ie, this).

		innerLoopTask = new LearnOneClause(workingDir, prefix, posExamplesReader, negExamplesReader, backgroundReader, factsReader, strategy, scorer, monitor, context, deferLoadingExamples);

        if (monitor instanceof Gleaner) {
            setGleaner((Gleaner) monitor);
        }
        else if (monitor != null) {
            Utils.waitHere("The Search Monitor is not an instance of Gleaner: " + monitor);
        } 

        setRRR(useRRR);
	}
	
	private String getFoldInfoString() {
		if (getCurrentFold() == -1) { return ""; }
		return "_fold" + getCurrentFold();
	}

	private int getCurrentFold() {
        return outerLoopState.getCurrentFold();
    }
	
	private static BufferedReader getBufferedReaderFromString(String string) throws IOException {
		if (string == null) { return null; }
		return new NamedReader(new CondorFileReader(string), string);
	}
	
	// Needed to get around need that "constructor call must be the first statement in a constructor."
	private static String getInputArgWithDefaultValue(String[] args, int N, String defaultString) {
		Utils.println("\n% getInputArgWithDefaultValue: args=" + Arrays.asList(args).toString() + "\n%  for N=" + N + ": args[N]=" + args[N]);
		return (args.length < (N + 1) ? defaultString : args[N]);
	}

	public void setMinPrecisionOfAcceptableClause(double precision) {
		if (precision < 0.0 || precision > 1.0) {
			Utils.error("Min precision (" + precision + ") must be in [0,1].");
		}
		innerLoopTask.setMinPrecision(precision);
	}

	public void setMaxRecallOfAcceptableClause(double recall) {
		if (recall < 0.0 || recall > 1.0) {
			Utils.error("Max recall (" + recall + ") must be in [0,1].");
		}
		innerLoopTask.setMaxRecall(recall);
	}

	public void setMaxBodyLength(int maxBodyLength) {
		if (maxBodyLength < 0) {
			Utils.error("Length (" + maxBodyLength + ") must be a non-negative integer.");
		}
		// Recall that in tree-structured runs, the length of all parent nodes is also included here.
		innerLoopTask.maxBodyLength = Math.min(maxBodyLength, learningTreeStructuredTheory ? maxTreeDepthInLiterals : Integer.MAX_VALUE);
	}

	private boolean isaGoodPosSeed(int index) { // If good, then set it as the positive seed to use.
		if (index < 0 || index >= getNumberOfPosExamples()) {
			return false;
		} // Simply skip over indices that are out of bounds.
		Example chosenExample = innerLoopTask.getPosExamples().get(index);
		if ((innerLoopTask.allowPosSeedsToBeReselected || getSeedPosExamplesUsed() == null || !getSeedPosExamplesUsed().contains(chosenExample)) && // Make sure that this wasn't previously a seed.
			!getCoveredPosExamples().contains(chosenExample)) { // Make sure this is an uncovered seed.
			int[] posSeeds = new int[1];
			posSeeds[0] = index;
			Utils.println(MessageType.ILP_OUTERLOOP, "% Have selected pos example #" + Utils.comma(index) + " as the next seed: " + chosenExample);
			innerLoopTask.selectTheseSeedsByIndex(posSeeds, getSeedPosExamplesUsed(), getSeedNegExamplesUsed()); // Use no negative seeds.
			return true;
		}
		return false;
	}

	private boolean collectMultipleSeeds() {
		if (numberPosSeedsToUse < 1) { numberPosSeedsToUse = 1; }
		if (numberNegSeedsToUse < 0) { numberNegSeedsToUse = 0; }
		
		// TODO - figure out how to report wrt to the flip-flop state.
		if (numberPosSeedsToUse > getNumberOfPosExamples()) { Utils.warning("% Have only " + Utils.comma(getNumberOfPosExamples()) + " positive examples, so cannot choose " + Utils.comma(numberPosSeedsToUse) + " of them."); }
		if (numberNegSeedsToUse > getNumberOfNegExamples()) { Utils.warning("% Have only " + Utils.comma(getNumberOfNegExamples()) + " negative examples, so cannot choose " + Utils.comma(numberNegSeedsToUse) + " of them."); }
		
		numberPosSeedsToUse = Math.min(numberPosSeedsToUse, getNumberOfPosExamples());
		numberNegSeedsToUse = Math.min(numberNegSeedsToUse, getNumberOfNegExamples());
		
		int[] posSeeds = new int[numberPosSeedsToUse];
		int[] negSeeds = new int[numberNegSeedsToUse];
		
		int posCounter = 0;
		int negCounter = 0;
		Set<Integer> posChosen = new HashSet<>(4);
		Set<Integer> negChosen = new HashSet<>(4);
		
		// Could be really slow if selecting nearly all of the examples, but we're limiting this to 10X tries, so don't worry about it.
		if (innerLoopTask.allowPosSeedsToBeReselected) {
			int counter = 0; // Put a limit on the number of cycles here.
			while (posCounter < numberPosSeedsToUse && counter++ < 10 * numberPosSeedsToUse) {
				int index = Utils.random0toNminus1(getNumberOfPosExamples());
				if (!posChosen.contains(index)) {
					posChosen.add(index);
					posSeeds[posCounter++] = index;
				}
			}			
		}
		// It still looking, grab in order.
		if (posCounter < numberPosSeedsToUse) {
			int i = 0;
			// Use the 1.1 to handle the case of not getting enough due to sampling effects.  This fraction is ratio of SEEDS_NEEDED over SEEDS_TO_SELECT_FROM.
			double fraction = 1.1 * (numberPosSeedsToUse - posCounter) / (double) (innerLoopTask.getPosExamples().size() - getCoveredPosExamples().size() - posCounter);
			for (Example pos : innerLoopTask.getPosExamples()) { // Would be nice to more cleanly randomly walk through the examples, but after the first cycle, will at least skip those already covered.
				if (Utils.random() < fraction && !getCoveredPosExamples().contains(pos) && !posChosen.contains(i)) {
					posChosen.add(i);
					posSeeds[posCounter++] = i;
					if (posCounter >= numberPosSeedsToUse) { break; }
				}
				i++;
			}
		}
		
		if (innerLoopTask.allowNegSeedsToBeReselected) {
			int counter = 0;
			while (negCounter < numberNegSeedsToUse && counter++ < 10 * numberNegSeedsToUse) {
				int index = Utils.random0toNminus1(getNumberOfNegExamples());
				if (!negChosen.contains(index)) {
					negChosen.add(index);
					negSeeds[posCounter++] = index;
				}
			}			
		}
		if (negCounter < numberNegSeedsToUse) {
			int i = 0; // See comment above.
			double fraction = 1.1 * (numberNegSeedsToUse - negCounter) / (double) (innerLoopTask.getNegExamples().size() - outerLoopState.getNegExamplesUsedAsSeeds().size() - negCounter);
			for (Example neg : innerLoopTask.getNegExamples()) {
				if (Utils.random() < fraction && !getNegExamplesUsedAsSeeds().contains(neg) && !negChosen.contains(i)) {
					negChosen.add(i);
					negSeeds[negCounter++] = i;
					getNegExamplesUsedAsSeeds().add(neg); // TODO - when done using all the negative seeds, should reset to use all again. 
					if (negCounter >= numberNegSeedsToUse) { break; }
				}
				i++;
			}
		}
		// If arrays still not full, shorten them.
		if (posCounter < numberPosSeedsToUse) {
			int[] posSeedsShorter = new int[Math.max(0, posCounter)];
            System.arraycopy(posSeeds, 0, posSeedsShorter, 0, posCounter);
			posSeeds = posSeedsShorter;
		}
		if (negCounter < numberNegSeedsToUse) {
			int[] negSeedsShorter = new int[Math.max(0, negCounter)];
            System.arraycopy(negSeeds, 0, negSeedsShorter, 0, negCounter);
			negSeeds = negSeedsShorter;
			   getNegExamplesUsedAsSeeds().clear(); // If ran short on negative seeds, allow old ones to be used again (BUG: should add more now, but live with one cycle with a shortage of negative seeds).
		}
		int maxToPrint = 100;
		if (posSeeds.length > 0) { Utils.print("\n% Have these " + Utils.comma(posSeeds.length) + " positive seeds:"); for (int i = 0; i < Math.min(maxToPrint, posSeeds.length); i++) Utils.print(" " + posSeeds[i]); if (posSeeds.length > maxToPrint) Utils.println(" ..."); else Utils.println(""); }
		if (negSeeds.length > 0) { Utils.print("\n% Have these " + Utils.comma(negSeeds.length) + " negative seeds:"); for (int i = 0; i < Math.min(maxToPrint, negSeeds.length); i++) Utils.print(" " + negSeeds[i]); if (negSeeds.length > maxToPrint) Utils.println(" ..."); else Utils.println(""); }
		innerLoopTask.selectTheseSeedsByIndex(posSeeds, negSeeds, false, getSeedPosExamplesUsed(), getSeedNegExamplesUsed()); // OK if reused (e.g., if not covered or if a negative seed).
		return (posCounter > 0); // Need at least one positive seed.
	}

    /* Executes the outer ILP loop.
     *
     * This will attempt to find one or more clauses that cover the positive and
     * negative examples.  executeOuterLoop will completely reset the search and
     * start from scratch.
     *
     * @return The learned theory.
     * @throws edu.wisc.cs.will.stdAIsearch.SearchInterrupted Thrown if the search is interrupted prior
     * to completion.
     */
	public Theory executeOuterLoop() throws SearchInterrupted {
        resetAll();
        ILPSearchAction action = innerLoopTask.fireOuterLoopStarting(this);

        if (action == ILPSearchAction.PERFORM_LOOP) {

            // If no body modes, no need to run.
            if (Utils.getSizeSafely(innerLoopTask.bodyModes) < 1) {
				Utils.waitHere("Have no body modes.");
				return new Theory(innerLoopTask.getStringHandler());
            }

            boolean stoppedBecauseNoMoreSeedsToTry         = false;
            boolean stoppedBecauseTreeStructuredQueueEmpty = false;

            if (learningTreeStructuredTheory && outerLoopState.queueOfTreeStructuredLearningTasksIsEmpty()) {
                stoppedBecauseTreeStructuredQueueEmpty = true;
                Utils.waitHere("Have learningTreeStructuredTheory=true but stack of tasks is empty (or equal to null).");
            }

            SingleClauseNode savedBestNode = null; // When learning tree-structured models, we need to remember the node learned at the parent.
            long start;
            boolean foundUncoveredPosSeed;
            // Stop when this fraction of the positive examples are covered by some acceptable clause.

            // TODO(@hayesall): `minFractionOfPosCoveredToStop` is always `0.9`, this might be an interesting parameter to tune, particularly with more boosted trees.
            double minFractionOfPosCoveredToStop = 0.90;
            while (!stoppedBecauseNoMoreSeedsToTry && !stoppedBecauseTreeStructuredQueueEmpty &&
                    getNumberOfLearnedClauses() < maxNumberOfClauses &&
                    getNumberOfCycles() < maxNumberOfCycles &&
                    getFractionOfPosCovered() < minFractionOfPosCoveredToStop &&
                    getTotal_nodesConsidered() < max_total_nodesExpanded &&
                    getTotal_nodesCreated() < max_total_nodesCreated &&
                    getClockTimeUsedInMillisec() < getMaximumClockTimeInMillisec()
                   ) {

                start = System.currentTimeMillis();
                if (learningTreeStructuredTheory) {
                    innerLoopTask.resetAllForReal(); // Clear OPEN and CLOSED (and other things).
                    outerLoopState.setCurrentTreeLearningTask(outerLoopState.popQueueOfTreeStructuredLearningTasks()); // Set in outerloopState class instead of here?
                    savedBestNode = outerLoopState.getCurrentTreeLearningTask().getCreatingNode();
                    clearSeedPosExamplesUsed();
                    clearSeedNegExamplesUsed();
                    innerLoopTask.setPosExamples(   outerLoopState.getCurrentTreeLearningTask().getPosExamples()); // Need to do these AFTER the setMinPosCoverage since that might be a fraction.
                    innerLoopTask.setNegExamples(   outerLoopState.getCurrentTreeLearningTask().getNegExamples());
                    innerLoopTask.setMinPosCoverage(outerLoopState.getOverallMinPosWeight()); // Even when we have fewer examples, we want the minPosWeight to be that from the first call.
                    
                    if (savedBestNode != null) { // Have to recompute this because the examples have changed.
                        Utils.println("\n% Working on expanding this node: '" + savedBestNode + "'");
                        ((LearnOneClause)savedBestNode.task).currentStartingNode = savedBestNode.getStartingNodeForReset(); // Only setting this while resetting the score for savedBestNode.
                        savedBestNode.resetAssumingAllExamplesCovered();
                        savedBestNode.setDontAddMeToOPEN(false);
                        innerLoopTask.scorer.scoreThisNode(savedBestNode);
                        setMaxBodyLength(Math.min(maxTreeDepthInLiterals, savedBestNode.bodyLength() + maxNumberOfLiteralsAtAnInteriorNode));
                    } else {
                        setMaxBodyLength(Math.min(maxTreeDepthInLiterals, maxNumberOfLiteralsAtAnInteriorNode));
                    }
					innerLoopTask.currentStartingNode = savedBestNode;
                }

                setNumberOfCycles( getNumberOfCycles() + 1 );

                Stopwatch stopwatch = new Stopwatch();

                // WE NEED TO PICK A NEW SET OF SEEDS EACH TIME SINCE SEEDS CHOSEN AT THE ROOT WILL FOLLOW VARIOUS PATHS THROUGH THE TREE.  if (!foundUncoveredPosSeed || !learningTreeStructuredTheory) { // If tree-structured task, we want to use the same seeds for the full tree (otherwise maybe no [new] seeds reach the current interior node).
				// Specify the specific seeds to use if requested.
				foundUncoveredPosSeed = false;
				if (numberPosSeedsToUse > 1 || numberNegSeedsToUse > 0) { foundUncoveredPosSeed = collectMultipleSeeds(); }

                // Otherwise randomly select one positive seed be used.
				int tries = 0;
				while (!foundUncoveredPosSeed && tries++ < 1000) { // 1000 might be low if a very large number of pos ex's, but if hard to find, grabbing seeds in numerical order (next step) should be fine.
					int index = Utils.random0toNminus1(getNumberOfPosExamples());
					foundUncoveredPosSeed = isaGoodPosSeed(index);
				}
				// If still no luck, walk through in order until an uncovered seed is found. Should always be able to find an uncovered seed because we know fraction covered less than 1.0 ...
				if (!foundUncoveredPosSeed) {
					int randomOffset = Utils.random0toNminus1(getNumberOfPosExamples());  // Start at a random location in the array, and do a "wrap around" walk through the values.
					for (int index = 0; index < getNumberOfPosExamples(); index++) {
						int indexToUse = (randomOffset + index)	% getNumberOfPosExamples();
						foundUncoveredPosSeed = isaGoodPosSeed(indexToUse);
                        if (foundUncoveredPosSeed) { break; }
					}
				}

				if (!foundUncoveredPosSeed) { // Since there is a minimum coverage on the best clause, some seeds won't be covered and we might run out of seeds before meeting some other termination criterion.
                    stoppedBecauseNoMoreSeedsToTry = true;
                } else {
                    // Do the ILP inner loop.
                    //    First clear Gleaner and set up a new Gleaner set (i.e., will keep best rules PER CYCLE).
                    Gleaner theGleaner = (Gleaner) innerLoopTask.searchMonitor;
                    theGleaner.clearBestNode();

                    innerLoopTask.caller     = this;
                    innerLoopTask.callerName = "outerLoop #" + getNumberOfCycles() + getFoldInfoString();
                    theGleaner.setCurrentMarker(innerLoopTask.callerName);
                    if (!learningTreeStructuredTheory) { innerLoopTask.stringHandler.resetVarCounters(); } // When learning a tree-structured theory, we need a consistent set of variables.
                    innerLoopTask.checkIfAcceptableClausePossible();

                    if (getMaximumClockTimeInMillisec() < Long.MAX_VALUE) {
                        double denominator = 1.0; // If there is a time limit, leave some for later cycles, but allow at least 25% of the time for this one.
                        if (maxNumberOfCycles > 1 && getMaximumClockTimeInMillisec() != Long.MAX_VALUE) { denominator = Math.max(1.0, Math.min(4.0, maxNumberOfCycles / (1 + getNumberOfCycles()))); }
                        long innerLoopTimeLimit = (long) (getTimeAvailableInMillisec() / denominator);
                        innerLoopTask.setMaximumClockTimePerIterationInMillisec(innerLoopTimeLimit);
                    } else {
                        innerLoopTask.setMaximumClockTimePerIterationInMillisec(getMaximumClockTimeInMillisec());
                    }

                    ((ChildrenClausesGenerator) innerLoopTask.childrenGenerator).countOfPruningDueToVariantChildren = 0;

                    // If we are going to be sampling the modes, make a copy of the full set.  AND RESET WHEN DONE.
                    if (randomlySelectWithoutReplacementThisManyModes > 0 && holdBodyModes == null) {
                        holdBodyModes = innerLoopTask.getBodyModes();

                        if (randomlySelectWithoutReplacementThisManyModes < 1) { // Interpret as a FRACTION.  TODO - should we keep the fraction?  Seems not worth the trouble.
                            randomlySelectWithoutReplacementThisManyModes = Math.round(randomlySelectWithoutReplacementThisManyModes * Utils.getSizeSafely(holdBodyModes));
                        }
                    }
                    if (randomlySelectWithoutReplacementThisManyModes > 0 && randomlySelectWithoutReplacementThisManyModes  < Utils.getSizeSafely(holdBodyModes)) {
                        Set<PredicateNameAndArity> newSetOfBodyModes = new HashSet<>((int) randomlySelectWithoutReplacementThisManyModes);
                        int bodyModeSize = Utils.getSizeSafely(holdBodyModes);
                        // If we are getting almost all of the body nodes, we really should make a copy then DELETE entries until small enough.
                        int counter = 0;
                        while (Utils.getSizeSafely(newSetOfBodyModes) < randomlySelectWithoutReplacementThisManyModes ) {
                            int                   index = Utils.random0toNminus1(bodyModeSize);
                            PredicateNameAndArity pName = Utils.getIthItemInCollectionUnsafe(holdBodyModes, index);

                            newSetOfBodyModes.add(pName); // If a duplicate, won't be added.
                            if (++counter > 10 * randomlySelectWithoutReplacementThisManyModes) { Utils.waitHere("Stuck in an infinite loop?  randomlySelectWithoutReplacementThisManyModes=" + Utils.comma(randomlySelectWithoutReplacementThisManyModes)); counter = 0; }
                        }
                        innerLoopTask.setBodyModes(newSetOfBodyModes);
                    }

                    // If we are learning a tree-structured theory, then we continue where we left off.
                    if (isRRR()) {
                        innerLoopTask.performRRRsearch(learningTreeStructuredTheory ? savedBestNode : null);
                    } else {
                        innerLoopTask.performSearch(learningTreeStructuredTheory ? savedBestNode : null);
					}

                    // Want limits on (and statistics about) the full ILP search as well.
                    setTotal_nodesConsidered(getTotal_nodesConsidered() + innerLoopTask.getNodesConsidered());
                    setTotal_nodesCreated(   getTotal_nodesCreated()    + innerLoopTask.getNodesCreated());
                    setTotal_nodesNotAddedToOPENsinceMaxScoreTooLow(    getTotal_nodesNotAddedToOPENsinceMaxScoreTooLow()     + innerLoopTask.nodesNotAddedToOPENsinceMaxScoreTooLow);
                    setTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow(getTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow() + innerLoopTask.nodesRemovedFromOPENsinceMaxScoreNowTooLow);
                    setTotal_countOfPruningDueToVariantChildren(getTotal_countOfPruningDueToVariantChildren() + ((ChildrenClausesGenerator) innerLoopTask.childrenGenerator).countOfPruningDueToVariantChildren);
                    // Report what happened (TODO have an output 'results' file).

                    // TODO(@hayesall): `SingleClauseNode bestNode = theGleaner.bestNode;`
                    SingleClauseNode bestNode = theGleaner.bestNode;
                    
                    Utils.println("\n% The best node found: " + bestNode); // TEMP
                    
                    if (bestNode != null && bestNode != savedBestNode) { // Also need to check to make sure we didn't simply return the previous root when doing tree-structured learning.
                        Utils.println("\n% The best node found: " + bestNode);
                        List<Example> coveredPosExamplesThisCycle = innerLoopTask.collectPosExamplesCovered(bestNode);
                        List<Example> coveredNegExamplesThisCycle = innerLoopTask.collectNegExamplesCovered(bestNode);
                        int newlyCoveredPosExamples = 0;
                        int newlyCoveredNegExamples = 0;
                        int coveredPosExamplesCount = Utils.getSizeSafely(coveredPosExamplesThisCycle);
                        int coveredNegExamplesCount = Utils.getSizeSafely(coveredNegExamplesThisCycle);

                        if (coveredPosExamplesCount > 0) {
                            for (Example ex : coveredPosExamplesThisCycle) {
                                // Utils.println("   covered pos: " + ex);
                                if (!getCoveredPosExamples().contains(ex)) {
                                    if (!learningTreeStructuredTheory) { // When learning trees we don't need to count coverings by possibly overlapping rules.
                                        getCoveredPosExamples().add(ex);
                                        setNumberOfPosExamplesCovered(getNumberOfPosExamplesCovered() + 1); // An awkward way to increment ...
                                    }
                                    newlyCoveredPosExamples++;
                                }
                            }
                        }
                        if (coveredNegExamplesCount > 0) {
                            for (Example ex : coveredNegExamplesThisCycle) {
                                // Utils.println(" covered neg: " + ex);
                                if (!getCoveredNegExamples().contains(ex)) {
                                    if (!learningTreeStructuredTheory) {  // See comment above.
                                        getCoveredNegExamples().add(ex);
                                        setNumberOfNegExamplesCovered(getNumberOfNegExamplesCovered() + 1); // An awkward way to increment ...
                                    }
                                    newlyCoveredNegExamples++;
                                }
                            }
                        }

                        // The following line of code allowed covered examples to be reweighted on the fly during theory search.
                        //
                        // While an interesting idea, there are all sorts of problems the way you implemented it
                        // (even in the old map-based weight implementation), the biggest being that you never retain
                        // their original weights, so post-learning scoring would have been wacky.  Covered examples
                        // would have been down weighted in the final coverage scores...this could happen on both
                        // negative and positive examples, so it would be hard to say exactly what the effect would
                        // be, but it wouldn't have been the expected final score.
                        //
                        // I am commenting it out for now, but we can re-implement later if desired.
                        // -Trevor

                        if (coveredPosExamplesCount < 1) {
                            Utils.warning("Have a bestNode that covers no positive examples.  That shouldn't happen.  Best node = " + bestNode);
                        }
                        setNumberOfLearnedClauses(getNumberOfLearnedClauses() + 1);
                        Clause newClause = new LearnedClause(innerLoopTask, bestNode, getNumberOfCycles(),
                                                             getNumberOfPosExamplesCovered(), coveredPosExamplesCount, newlyCoveredPosExamples,
                                                             getNumberOfPosExamples(), getNumberOfNegExamplesCovered(),  coveredNegExamplesCount,
                                                             newlyCoveredNegExamples, getNumberOfNegExamples());

                        if (learningTreeStructuredTheory) {

                            TreeStructuredLearningTask       currentTask  = outerLoopState.getCurrentTreeLearningTask();
                            TreeStructuredTheoryInteriorNode interiorNode = currentTask.getNode();
                            interiorNode.setSearchNodeThatLearnedTheClause(bestNode); // Be sure to set this before the next call.
                            interiorNode.setNodeTestFromFullNodeTest(newClause);
                            // Set the task used to learn this node.
                            bestNode.setStartingNodeForReset(innerLoopTask.currentStartingNode);
							Utils.println("\n% Expanding node at Level " + interiorNode.getLevel() + " with score = " + Utils.truncate(currentTask.getScore(), 3) + ".\n% Will extend: " + interiorNode.getSearchNodeThatLearnedTheClause());

							boolean atMaxDepth = (interiorNode.getLevel() >= maxTreeDepthInInteriorNodes);
                            
                            TreeStructuredTheoryNode trueBranch;
                            TreeStructuredTheoryNode falseBranch;
                            boolean goodEnoughFitTrueBranch  = atMaxDepth || bestNode.acceptableScoreTrueBranch( outerLoopState.maxAcceptableNodeScoreToStop);
                            boolean goodEnoughFitFalseBranch = atMaxDepth || bestNode.acceptableScoreFalseBranch(outerLoopState.maxAcceptableNodeScoreToStop);

                            List<Example> trueBranchPosExamples  = null;
                            List<Example> falseBranchPosExamples = null;
                            List<Example> trueBranchNegExamples  = null;
                            List<Example> falseBranchNegExamples = null;

                            double wgtedCountTrueBranchPos  = 0.0;
                            double wgtedCountTrueBranchNeg  = 0.0;
                            double wgtedCountFalseBranchPos = 0.0;
                            double wgtedCountFalseBranchNeg = 0.0;

                            List<Example> posEx = currentTask.getPosExamples();
                            List<Example> negEx = currentTask.getNegExamples();

                            // Since we are collecting 'extra labels' for leaf nodes, we need always to collect examples.
                            if (posEx != null) {
                                trueBranchPosExamples  = new ArrayList<>(8);
                                falseBranchPosExamples = new ArrayList<>(8);
                                for (Example ex : posEx) {
                                    if (bestNode.matchesThisExample(ex, true)) {
										trueBranchPosExamples.add(ex);
										wgtedCountTrueBranchPos += ex.getWeightOnExample();
                                    } else {
										falseBranchPosExamples.add(ex);
										wgtedCountFalseBranchPos += ex.getWeightOnExample();
                                    }
                                }
                            }
                            // Since we are collecting 'extra labels' for leaf nodes, we need always to collect examples.
                            if (negEx != null) {
                                trueBranchNegExamples  = new ArrayList<>(8);
                                falseBranchNegExamples = new ArrayList<>(8);
                                for (Example ex : negEx) {
                                    if (bestNode.matchesThisExample(ex, false)) {
										trueBranchNegExamples.add(ex);
										wgtedCountTrueBranchNeg += ex.getWeightOnExample();
                                    } else {
										falseBranchNegExamples.add(ex);
										wgtedCountFalseBranchNeg += ex.getWeightOnExample();
                                    }
                                }
                            }

							double meanTrue;

                            if (learnMLNTheory) {
                            	meanTrue = bestNode.mlnRegressionForTrue();
                            } else {
                            	if (!learnOCCTree) {
                            		meanTrue = bestNode.meanIfTrue();
                            	} else {
                            		meanTrue = 1;
                            		for (Boolean b : interiorNode.returnBoolPath()) {
										meanTrue = 10*meanTrue + (b?1:0);
									}
                            		meanTrue = 10*meanTrue + 1;
                            	}
                            }
                            
                            if (learnMultiValPredicates) {
                                // TODO(@hayesall): This branch always leads to an error, we might be able to exit earlier.
                                Utils.error("No mean vector on true branch!!");
                            }
                            // We use 2.1 * getMinPosCoverage() here since we assume each branch needs to have getMinPosCoverage() (could get by with 2, but then would need a perfect split).
                            // Since getLength() includes the head, we see if current length EXCEEDS the maxTreeDepthInLiterals.
                            // Since 'maxTreeDepthInLiterals' includes bridgers, count them as well.
                            if (atMaxDepth) { Utils.println("%   Creating a TRUE-branch and FALSE-branch leaves because level = "  + interiorNode.getLevel() + " >= " + maxTreeDepthInInteriorNodes); }
							// If false, then sort by TOTAL score of the examples reaching that node.
                            if (atMaxDepth || goodEnoughFitTrueBranch ||
                                newClause.getLength()   >  maxTreeDepthInLiterals || // We use '>' here since we don't count the head literal in depth.
                                wgtedCountTrueBranchPos <  2.1 * innerLoopTask.getMinPosCoverage() ||
                                wgtedCountTrueBranchPos <  outerLoopState.getOverallMinPosWeight()) {
                                

                                if (!atMaxDepth) {
                                    if      (newClause.getLength()   >  maxTreeDepthInLiterals)                  { Utils.println("%   Creating a TRUE-branch leaf because length = " + newClause.getLength()   + " > " + maxTreeDepthInLiterals); }
                                    else if (wgtedCountTrueBranchPos <  2.1 * innerLoopTask.getMinPosCoverage()) { Utils.println("%   Creating a TRUE-branch leaf because wgtedCountTrueBranchPos = "  + Utils.truncate(wgtedCountTrueBranchPos, 1) + " < 2.1 * minPosCov = " + Utils.truncate(2.1 * innerLoopTask.getMinPosCoverage(), 1)); }
                                    else if (wgtedCountTrueBranchPos <  outerLoopState.getOverallMinPosWeight()) { Utils.println("%   Creating a TRUE-branch leaf because wgtedCountTrueBranchPos = "  + Utils.truncate(wgtedCountTrueBranchPos, 1) + " < minPosWgt = "       + Utils.truncate(outerLoopState.getOverallMinPosWeight(), 1)); }
                                    else if (goodEnoughFitTrueBranch) 											 { Utils.println("%   Creating a TRUE-branch leaf because good enough fit since score < " +  outerLoopState.maxAcceptableNodeScoreToStop); }
                                }
                                Term leaf;
                                if (learnMultiValPredicates) {
                                    // TODO(@hayesall): Replacing with null leads this to always fail.
                                	leaf = createLeafNodeFromCurrentExamples(Objects.requireNonNull(null));
                                } else {
                                	leaf = createLeafNodeFromCurrentExamples(meanTrue);
                                }
                                trueBranch = new TreeStructuredTheoryLeaf(wgtedCountTrueBranchPos, wgtedCountTrueBranchNeg, bestNode.getVarianceTrueBranch(), leaf, Example.makeLabel(trueBranchPosExamples));
                            } else {
                                // Have another learning task.
                                TreeStructuredTheoryInteriorNode newTreeNode = new TreeStructuredTheoryInteriorNode(wgtedCountTrueBranchPos, wgtedCountTrueBranchNeg, null, null, null);
                                TreeStructuredLearningTask       newTask     = new TreeStructuredLearningTask(      trueBranchPosExamples,   trueBranchNegExamples, newTreeNode);
                                trueBranch = newTreeNode;
                                newTreeNode.setParent(interiorNode); // Need a back pointer in case we later make this interior node a leaf.
                                newTreeNode.setBoolPath(interiorNode.returnBoolPath()); newTreeNode.addToPath(true);// Set the path taken to this node
                                if (learnMultiValPredicates) {
                                	newTreeNode.setRegressionVectorIfLeaf(null);
                                } else {
                                	newTreeNode.setRegressionValueIfLeaf(meanTrue);
                                }
                                
                                // Since elsewhere we negate the score, do so here as well.
                                Utils.println("%   Creating a TRUE-branch interior node with wgtedCountTrueBranchPos = " + Utils.truncate(wgtedCountTrueBranchPos, 1));
                                outerLoopState.addToQueueOfTreeStructuredLearningTasks(newTask, newTreeNode, bestNode, -bestNode.getVarianceTrueBranch(true));
                            }
                            double meanFalse;

                            if (learnMLNTheory) {
                            	meanFalse = bestNode.mlnRegressionForFalse();
                            } else {
                            	if (!learnOCCTree) {
                            		meanFalse = bestNode.meanIfFalse();
                            	} else {
                            		meanFalse = 1;
                            		for (Boolean b : interiorNode.returnBoolPath()) {
										meanFalse = 10*meanFalse + (b?1:0);
									}
                            		meanFalse = 10*meanFalse + 0;
                            	}
                            }

                            // No need to check max clause length (maxTreeDepthInLiterals) since that should have been checked at parent's call (since no literals added for FALSE branch).
                            if (atMaxDepth || goodEnoughFitFalseBranch ||
                                wgtedCountFalseBranchPos <  2.1 * innerLoopTask.getMinPosCoverage() ||
                                wgtedCountFalseBranchPos <  outerLoopState.getOverallMinPosWeight()) {
          
                                Term leaf;
                                if (learnMultiValPredicates) {
                                    // TODO(@hayesall): This simplified to `Objects.requireNonNull(null)`, remove.
                                	leaf = createLeafNodeFromCurrentExamples(Objects.requireNonNull(null));
                                } else {
                                	leaf = createLeafNodeFromCurrentExamples(meanFalse);
                                }
                                

                                if (!atMaxDepth) {
                                    if      (interiorNode.getLevel() >= maxTreeDepthInInteriorNodes) { Utils.println("%   Creating a FALSE-branch leaf because level = "  + interiorNode.getLevel() + " > " + maxTreeDepthInInteriorNodes); }
                                    else if (wgtedCountFalseBranchPos <  2.1 * innerLoopTask.getMinPosCoverage()) { Utils.println("%   Creating a FALSE-branch leaf because wgtedCountFalseBranchPos = "  + Utils.truncate(wgtedCountFalseBranchPos, 1) + " < 2.1 * minPosCov = " + Utils.truncate(2.1 * innerLoopTask.getMinPosCoverage(), 1)); }
                                    else if (wgtedCountFalseBranchPos <  outerLoopState.getOverallMinPosWeight()) { Utils.println("%   Creating a FALSE-branch leaf because wgtedCountFalseBranchPos = "  + Utils.truncate(wgtedCountFalseBranchPos, 1) + " < minPosWgt = "       + Utils.truncate(outerLoopState.getOverallMinPosWeight(), 1)); }
                                    else if (goodEnoughFitFalseBranch) 									   		  { Utils.println("%   Creating a FALSE-branch leaf because good enough fit since score < " +  outerLoopState.maxAcceptableNodeScoreToStop); }
                                }

                                falseBranch = new TreeStructuredTheoryLeaf(wgtedCountFalseBranchPos, wgtedCountFalseBranchNeg, bestNode.getVarianceFalseBranch(), leaf, Example.makeLabel(falseBranchPosExamples));
                            } else {
                                // Have another learning task.
                                TreeStructuredTheoryInteriorNode newTreeNode = new TreeStructuredTheoryInteriorNode(wgtedCountFalseBranchPos, wgtedCountFalseBranchNeg, null, null, null);
                                TreeStructuredLearningTask       newTask     = new TreeStructuredLearningTask(      falseBranchPosExamples,   falseBranchNegExamples, newTreeNode);
                                // On the FALSE branch, we need to use the PARENT's node (since the latest node failed).  There should always be a parent, but play it safe here.
                                // NOTE: we need to get the parent in the TREE and not in the LearnOneClause search.  I.e., bestNode might have more than 1 literal!  So can't do bestNode.getParentNode().
                                // Also, need to get the TIME A TRUE BRANCH WAS TAKEN.
                                TreeStructuredTheoryInteriorNode parentOfCurrentNode = interiorNode.getLastParentOnTrueBranch(interiorNode);
                                SingleClauseNode parentSearchNode = (parentOfCurrentNode == null ? null : parentOfCurrentNode.getSearchNodeThatLearnedTheClause());
                                falseBranch = newTreeNode;
                                newTreeNode.setParent(interiorNode); // Need a back pointer in case we later make this interior node a leaf.
                                newTreeNode.setBoolPath(interiorNode.returnBoolPath()); newTreeNode.addToPath(false);// Set the path taken to this node

                                if (learnMultiValPredicates) {
                                	newTreeNode.setRegressionVectorIfLeaf(null);
                                } else {
                                	newTreeNode.setRegressionValueIfLeaf(meanFalse);
                                }
                                // Since elsewhere we negate the score, do so here as well.
                                Utils.println("%   Creating a FALSE-branch interior node with wgtedCountFalseBranchPos = " + Utils.truncate(wgtedCountFalseBranchPos, 1));
                                outerLoopState.addToQueueOfTreeStructuredLearningTasks(newTask, newTreeNode, parentSearchNode, -bestNode.getVarianceFalseBranch(true)); // We want to sort by TOTAL error, not AVERAGE.
                            }
                            interiorNode.setTreeForTrue( trueBranch);
                            interiorNode.setTreeForFalse(falseBranch);
                        }
                        else {
                            getStdILPtheory().addMainClause(newClause, innerLoopTask.getInlineManager()); // The inline manager probably has already been sent, but send it again anyway.
                            if (learnMLNTheory && !learningTreeStructuredTheory) {
                            	double reg = bestNode.mlnRegressionForTrue();
                            	Utils.println("Setting " + reg + " for " + newClause);
                            	int len = getStdILPtheory().getClauses().size();
                            	getStdILPtheory().getClauses().get(len-1).setWeightOnSentence(reg);
                            	// Update gradients
                            	for (Example eg : coveredPosExamplesThisCycle) {
									((RegressionRDNExample)eg).setOutputValue(((RegressionRDNExample)eg)
											.getOutputValue() - reg); 
								}
                            }
                        }

                        long end = System.currentTimeMillis();
                        if (learningTreeStructuredTheory) {
                            Utils.println("\n% Time for loop #" + getNumberOfCycles() + ": " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
                            Utils.println(  "% Internal node max length = " + getMaxNumberOfLiteralsAtAnInteriorNode());
                            Utils.println(  "% Max tree depth in lits   = " + getMaxTreeDepthInLiterals());
                            Utils.println(  "% Max tree depth in nodes  = " + getMaxTreeDepth());
                            Utils.println(  "% Max number of clauses    = " + maxNumberOfClauses);
                        }

						setFractionOfPosCovered((double) getNumberOfPosExamplesCovered() / (double) getNumberOfPosExamples());
						setFractionOfNegCovered((double) getNumberOfNegExamplesCovered() / (double) getNumberOfNegExamples());
						Utils.println("\n% On cycle #" + getNumberOfCycles()+ ", the best clause found is:");
						Utils.println("%      " + bestNode);
						Utils.println("% This clause covers " + coveredPosExamplesCount + " positive examples, of which " + newlyCoveredPosExamples + " are newly covered.");
						Utils.println("% It also covers "	  + coveredNegExamplesCount + " negative examples, of which " + newlyCoveredNegExamples + " are newly covered.");
						if (!learningTreeStructuredTheory) {
							Utils.println("% The current set of " + Utils.getSizeSafely(getStdILPtheory().getClauses()) + " best clauses covers "
										  + Utils.truncate(100 * getFractionOfPosCovered(), 1) + "% of the positive examples and "
										  + Utils.truncate(100 * getFractionOfNegCovered(), 1) + "% of the negatives." + "}");
						}
					} else {
						Utils.println(MessageType.ILP_INNERLOOP, "\n% No acceptable clause was learned on this cycle of the ILP inner loop (LearnOneClause).");
						Utils.println(MessageType.ILP_INNERLOOP,   "% The closest-to-acceptable node found (score = " + Utils.truncate(theGleaner.bestScoreRegardless, 4) + "):\n%  " + theGleaner.bestNodeRegardless);
						//     Utils.waitHere();

						if (learningTreeStructuredTheory) { // Need to make the current node a leaf.
                            TreeStructuredLearningTask currentTask = outerLoopState.getCurrentTreeLearningTask();
                            createTreeStructuredLearningTaskLeaf(currentTask);
                        }
                    }
                }

                // Increment clock time used.
                long clockTimeUsed = getClockTimeUsedInMillisec();
                clockTimeUsed += stopwatch.getTotalTimeInMilliseconds();
                setClockTimeUsedInMillisec(clockTimeUsed);


                if (learningTreeStructuredTheory) {
                    stoppedBecauseTreeStructuredQueueEmpty = outerLoopState.queueOfTreeStructuredLearningTasksIsEmpty();
                }

            } // End of WHILE

			Utils.println(MessageType.ILP_INNERLOOP, "\n% ******************************************\n");
			if (!innerLoopTask.regressionTask && getFractionOfPosCovered() >= minFractionOfPosCoveredToStop) {
				Utils.println(MessageType.ILP_INNERLOOP, "% Have stopped ILP's outer loop because have exceeded the minimal fraction ("
								+ minFractionOfPosCoveredToStop + ") of positive examples to cover.");
			} else {
                if (stoppedBecauseTreeStructuredQueueEmpty) {
                    Utils.println(MessageType.ILP_INNERLOOP, "%  Have stopped ILP's outer loop because the tree-structured queue is empty.");
                } else if (getNumberOfCycles() >= maxNumberOfCycles) {
                    Utils.println(MessageType.ILP_INNERLOOP, "% Have stopped ILP's outer loop because have reached the maximum number of iterations (" + maxNumberOfCycles + ").");
                } else if (getNumberOfLearnedClauses() >= maxNumberOfClauses) {
                    Utils.println(MessageType.ILP_INNERLOOP, "% Have stopped ILP's outer loop because have reached the maximum number of learned clauses (" + maxNumberOfClauses + ").");
                } else if (stoppedBecauseNoMoreSeedsToTry) {
                    Utils.println(MessageType.ILP_INNERLOOP, "% Have stopped ILP's outer loop because have run out of seed positive examples to try.");
                } else if (getTotal_nodesConsidered() >= max_total_nodesExpanded) {
                    Utils.println(MessageType.ILP_INNERLOOP, "% Have stopped ILP's outer loop because have reached the maximum number of nodes to consider.");
                } else if (getTotal_nodesCreated() >= max_total_nodesCreated) {
                    Utils.println(MessageType.ILP_INNERLOOP, "% Have stopped ILP's outer loop because have reached the maximum number of nodes to created.");
                } else if (getClockTimeUsedInMillisec() >=  getMaximumClockTimeInMillisec()) {
                    Utils.println(MessageType.ILP_INNERLOOP, "%  Have stopped ILP's outer loop because have reached the maximum clock time.");
                }
            }
			Utils.println(MessageType.ILP_INNERLOOP, "\n% ******************************************");

			if (learningTreeStructuredTheory ) {
                // May have stopped for reasons other than the queue is empty.  In that case, need to convert all pending nodes to leaves.
                while (!outerLoopState.queueOfTreeStructuredLearningTasksIsEmpty()) {
                    createTreeStructuredLearningTaskLeaf(outerLoopState.popQueueOfTreeStructuredLearningTasks());
                }
            }

            if (holdBodyModes != null) { innerLoopTask.setBodyModes(holdBodyModes); holdBodyModes = null; }
            Theory finalTheory = produceFinalTheory();

            innerLoopTask.fireOuterLoopFinished(this);

            return finalTheory;

        }
        else if (action == ILPSearchAction.SKIP_ITERATION) {
            Utils.println("ILPSearchListener skipped outer-loop execution.");
            return null;
        }
        else {
            Utils.println("ILPSearchListener terminated outer-loop execution.");
            throw new SearchInterrupted("ILPSearchListener terminated outer-loop execution.");
        }
	}


	private void createTreeStructuredLearningTaskLeaf(TreeStructuredLearningTask currentTask) {
		Term val = null;
			if (currentTask.getNode() != null) {
				if (isLearnMultiValPredicates()) {
					val = createLeafNodeFromCurrentExamples(currentTask.getNode().getRegressionVectorIfLeaf());
				} else {
					val = createLeafNodeFromCurrentExamples(currentTask.getNode().getRegressionValueIfLeaf());
				}
			} else {
				Utils.error("task is not interior node!!");
			}
		TreeStructuredTheoryLeaf leaf = new TreeStructuredTheoryLeaf(currentTask.getNode().getWeightedCountOfPositiveExamples(),
																	 currentTask.getNode().getWeightedCountOfNegativeExamples(),
																	 computeVarianceOverTheseExamples( currentTask.getPosExamples()),
																	 val,
																	 Example.makeLabel(currentTask.getPosExamples()));
		// The parent had been expecting an interior node, so need to do some surgery.
		TreeStructuredTheoryNode node   = currentTask.getNode();
		TreeStructuredTheoryInteriorNode parent = node.getParent();
		if (parent == null) {
			outerLoopState.getTreeBasedTheory().setRoot(leaf);
		} else {
			Utils.println("Created a leaf under " + parent.getNodeTest());
			parent.changeChild(node, leaf);
			leaf.setParent(parent);
		}
	}

   private Term createLeafNodeFromCurrentExamples(double value) {
	   return innerLoopTask.stringHandler.getNumericConstant(value);
   }
   private Term createLeafNodeFromCurrentExamples(double[] value) {
	   List<Term> terms = new ArrayList<>();
	   for (double val : value) {
		terms.add(innerLoopTask.stringHandler.getNumericConstant(val));
	   }
	   return innerLoopTask.stringHandler.getConsCellFromList(terms);
   }

	private double computeVarianceOverTheseExamples(Collection<Example> currentExamples) {
		if (innerLoopTask.regressionTask) {

			if (Utils.getSizeSafely(currentExamples) < 1) {
				Utils.error("Should not reach here with ZERO examples!");
				return -1;
			}
			
			if (learnMultiValPredicates) {
				VectorStatistics vecStats = new VectorStatistics();
				if (currentExamples != null) for (Example ex : currentExamples) {
					vecStats.addVector(VectorStatistics.scalarProduct(((RegressionExample) ex).getOutputVector(), 
																		ex.getWeightOnExample()));
				}
				return vecStats.getVariance();
			}
			// Compute the mean value over all the (weighted) examples.
			double totalOfOutputValues  = 0.0;
			double totalSquaredOfOutput = 0.0;
			double weightedCount        = 0.0;
			if (currentExamples != null) for (Example ex : currentExamples) {
				double output = ex.getWeightOnExample() * ((RegressionExample) ex).getOutputValue();
				totalOfOutputValues  += output; 
				totalSquaredOfOutput += output * output;
				weightedCount        += ex.getWeightOnExample();
			}
			
			double result = (weightedCount <= 0.0 ? 0.0
					          : (    totalSquaredOfOutput / weightedCount)
						          - ((totalOfOutputValues  / weightedCount * totalOfOutputValues / weightedCount)));
			// Be robust to numeric errors.
			return Math.max(result, 0.0);
		}
		// Else return -1 to save this is not relevant (though could compute variance for the binomial distribution).
		return -1;
   }

	/* Resets the state of the search from the beginning.
	 *
	 * This should reset the state of both the outer and inner loop
	 * so that a new search can be started.
	 */
	public void resetAll() {
        innerLoopTask.resetAll();  // Clean up the inner loop in case we are starting a new fold...
        outerLoopState.clearAll();
        innerLoopTask.stringHandler.resetVarCounters();

        setStdILPtheory(new Theory(innerLoopTask.stringHandler, null, innerLoopTask.getInlineManager()));
        setCoveredPosExamples(new HashSet<>());
        setCoveredNegExamples(new HashSet<>());
        setNumberOfCycles(0);
        setNumberOfLearnedClauses(0);
        setNumberOfPosExamplesCovered(0);  // These are normal (ie, UNweighted) counts.  Wgt'ing of examples happens when they are covered (so the next round they can count 1.0 [fully], 0.0 [not at all], or somewhere in between).
        setNumberOfNegExamplesCovered(0);
        setFractionOfPosCovered(0.0);
        setTotal_nodesConsidered(0);
        setTotal_nodesCreated(0);
        setTotal_nodesNotAddedToOPENsinceMaxScoreTooLow(0);
        setTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow(0);
        setTotal_countOfPruningDueToVariantChildren(0);
        clearSeedPosExamplesUsed();
        clearSeedNegExamplesUsed();
        setClockTimeUsedInMillisec(0);

        if (learningTreeStructuredTheory) {
        	TreeStructuredTheoryInteriorNode newTreeNode = new TreeStructuredTheoryInteriorNode(innerLoopTask.getTotalPosWeight(), innerLoopTask.getTotalNegWeight(), null, null, null);
        	TreeStructuredLearningTask         firstTask = new TreeStructuredLearningTask(      innerLoopTask.getPosExamples(),    innerLoopTask.getNegExamples(), newTreeNode);
        	TreeStructuredTheory         treeBasedTheory = new TreeStructuredTheory(innerLoopTask.stringHandler, getTargetLiteral(), newTreeNode);
        	newTreeNode.setLevel(0);
        	outerLoopState.setTreeBasedTheory(treeBasedTheory);
        	outerLoopState.setOverallMinPosWeight(innerLoopTask.getMinPosCoverage()); // We want to keep this constant for all the recursive tree-building calls.
        	outerLoopState.addToQueueOfTreeStructuredLearningTasks(firstTask, newTreeNode, null, Double.MAX_VALUE);
        	// Set the acceptable score based on variance at root
        	double totalVariance = firstTask.getVariance();
        	Utils.println("Variance:" + totalVariance);
        	setMaxAcceptableNodeScoreToStop(Math.min(getMaxAcceptableNodeScoreToStop(), totalVariance*0.25));
        	Utils.println("Set score:" + getMaxAcceptableNodeScoreToStop());
        }
    }
    
    private Literal getTargetLiteral() {
    	List<Literal> targets = innerLoopTask.targets;
    	
    	if (Utils.getSizeSafely(targets) == 1) { return targets.get(0); }
    	Utils.error("Have too many/few (" + Utils.getSizeSafely(targets) + ") targets (should have exactly one): " + targets); 
    	return null;
    }

    public void initialize(boolean creatingCompoundFeaturesOnly) throws SearchInterrupted { // Pull this out from the constructor so that the caller can set some globals in innerLoopTask after that instance is created.
    	
		// All the stuff that used to be here was moved to resetAll()...
    	
        innerLoopTask.initialize(creatingCompoundFeaturesOnly);
        // Calling it here as one might be setting the parameters to initial values.
    	overwriteParametersFromBK();
	}
    
    private void overwriteParametersFromBK() {
		////////////////////////////////////////////////////////
		// Set parameters using setParams:
		////////////////////////////////////////////////////////
		String lookup;
		if ((lookup =  innerLoopTask.getStringHandler().getParameterSetting("maxNodesToConsider")) != null) {
			innerLoopTask.setMaxNodesToConsider(Integer.parseInt(lookup));
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("maxNodesToCreate")) != null) {
			innerLoopTask.setMaxNodesToCreate(Integer.parseInt(lookup));
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("maxTreeDepth")) != null) {
			setMaxTreeDepth(Integer.parseInt(lookup));
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("clauseLength")) != null) {
			setMaxTreeDepthInLiterals(Integer.parseInt(lookup));
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("nodeSize")) != null) {
			setMaxNumberOfLiteralsAtAnInteriorNode(Integer.parseInt(lookup));
			innerLoopTask.maxBodyLength = getMaxNumberOfLiteralsAtAnInteriorNode();
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("numOfClauses")) != null) {
			maxNumberOfClauses = Integer.parseInt(lookup);
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("numOfCycles")) != null) {
			maxNumberOfCycles = Integer.parseInt(lookup);
		}
        if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("maxScoreToStop")) != null) {
			setMaxAcceptableNodeScoreToStop(Double.parseDouble(lookup));
		}
		
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("minPosCoverage")) != null) {
			innerLoopTask.setMinPosCoverage(Double.parseDouble(lookup));
		}

	}		

    // TODO - put all this RDN stuff in a subclass of ILPouterLoop.
    public  void setLearnMLNTheory(boolean val) {
    	learnMLNTheory = val;
    	innerLoopTask.setMlnRegressionTask(val);
    }
    
    public  void setLearnOCCTree(boolean val) {
    	innerLoopTask.oneClassTask = val;
    	learnOCCTree = val;
    }

    public void setFlagsForRegressionTask(boolean notLearnTrees) {
    	innerLoopTask.regressionTask           = true;
		innerLoopTask.stopIfPerfectClauseFound = false;
		
		innerLoopTask.stopWhenUnacceptableCoverage = false;
		learningTreeStructuredTheory           = !notLearnTrees;
		innerLoopTask.setIsaTreeStructuredTask(!notLearnTrees); // TODO - couple this with setting the above (via a setter)
    }
    
    public void morphToRDNRegressionOuterLoop(double all_pos_wt, double all_neg_wt, double ratioOfNegToPositiveEx, 
    		double samplePositiveProb, boolean notLearnTrees, boolean reweighExs, boolean areRegressionEgs) {
    	setFlagsForRegressionTask(notLearnTrees);
		
		List<Example>  origPosExamples = getPosExamples();
		List<Example> positiveExamples = new ArrayList<>(4);
		int        numbOrigPosExamples = Utils.getSizeSafely(origPosExamples);
		int		   numbNewPosExamples  = (int) samplePositiveProb * numbOrigPosExamples;
		
		// Less than zero means we dont want to sample.
		if (numbNewPosExamples <= 0) {
			numbNewPosExamples = numbOrigPosExamples;
		}

		// TODO(@hayesall): integer division that returning a double. This is likely a bug.
		double	   reweighPositiveExamples = numbOrigPosExamples / numbNewPosExamples;
		
		int countOfPosKept = 0;
        // TODO integrate this better if we decide to keep it.
        // TODO - should this also be sampling with replacement of the expected number to collect?  Correctly no duplicates, but number collected can vary.
        if (numbOrigPosExamples > 0) for (Example eg : origPosExamples) { // Should we ignore this positive example?
            if (samplePositiveProb >= 0 && samplePositiveProb < 1 && Utils.random() > samplePositiveProb) {	continue; }
            double outputVal = all_pos_wt;
            if (areRegressionEgs) {
                if (eg instanceof RegressionExample) {
                    outputVal = ((RegressionExample)eg).getOutputValue();
                } else {
                    Utils.waitHere("Expected regression examples for learning regression trees");
                }
            }
            RegressionRDNExample regEx = new RegressionRDNExample(eg.getStringHandler(), eg.extractLiteral(),
                                                                  outputVal, eg.provenance, eg.extraLabel, true);
            if (areRegressionEgs) {
                regEx.originalRegressionOrProbValue = regEx.getOutputValue();
            }
            if (reweighExs) {
            regEx.setWeightOnExample(eg.getWeightOnExample() * reweighPositiveExamples);

            }
            positiveExamples.add(regEx);
            countOfPosKept++;
        }

        // TODO - Handle skew in both directions.
		// Now move the negative examples to positives (since for regression all examples are positives).
		List<Example> origNegExamples = getNegExamples();
		int       numbOrigNegExamples = Utils.getSizeSafely(origNegExamples);
		double   probOfSelectingNegEx = (ratioOfNegToPositiveEx * (double) countOfPosKept)      / (double) numbOrigNegExamples; // Use the NEW number of positive examples, NOT the original!
		
		// If #positives = 0, we do need few negative example but not all. 
		if (countOfPosKept == 0) {
			probOfSelectingNegEx = ratioOfNegToPositiveEx / (double) numbOrigNegExamples;
		}
		int           countOfNegsKept = 0;	
		double	   reweighNegativeExamples = 1 / probOfSelectingNegEx;
		if (probOfSelectingNegEx >= 1 || probOfSelectingNegEx <= 0) {
			reweighNegativeExamples = 1;
		}

		/*  TUSHAR - I (JWS) replaced this (above) with random sampling with replacement.  Will be faster if we have a lot of negatives (though that probably doesn't matter much),
		 *           but maybe more importantly we'll always get the same number of negatives.
		 */
		if (numbOrigNegExamples > 0) for (Example eg : origNegExamples) {
			if (probOfSelectingNegEx >= 0 && probOfSelectingNegEx < 1 && Utils.random() > probOfSelectingNegEx)	{ continue; }
			double outputVal = all_neg_wt;
			if (areRegressionEgs) {
				if (eg instanceof RegressionExample) {
					outputVal = ((RegressionExample)eg).getOutputValue();
				}
			}
			RegressionRDNExample regEx = new RegressionRDNExample(eg.getStringHandler(), eg.extractLiteral(),
																  outputVal, eg.provenance, eg.extraLabel, false);
			if (areRegressionEgs) {
				regEx.originalRegressionOrProbValue = regEx.getOutputValue();
			}
			if (reweighExs) {
				regEx.setWeightOnExample(eg.getWeightOnExample() * reweighNegativeExamples);

			}
			positiveExamples.add(regEx);
			countOfNegsKept++;
		}

		Utils.println("% Kept " + "" + Utils.comma(countOfPosKept) + " of the " + Utils.comma(numbOrigPosExamples) + " positive examples.");
		Utils.println("% Kept " + "" + Utils.comma(countOfNegsKept) + " of the " + Utils.comma(numbOrigNegExamples) + " negative examples.");
		setPosExamples(positiveExamples);
		setNegExamples(new ArrayList<>(0));
    }

	private boolean isLearnMultiValPredicates() {
		return learnMultiValPredicates;
	}

	public void setLearnMultiValPredicates(boolean learnMultiValPredicates) {
		this.learnMultiValPredicates = learnMultiValPredicates;
		innerLoopTask.setLearnMultiVal(learnMultiValPredicates);
	}
	private Theory produceFinalTheory() {
		// TODO allow theories to come from some covering algorithm, possibly based on all the Gleaners.		
		Theory result;
		if (learningTreeStructuredTheory) {
			// Note: this code assumes all the heads have the same arguments, other than the last variables that stores the numeric answer. 
			// The renameAllVariables() is only used to make the tree-structured theory a bit more human readable.
			result = outerLoopState.getTreeBasedTheory().renameAllVariables().convertToStandardTheory(innerLoopTask.getInlineManager()).renameAllClausesWithUniqueBodyVariables(); // Cleanup the variable names and then convert to Horn clauses.

		} else {
			result = getStdILPtheory(); // Is in-lining properly handled here?  Presumably this should happen when clauses are learned?
			if (learnMLNTheory) {
				Utils.println("adding regression values");
				for (Clause cl : result.getClauses()) {
					Term leafValue =  innerLoopTask.stringHandler.getNumericConstant(cl.getWeightOnSentence());
					Utils.println("Added " + cl.getWeightOnSentence() + " to " + cl);
					Literal      headCopy = cl.getDefiniteClauseHead();
					List<String> argNames = headCopy.getArgumentNames();
					if (argNames != null) {
						headCopy.addArgument(leafValue, "OutputVarTreeLeaf");
					} else {
						headCopy.addArgument(leafValue);
					}
				}
				
			}
		}
		
		if (result == null) { return null; }
		
		if (!prefixForExtractedRules.equals("") || !postfixForExtractedRules.equals("")) { 
			Literal target = getTargetLiteral();
			assert target != null;
			if (!target.predicateName.isaTemporaryName(target.getArity() + (innerLoopTask.regressionTask ? 1 : 0))) { // Possibly add 1 since we add the output value for regression tasks.
				 target.predicateName.addTemporary(    target.getArity() + (innerLoopTask.regressionTask ? 1 : 0)); 
			}
			result.addPreAndPostfixToTemporaryNames(prefixForExtractedRules, postfixForExtractedRules); 
		}
		// Set inline mgr before simplifying
		result.setInlineHandler(this.innerLoopTask.getInlineManager());
		if (learningTreeStructuredTheory) { // Need to wait until any pre/post-fix stuff has been applied.
			return ((TreeStructuredTheory) result).createFlattenedClauses().simplify();
		}
		return result.simplify();
	}

    private void clearSeedPosExamplesUsed() {
        outerLoopState.clearSeedPosExamplesUsed();
    }

    private void clearSeedNegExamplesUsed() {
        outerLoopState.clearSeedNegExamplesUsed();
    }

    private void setGleaner(Gleaner gleaner) {
    	Gleaner oldGleaner = (Gleaner) innerLoopTask.getGleaner(); // cth updated to pass structured output flag
        innerLoopTask.setGleaner(gleaner);
        
    	if ( gleaner == null ) { return; }
        gleaner.setILPouterLooper(this);	
      	if (oldGleaner != null) { gleaner.setUseStructuredOutput(oldGleaner.getUseStructuredOutput()); }
        // cth updated to make structured output flag (for visualizer) persistent, based on notes from Jude
        if (oldGleaner != null) { gleaner.setUseStructuredOutput(oldGleaner.getUseStructuredOutput()); }
		// These two hold on to gleaners when we do flip-flops.  The gleaner is 'really' stored in LearnOneClause.
		Gleaner gleanerFlipFlopped = new Gleaner();
      	gleanerFlipFlopped.setILPouterLooper(this); 
      	gleanerFlipFlopped.setUseStructuredOutput(gleaner.getUseStructuredOutput());
    }

    public boolean proveExample(Clause clause, Example ex) {
        return innerLoopTask.proveExample(clause, ex);
    }

    private void setTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow(int total_nodesRemovedFromOPENsinceMaxScoreNowTooLow) {
        outerLoopState.setTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow(total_nodesRemovedFromOPENsinceMaxScoreNowTooLow);
    }

	private void setTotal_nodesNotAddedToOPENsinceMaxScoreTooLow(int total_nodesNotAddedToOPENsinceMaxScoreTooLow) {
        outerLoopState.setTotal_nodesNotAddedToOPENsinceMaxScoreTooLow(total_nodesNotAddedToOPENsinceMaxScoreTooLow);
    }

	private void setTotal_nodesCreated(int total_nodesCreated) {
        outerLoopState.setTotal_nodesCreated(total_nodesCreated);
    }

	private void setTotal_nodesConsidered(int total_nodesConsidered) {
        outerLoopState.setTotal_nodesConsidered(total_nodesConsidered);
    }

	private void setTotal_countOfPruningDueToVariantChildren(int total_countOfPruningDueToVariantChildren) {
        outerLoopState.setTotal_countOfPruningDueToVariantChildren(total_countOfPruningDueToVariantChildren);
    }

	private void setStdILPtheory(Theory stdILPtheory) {
        outerLoopState.setStdILPtheory(stdILPtheory);
    }

	private void setNumberOfPosExamplesCovered(int numberOfPosExamplesCovered) {
        outerLoopState.setNumberOfPosExamplesCovered(numberOfPosExamplesCovered);
    }

	private void setNumberOfNegExamplesCovered(int numberOfNegExamplesCovered) {
        outerLoopState.setNumberOfNegExamplesCovered(numberOfNegExamplesCovered);
    }

	private void setNumberOfLearnedClauses(int numberOfLearnedClauses) {
        outerLoopState.setNumberOfLearnedClauses(numberOfLearnedClauses);
    }

	private void setNumberOfCycles(int numberOfCycles) {
        outerLoopState.setNumberOfCycles(numberOfCycles);
    }

    private void setFractionOfPosCovered(double fractionOfPosCovered) {
        outerLoopState.setFractionOfPosCovered(fractionOfPosCovered);
    }

	private void setFractionOfNegCovered(double fractionOfNegCovered) {
        outerLoopState.setFractionOfNegCovered(fractionOfNegCovered);
    }

	private void setCoveredPosExamples(Collection<Example> coveredPosExamples) {
        outerLoopState.setCoveredPosExamples(coveredPosExamples);
    }

	private void setCoveredNegExamples(Collection<Example> coveredNegExamples) {
        outerLoopState.setCoveredNegExamples(coveredNegExamples);
    }

	private int getTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow() {
        return outerLoopState.getTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow();
    }

    private int getTotal_nodesNotAddedToOPENsinceMaxScoreTooLow() {
        return outerLoopState.getTotal_nodesNotAddedToOPENsinceMaxScoreTooLow();
    }

    int getTotal_nodesCreated() {
        return outerLoopState.getTotal_nodesCreated();
    }

    int getTotal_nodesConsidered() {
        return outerLoopState.getTotal_nodesExpanded();
    }

	private int getTotal_countOfPruningDueToVariantChildren() {
        return outerLoopState.getTotal_countOfPruningDueToVariantChildren();
    }

    private Theory getStdILPtheory() {
        return outerLoopState.getStdILPtheory();
    }

    private int getNumberOfPosExamplesCovered() {
        return outerLoopState.getNumberOfPosExamplesCovered();
    }

    public int getNumberOfPosExamples() {
        return innerLoopTask.getNumberOfPosExamples();
    }

	private int getNumberOfNegExamplesCovered() {
        return outerLoopState.getNumberOfNegExamplesCovered();
    }

    public int getNumberOfNegExamples() {
        return innerLoopTask.getNumberOfNegExamples();
    }

	private int getNumberOfLearnedClauses() {
        return outerLoopState.getNumberOfLearnedClauses();
    }

	private int getNumberOfCycles() {
        return outerLoopState.getNumberOfCycles();
    }

    private double getFractionOfPosCovered() {
        return outerLoopState.getFractionOfPosCovered();
    }

	private double getFractionOfNegCovered() {
        return outerLoopState.getFractionOfNegCovered();
    }

	private Collection<Example> getCoveredPosExamples() {
        return outerLoopState.getCoveredPosExamples();
    }

    private Collection<Example> getCoveredNegExamples() {
        return outerLoopState.getCoveredNegExamples();
    }

	public void setOverallMinPosWeight(double wgt) {
        outerLoopState.setOverallMinPosWeight(wgt);
    }

    public String getWorkingDirectory() {
        return workingDirectory;
    }

    private void setWorkingDirectory(String workingDirectory) {
        this.workingDirectory = workingDirectory;
    }

    private void setRRR(boolean useRRR) {
        outerLoopState.setRRR(useRRR);
    }

    private boolean isRRR() {
        return outerLoopState.isRRR();
    }

    /* Sets the PosExamples to use for the search.
     *
     * This is just a convenience method.  The list is actually stored in the LearnOneClause object.
     *
     * @param posExamples the posExamples to set
     */
    public void setPosExamples(List<Example> posExamples) {
        innerLoopTask.setPosExamples(posExamples);
    }

    /* Sets the NegExamples to use for the search.
     *
     * This is just a convenience method.  The list is actually stored in the LearnOneClause object.
     *
     * @param negExamples the negExamples to set
     */
    public void setNegExamples(List<Example> negExamples) {
        innerLoopTask.setNegExamples(negExamples);
    }

    /* Returns the PosExamples to use for the search.
     *
     * This is just a convenience method.  The list is actually stored in the LearnOneClause object.
     */
    public List<Example> getPosExamples() {
        return innerLoopTask.getPosExamples();
    }

    /* Returns the NegExamples to use for the search.
     *
     * This is just a convenience method.  The list is actually stored in the LearnOneClause object.
     */
    public List<Example> getNegExamples() {
        return innerLoopTask.getNegExamples();
    }


    private Set<Example> getNegExamplesUsedAsSeeds() {
        return outerLoopState.getNegExamplesUsedAsSeeds();
    }

	private Set<Example> getSeedPosExamplesUsed() {
        return outerLoopState.getSeedPosExamplesUsed();
    }

	private Set<Example> getSeedNegExamplesUsed() {
        return outerLoopState.getSeedNegExamplesUsed();
    }


    public void setMaximumClockTimeInMillisec(long maximumClockTime) {
    	if (maximumClockTime < 0) { Utils.waitHere("setMaximumClockTime = " + maximumClockTime); }
        outerLoopState.setMaximumClockTimeInMillisec(maximumClockTime);
    }

    private void setClockTimeUsedInMillisec(long clockTimeUsed) {
        outerLoopState.setClockTimeUsedInMillisec(clockTimeUsed);
    }

    private long getMaximumClockTimeInMillisec() {
        return outerLoopState.getMaximumClockTimeInMillisec();
    }

    private long getClockTimeUsedInMillisec() {
        return outerLoopState.getClockTimeUsedInMillisec();
    }

	private long getTimeAvailableInMillisec() {
       return getMaximumClockTimeInMillisec() == Long.MAX_VALUE ? Long.MAX_VALUE : Math.max(0, getMaximumClockTimeInMillisec() - getClockTimeUsedInMillisec());
    }

	public void setMaxAcceptableNodeScoreToStop(double score) {
    	outerLoopState.maxAcceptableNodeScoreToStop = score;
    }

    public double getMaxAcceptableNodeScoreToStop() {
    	return outerLoopState.maxAcceptableNodeScoreToStop;
    }

	public int getMaxNumberOfLiteralsAtAnInteriorNode() {
		return maxNumberOfLiteralsAtAnInteriorNode;
	}

	public void setMaxNumberOfLiteralsAtAnInteriorNode(int maxNumberOfLiteralsAtAnInteriorNode) {
		this.maxNumberOfLiteralsAtAnInteriorNode = Math.max(1, maxNumberOfLiteralsAtAnInteriorNode);
	}

	public int getMaxTreeDepthInLiterals() {
		return maxTreeDepthInLiterals;
	}

	public void setMaxTreeDepthInLiterals(int maxTreeDepthInLiterals) {
		this.maxTreeDepthInLiterals = Math.max(1, maxTreeDepthInLiterals);
	}

	public void setPrefixForExtractedRules(String prefixForExtractedRules) {
		this.prefixForExtractedRules = prefixForExtractedRules;
	}

	public void setPostfixForExtractedRules(String postfixForExtractedRules) {
		this.postfixForExtractedRules = postfixForExtractedRules;
	}

	public int getMaxTreeDepth() {
		return maxTreeDepthInInteriorNodes;
	}

	public void setMaxTreeDepth(int maxTreeDepth) {
		this.maxTreeDepthInInteriorNodes = Math.max(1, maxTreeDepth);
	}

}
