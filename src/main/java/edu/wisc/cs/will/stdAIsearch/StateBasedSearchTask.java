package edu.wisc.cs.will.stdAIsearch;

import edu.wisc.cs.will.Utils.Utils;

import java.util.List;


// TODO sampling search (eg, walksat)
// TODO how would the case of using a small dataset during initial clause generation work, with a larger one later?  look at nodesExplored, etc.
// TODO implement code for dealing with CLOSED (ie, how to do equals)
// TODO implement iterativeDeepening that works with ANY search

/*
 * The specification of a state-based search task.
 * 
 * @param <T> Class of the search nodes.
 * @author shavlik
 */
public class StateBasedSearchTask<T extends SearchNode> {
	protected String taskName = "unnamedTask"; // Used in println's to clarify which task is being discussed.

    private SearchStrategy strategy;

    public ScoringFunction scorer;

    public ChildrenNodeGenerator childrenGenerator;

    public Initializer initializer;

    public EndTest terminator;

    public OpenList<T> open;

    public ClosedList closed;

    final boolean    addNodesToClosedListWhenCreated = true;

    public SearchMonitor searchMonitor;

    private T lastNodeVisited;

    private SearchNode bestNodeVisited;

    final boolean stopWhenMaxNodesCreatedReached = true;

    final boolean stopWhenMaxNodesCreatedThisIterationReached = true;

    private int maxNodesToConsider = -1;

    private int maxNodesToCreate = -1;

    public int maxSearchDepth = java.lang.Integer.MAX_VALUE;

    public int beamWidth = -1;

    final double minAcceptableScore = Double.NEGATIVE_INFINITY;

    final boolean allowToTieMinAcceptableScore = true;

    final boolean inOpenListPutNewTiesInFront = false;

    private final boolean useIterativeDeepeningDepth = false;

    public boolean continueTheSearch = true;

    private int maxNodesToConsiderPerIteration = -1;

    /*
     * Allow, per iterative-deepening cycle or in a random-sampling search that
     * does some local heuristic search, a max on the number of nodes CREATED
     * (non-pos values mean infinity). The default is -1.
     */
    private int maxNodesToCreatePerIteration = -1;

    /*
     * If 0, no comments. 
     * If verbosity=1, minimal comments. 
     * If verbosity=2, moderate comments. 
     * If verbosity=3, many comments. 
     * If verbosity>3, maximal comments. 
     * The default is 0.
     */
    public int verbosity = 0;

    protected int nodesConsidered = 0;

    protected int nodesCreated = 0;

    int nodesConsideredThisIteration = 0;

    int nodesCreatedThisIteration = 0;

    private long maximumClockTimePerIterationInMillisec = Integer.MAX_VALUE; // Units are milliseconds.

    private long iterationStartTimeInMillisec = -1;

    private boolean initialized = false;

    /* If true, the open list is not cleared at the end of a search.
     *
     * Since the open list is not cleared, it is possible to continue the
     * search after an answer is found via the continueSearch() method.
     */
    protected boolean redoable = false;


    protected boolean      discardIfBestPossibleScoreOfNodeLessThanBestSeenSoFar = false; // If true, do a branch-and-bound search.
    double       bestScoreSeenSoFar                                    = Double.NEGATIVE_INFINITY;
    public    int          nodesNotAddedToOPENsinceMaxScoreTooLow                = 0;
    public    int          nodesRemovedFromOPENsinceMaxScoreNowTooLow            = 0;
	
    /*
     * Default constructor. Does nothing.
     */
    protected StateBasedSearchTask() {
    }

    /*
     * Initializes this state-based search task.
     * 
     * @param initializer
     *                The creator of the open list.
     * @param terminator
     *                The controller of search termination/satisfaction.
     *                Optional (may be null).
     * @param searchMonitor
     *                The monitor of the search. Optional (may be null). If
     *                null, a search monitor is created.
     * @param strategy
     *                How to search. Optional (may be null). If null, a
     *                best-first search is created.
     * @param scorer
     *                The scoring function. Optional (may be null).
     * @param childrenGenerator
     *                The generator of the successor search nodes.
     * @param closed
     *                The list of nodes already searched. Optional (may be
     *                null).
     */
    protected void initalizeStateBasedSearchTask(Initializer initializer,
                                                 EndTest terminator, SearchMonitor searchMonitor,
                                                 SearchStrategy strategy, ScoringFunction scorer,
                                                 ChildrenNodeGenerator childrenGenerator, ClosedList closed) {
        // TODO convert errors to exceptions

        // First create defaults if necessary and where possible.  Otherwise complain if something is mandatory.
        if (strategy == null) {
            strategy = new BreadthFirstSearch();
            Utils.waitHere("Breadth-first search being used since no search strategy was provided.");
        }
        if (searchMonitor == null) {
            searchMonitor = new SearchMonitor(this);
        }
        if (initializer == null) {
            Utils.error("A method that initiates OPEN must be provided to initalizeStateBasedSearchTask().");
        }
        if (childrenGenerator == null) {
            Utils.error("A method that generates child nodes must be provided to initalizeStateBasedSearchTask().");
        }

        this.initializer        = initializer;
        this.terminator        = terminator;
        this.searchMonitor     = searchMonitor;
        this.strategy          = strategy;
        this.scorer            = scorer;
        this.childrenGenerator = childrenGenerator;
        this.closed            = closed;

        initializer.setSearchTask(this);
        searchMonitor.setSearchTask(this);
        strategy.setSearchTask(this);

        childrenGenerator.setSearchTask(this);

        if (open == null) { open = new OpenList<>(this); }
    }
    
    /*
     * Clears and resets basic search information such as counters.
     */
    private void clearAnySavedBasicSearchInformation(boolean withinInterativeDeepening) {
        if (withinInterativeDeepening) {
            nodesConsideredThisIteration = 0;
            nodesCreatedThisIteration    = 0;
        }
        else {
            nodesConsidered = 0; // Clear some counters, etc.
            nodesCreated    = 0;
            lastNodeVisited = null; // Allow this to persist across iterative deep. in case a future use arises.

            bestScoreSeenSoFar = Double.NEGATIVE_INFINITY;
            nodesNotAddedToOPENsinceMaxScoreTooLow     = 0;
            nodesRemovedFromOPENsinceMaxScoreNowTooLow = 0;

        }
        continueTheSearch = true;
    }

    /*
     * Some applications built on top of this general search algorithm might be
     * extra "markers" of various sorts in OPEN. This method allows them to
     * cleanup OPEN should they wish to do so. Does nothing.
     */
    public void cleanOpen() {
    }


    /* Resets the search space completely, including the open and closed list.
     *
     * This method resets the complete search state.  If you are doing iterative deepening
     * or rrr, you probably don't want to use this.  Use the somewhat confusingly named resetAll
     * which leaves the open and closed lists intact.
     */
    public void resetAllForReal() {
        resetAll(false);
        clearClosedList();
        clearOpenList();
    }
    
    private void clearOpenList() {
    	if (open != null) {
            open.clear();
        }
    }

    private void initialize() throws SearchInterrupted {
        if (!initialized) {
            if (closed != null) {
                closed.emptyClosedList();
            } // Should we allow closed lists to persist across multiple iterations?  Generally won't want to do so.  Hence another boolean would be needed.
            if (open == null) {
                open = new OpenList<>(this);
            }
            initializer.initializeOpen(open); // Do this AFTER clearing CLOSED.
            initialized = true;
        }
    }
    
    private void clearClosedList() {
        if (closed != null) {
            closed.emptyClosedList();
        }   	
    }
    

    /*
     * Resets all the search state.
     */
    private void resetAll(boolean withinInterativeDeepening) {
        clearAnySavedBasicSearchInformation(withinInterativeDeepening); // Explicitly call this rather than counting on subclasses to call super().
        if (terminator        != null) { terminator.clearAnySavedInformation();    }
        if (childrenGenerator != null) { childrenGenerator.clearAnySavedInformation(); }

        initialized = false;
    }

    /*
     * Conducts the search specified by this search task. All the search state
     * is reset before the search begins.
     */
    public SearchResult performSearch() throws SearchInterrupted {
        
        resetAll(false);
        
        if (useIterativeDeepeningDepth) { // to do: should max nodes by PER iter. deep. run?  Probably, but then too many params?
            int holdMaxSearchDepth = maxSearchDepth;
            boolean goalFound = false;
            SearchResult result = null;

            maxSearchDepth = 0;
            while (!goalFound && maxSearchDepth < holdMaxSearchDepth) {
                resetAll(true);
                result = performSearchIteration();
                if (result.goalFound()) { goalFound = true; }
                maxSearchDepth++;
            }
            maxSearchDepth = holdMaxSearchDepth;
            return result;
        }
		if (open == null) {
		    open = new OpenList<>(this);
		    initializer.initializeOpen(open);
		} // Do this here so that 'verbosity' can be set before OPEN is created.

		maxNodesToConsiderPerIteration = -1; // Don't want these playing a role in a non-iterative search.
		maxNodesToCreatePerIteration   = -1; // Don't want these playing a role in a non-iterative search.
		
		return performSearchIteration();
    }


    /*
     * Performs a basic search, that is, either not an iterative deepening
     * search or one iteration of an iterative deepening search.
     */
    private SearchResult performSearchIteration() throws SearchInterrupted { 
        initialize();

        return search();
    }
    
    public boolean isThereNotTimeLeft() {
    	if (maximumClockTimePerIterationInMillisec == Long.MAX_VALUE) { return false; }

        return (System.currentTimeMillis() - iterationStartTimeInMillisec >= maximumClockTimePerIterationInMillisec);
    }
    
    public String explainTimeLeft() {
    	if (maximumClockTimePerIterationInMillisec == Long.MAX_VALUE) { return "All the time in the world is left."; }

        return "Have spent " + Utils.convertMillisecondsToTimeSpan(System.currentTimeMillis() - iterationStartTimeInMillisec)
        		+ " but only have " + Utils.convertMillisecondsToTimeSpan(maximumClockTimePerIterationInMillisec);
    }

    private int countOfWarnings =   0;

    /* Performs that actual search loop.
     */
    private SearchResult search() throws SearchInterrupted {
        boolean done = false;

        iterationStartTimeInMillisec = System.currentTimeMillis();
        
        if (open.isEmpty() || !continueTheSearch) {
        	if (redoable) {
        		searchMonitor.searchResult = SearchMonitor.openBecameEmpty;
        	} else  {
        		Utils.waitHere("This search will never start for '" + taskName + "': continueTheSearch = " + continueTheSearch + ", |open| = " + Utils.comma(open));
        	}
        }

        while (continueTheSearch && !done && !open.isEmpty()) {
        	lastNodeVisited = open.popOpenList();

        	if (verbosity > 10) { Utils.println("% VISIT for '" + taskName  + "."); }

            // After this limit hit, be more terse in warnings.
            int maxWarnings = 100;
            if (getMaxNodesToConsider() > 0 && nodesConsidered >= getMaxNodesToConsider()) {
                done = true;
                if (countOfWarnings++ < maxWarnings) {
                	Utils.warning(        "#" + Utils.comma(countOfWarnings) + " TOO MANY NODES CONSIDERED (i.e., 'expanded') for '" + taskName + "': nodesConsidered = " + Utils.comma(nodesConsidered) + " and maxNodesToConsider = " + Utils.comma(getMaxNodesToConsider()) + ".");  // ; node = " + lastNodeVisited);
                } else {
                	Utils.println("Warning #" + Utils.comma(countOfWarnings) + " TOO MANY NODES CONSIDERED (i.e., 'expanded') for '" + taskName + "'.");
                }
                searchMonitor.searchEndedByMaxNodesConsidered(nodesConsidered);
            }

            if (isThereNotTimeLeft()) {
                done = true;
                if (countOfWarnings++ < maxWarnings) {
                    long currentTime = System.currentTimeMillis();
                  	Utils.warning(        "#" + Utils.comma(countOfWarnings) + " TOO MUCH TIME SPENT for '" + taskName + "': '" + Utils.convertMillisecondsToTimeSpan(currentTime - iterationStartTimeInMillisec) + "' vs. '" + Utils.convertMillisecondsToTimeSpan(maximumClockTimePerIterationInMillisec) + "'.");
                } else {
                  	Utils.println("Warning #" + Utils.comma(countOfWarnings) + " TOO MUCH TIME SPENT for '" + taskName + ".");
                }	
                searchMonitor.searchEndedByMaxTimeUsed();
            }

            // Some searches don't want to stop when reaching max nodes CREATED.  Instead, don't add any more children to OPEN.
            if (!done && getMaxNodesToCreate() > 0 && nodesCreated >= getMaxNodesToCreate()) {
                done = searchMonitor.searchReachedMaxNodesCreated(nodesCreated); // Since this setting of 'done' is conditional, make sure done=false when reaching here.
                if (done) {
                	if (countOfWarnings++ < maxWarnings) {
                    	Utils.warning(            "#" + Utils.comma(countOfWarnings) + " TOO MANY NODES CREATED for '" + taskName + "':  maxNodesToCreate = "      + Utils.comma(getMaxNodesToCreate())      + " vs nodesCreated = "   + Utils.comma(nodesCreated) + "."); // ; node = " + lastNodeVisited);
                	} else {
                    	Utils.println("\n% Warning #" + Utils.comma(countOfWarnings) + " TOO MANY NODES CREATED for '" + taskName + "'.");
                    }	
                }
            }

            if (useIterativeDeepeningDepth) {
                if (maxNodesToConsiderPerIteration > 0 && nodesConsideredThisIteration >= maxNodesToConsiderPerIteration) {
                    done = true;
                    searchMonitor.searchEndedByMaxNodesConsideredThisIteration(nodesConsideredThisIteration);
                }
                if (!done && maxNodesToCreatePerIteration > 0 && nodesCreatedThisIteration >= maxNodesToCreatePerIteration) {
                    done = searchMonitor.searchReachedMaxNodesCreatedThisIteration(nodesCreatedThisIteration); // Since this setting of 'done' is conditional, make sure done=false when reaching here.
                }
            }
            if (terminator != null && terminator.endSearch(lastNodeVisited)) {
                done = true;
                searchMonitor.searchEndedByTerminator();
                if (verbosity > 3) { Utils.warning("Search ended for '" + taskName + "' by terminator for some reason."); }
            }
            if (!done) {
                if (lastNodeVisited.depth < maxSearchDepth) {
                    List<T> children = childrenGenerator.collectChildren(lastNodeVisited);
                    if (verbosity > 1) {Utils.println("%  Add " + Utils.comma(children) + " to OPEN."); }
                    if (Utils.getSizeSafely(children) > 0) {

                        for (SearchNode searchNode : children) {
                            if ( bestNodeVisited == null || searchNode.score > bestNodeVisited.score ) {
                                bestNodeVisited = searchNode;
                            }
                        }

                        strategy.addChildrenToOpenList(open, children);
                    }
                } 
                else {
                	if (countOfWarnings++ < maxWarnings) {
                    	Utils.warning("Warning #" + Utils.comma(countOfWarnings) + " % Skipped expansion of first open node.  Maximum depth reached: node.depth = " + Utils.comma(lastNodeVisited.depth) + " vs maxSearchDepth = " + Utils.comma(maxSearchDepth) + "."); // ; node = " + lastNodeVisited);
                	} else {
                    	Utils.println("Warning #" + Utils.comma(countOfWarnings) + " % Skipped expansion of first open node.  Maximum depth reached for '" + taskName);
                    }
                    if (verbosity > -10) {
                        Utils.waitHere("Did you really want to hit the depth limit?");
                    }
                }
                
                if (verbosity > 2) { Utils.println("  task=" + taskName + "  |open| = " + open.size() + "  done=" + " continueTheSearch=" + continueTheSearch); }

                if (open.isEmpty()) {
                    done = true;
                    searchMonitor.searchEndedBecauseOPENbecameEmpty();
                } 
            }
            if (done && !redoable) {
            	open.clear(); // Even if we worried about getting the next solution (see TAW notes below), ok to clear here since we hit limits (which prevent spending time on more solutions).
            	if (closed != null) { closed.emptyClosedList(); } // Ditto.
            	if (verbosity > 2) { Utils.println("  task=" + taskName + ";  |open| = " + open.size() + ";  done=" + "; continueTheSearch=" + continueTheSearch + "."); } // "; node = " + lastNodeVisited); }
            } 
        }
        return searchMonitor.getSearchResult();
    }

    public void setMaximumClockTimePerIterationInMillisec(long maximumClockTimePerIterationInMilliseconds) {
        this.maximumClockTimePerIterationInMillisec = maximumClockTimePerIterationInMilliseconds;
    }

	public int getNodesConsidered() {
		return nodesConsidered;
	}

    public int getNodesCreated() {
		return nodesCreated;
	}

	public void setNodesCreated(int nodesCreated) {
		this.nodesCreated = nodesCreated;
	}

    public int getMaxNodesToConsider() {
        return maxNodesToConsider;
    }

    public void setMaxNodesToConsider(int maxNodesToConsider) {
        this.maxNodesToConsider = maxNodesToConsider;
    }

    public int getMaxNodesToCreate() {
        return maxNodesToCreate;
    }

    public void setMaxNodesToCreate(int maxNodesToCreate) {
        this.maxNodesToCreate = maxNodesToCreate;
    }

}
