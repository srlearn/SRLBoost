package edu.wisc.cs.will.stdAIsearch;

import edu.wisc.cs.will.Utils.Utils;

import java.io.IOException;
import java.io.Serializable;

/*
 * The job of this class is to keep track of a search and return the desired result at the end.
 * @author shavlik
 */
public class SearchMonitor implements Serializable {

	private static final long serialVersionUID = 1L;

	private transient StateBasedSearchTask taskBeingMonitored;

	SearchResult searchResult;

	// TODO(@hayesall): What is special about these?
	public static final SearchResult maxNodesConsideredReached = new SearchResult(false, "Reached maxNodesConsidered.");
	static final SearchResult openBecameEmpty = new SearchResult(false, "OPEN became empty before a goal was found.");

	private static final SearchResult goalFound = new SearchResult(true,  "Goal was found.");
	private static final SearchResult maxNodesCreatedReached = new SearchResult(false, "Reached maxNodesCreated.");
	private static final SearchResult maxNodesConsideredThisIterationReached = new SearchResult(false, "Reached maxNodesConsideredThisIteration.");
	private static final SearchResult maxNodesCreatedThisIterationReached = new SearchResult(false, "Reached maxNodesCreatedThisIteration.");
    private static final SearchResult maxTimeUsedPerIteration = new SearchResult(false, "Reached maximum clock time limit.");

	protected SearchMonitor() {}

	public SearchMonitor(StateBasedSearchTask task) {
		setTaskBeingMonitored(task);
	}
	
	public void setSearchTask(StateBasedSearchTask task) {
		setTaskBeingMonitored(task);
	}

	public boolean recordNodeBeingScored(SearchNode nodeBeingCreated, double score) throws SearchInterrupted {
		// Return TRUE only if this node is acceptable as one that sets "best score seen so far."
		return true;
	}
	
	void searchEndedByTerminator() {
		if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search ended because goal found."); }
		searchResult = goalFound;
	}
	
	public void searchEndedByMaxNodesConsidered(int numberOfNodesConsidered) {
		if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search ended because " + numberOfNodesConsidered      + " exceeds the max number of nodes considered."); }
		searchResult = maxNodesConsideredReached;
	}
	
	public boolean searchReachedMaxNodesCreated(int searchEndedByMaxNodesCreated) {
		if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search created " + searchEndedByMaxNodesCreated + "nodes, which exceeds the max number of nodes created."); }
		// Should override this if there is a reason to continue until OPEN is empty.
		searchResult = maxNodesCreatedReached;
		return getTaskBeingMonitored().stopWhenMaxNodesCreatedReached;
	}
	
	void searchEndedByMaxNodesConsideredThisIteration(int numberOfNodesConsideredThisIteration) {
		if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search ended because " + numberOfNodesConsideredThisIteration      + " exceeds the max number of nodes considered for this iteration."); }
		searchResult = maxNodesConsideredThisIterationReached;
	}
	               
	boolean searchReachedMaxNodesCreatedThisIteration(int searchEndedByMaxNodesCreatedThisIteration) {
		if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search ended because " + searchEndedByMaxNodesCreatedThisIteration + " exceeds the max number of nodes created for this iteration."); }
		searchResult = maxNodesCreatedThisIterationReached;
		// Should override this if there is a reason to continue until OPEN is empty.
		return getTaskBeingMonitored().stopWhenMaxNodesCreatedThisIterationReached;
	}

    void searchEndedByMaxTimeUsed() {
        if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search ended because maximum clock time reached."); }
		searchResult = maxTimeUsedPerIteration;
    }

	void searchEndedBecauseOPENbecameEmpty() {
		if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search ended because OPEN became empty."); }
		searchResult = openBecameEmpty;
	}
	
	SearchResult getSearchResult() {
		// Determine what should be returned when the search has completed.
		return searchResult;
	}

	protected void setTaskBeingMonitored(StateBasedSearchTask taskBeingMonitored) {
		this.taskBeingMonitored = taskBeingMonitored;
	}

	protected StateBasedSearchTask getTaskBeingMonitored() {
		return taskBeingMonitored;
	}

	/*
	* Methods for reading a Object cached to disk.
    */
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
		// TODO(@hayesall): The same method is also in `SearchNode.java`
        if (!(in instanceof StateBasedSearchInputStream)) {
            throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject() input stream must support StateBasedSearchInputStream interface");
        }

        in.defaultReadObject();

        StateBasedSearchInputStream stateBasedSearchInputStream = (StateBasedSearchInputStream) in;

        this.setTaskBeingMonitored(stateBasedSearchInputStream.getStateBasedSearchTask());
    }
}
