package edu.wisc.cs.will.stdAIsearch;

/*
 * @author shavlik
 */
public abstract class EndTest {

	public EndTest() {
	}

	void setSearchTask() {
	}

	// Clear any state saved between searches using the same instance.
	public abstract void clearAnySavedInformation(boolean insideIterativeDeepening);

	public abstract boolean endSearch(SearchNode currentNode);
}
