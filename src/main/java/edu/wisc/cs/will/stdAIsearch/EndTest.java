package edu.wisc.cs.will.stdAIsearch;

/*
 * @author shavlik
 */
public abstract class EndTest {

	protected EndTest() {
	}

	void setSearchTask() {
	}

	// Clear any state saved between searches using the same instance.
	public abstract void clearAnySavedInformation();

	public abstract boolean endSearch(SearchNode currentNode);
}
