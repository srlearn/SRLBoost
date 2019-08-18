package edu.wisc.cs.will.stdAIsearch;

/*
 * @author shavlik
 */
public abstract class EndTest {

	protected StateBasedSearchTask task;

	public EndTest(StateBasedSearchTask task) {
		this.task = task;
	}

	public void setSearchTask(StateBasedSearchTask task) {
		this.task = task;
	}

	// Clear any state saved between searches using the same instance.
	public abstract void clearAnySavedInformation(boolean insideIterativeDeepening);

	public abstract boolean endSearch(SearchNode currentNode);
}
