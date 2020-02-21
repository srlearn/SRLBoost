package edu.wisc.cs.will.stdAIsearch;

/*
 * The job of this is to initialize the open list for the given search task.
 * @author shavlik
 */
public abstract class Initializer {
	protected StateBasedSearchTask task;

	// TODO(?): Also needs to add all generated initial nodes to CLOSED if CLOSED is being used.

	protected Initializer() {}

	void setSearchTask(StateBasedSearchTask task) {
		this.task = task;
	}
	
	public abstract void initializeOpen(OpenList open) throws SearchInterrupted;

}
