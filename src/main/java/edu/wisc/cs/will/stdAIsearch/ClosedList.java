package edu.wisc.cs.will.stdAIsearch;

/*
 * Keep track of nodes already visited.  Order doesn't matter (fast access does) so use a hash table.
 * @author shavlik
 */
public abstract class ClosedList {

	// TODO(?): have a max size on this (and then randomly discard some percent if full? see linkedHashMap)

	protected ClosedList() {}

	public abstract void addNodeToClosed(SearchNode node);

	public abstract boolean alreadyInClosedList(SearchNode node);

	public abstract void emptyClosedList();
}
