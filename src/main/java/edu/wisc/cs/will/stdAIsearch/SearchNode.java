package edu.wisc.cs.will.stdAIsearch;

import edu.wisc.cs.will.Utils.Utils;

import java.io.IOException;
import java.io.Serializable;

/*
 * @author shavlik
 */
public abstract class SearchNode implements Serializable {

	private final SearchNode parentNode;

	// Provide a back pointer.
	transient public StateBasedSearchTask task;

	// Depth in the search tree (root is 0).
	public int depth = 0;

	// Used for heuristic searches.
	public double score = 0;

	// Used if we want to 'tweak' the score of a node to manipulate the ordering of the OPEN list.
	double bonusScore = 0;

	private boolean dontAddMeToOPEN = false;

	/*
	 * Create the root node, since it connects nodes to the search task.
	 */
	protected SearchNode(StateBasedSearchTask task) {
		this.task = task;
		if (task == null) {
			Utils.error("Creating a search node but have task=null.");
		}
		this.parentNode = null;		
	}

	protected SearchNode(SearchNode parentNode) {
		task = parentNode.task;
		this.parentNode = parentNode;
		depth  = parentNode.depth + 1;
	}
	
	boolean dontActuallyAddToOpen() {
		return dontAddMeToOPEN;
	}

	// The next two are only needed when dealing with CLOSED lists.
	// Remember that if two search nodes are equal, then their hash codes also need to be equal.

	public boolean equals(Object otherNode) {
		// Leave this here as a reminder to override if needed.
		return super.equals(otherNode); 
	}

   /*
	* Methods for reading a Object cached to disk.
    */
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
		// TODO(@hayesall): The same method is also in `SearchMonitor.java`
        if (!(in instanceof StateBasedSearchInputStream)) {
            throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject() input stream must support FOPCObjectInputStream interface");
        }

        in.defaultReadObject();

        StateBasedSearchInputStream stateBasedSearchInputStream = (StateBasedSearchInputStream) in;

        this.task = stateBasedSearchInputStream.getStateBasedSearchTask();
    }

    public SearchNode getParentNode() {
        return parentNode;
    }

	public void setDontAddMeToOPEN(boolean dontAddMeToOPEN) {
		this.dontAddMeToOPEN = dontAddMeToOPEN;
	}
}
