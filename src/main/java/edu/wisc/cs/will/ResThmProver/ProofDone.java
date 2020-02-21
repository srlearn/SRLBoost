package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.Binding;
import edu.wisc.cs.will.stdAIsearch.EndTest;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

import java.util.List;

/*
 * @author shavlik
 */
public class ProofDone extends EndTest {
	private HornSearchNode goalNodeFound;

	ProofDone() {
		super();
	}
	
	public boolean endSearch(SearchNode currentNode) {
		HornSearchNode thisNode = (HornSearchNode)currentNode;
		boolean result = thisNode.isSolution();
		if (result) { goalNodeFound = thisNode; }
		return result;
	}
	
	public void clearAnySavedInformation() {
		goalNodeFound = null;
	}

	public List<Binding> collectQueryBindings() {
        if (goalNodeFound == null) { return null; }
		return goalNodeFound.collectQueryBindings().collectBindingsInList();
    }

	public String toString() {
		if (goalNodeFound == null) { return "Search ended without finding a proof-by-negation."; }
		return "Search ended successfully.";
	}
}
