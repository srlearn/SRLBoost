package edu.wisc.cs.will.Boosting.RDN.Models;

// TODO(@hayesall): `textForDOT` and `styleForDOT` could probably be simplified.
//		dot-file concerns should probably be separated into their own class as well.

/*
 * @author Tushar Khot
 *
 */
public class DependencyNetworkEdge {
	private final DependencyNode start;

	public enum EdgeType {
		DETERMINISTIC,
		PROBABILISTIC,
	}
	
	private final EdgeType edge;

	DependencyNetworkEdge(DependencyNode start) {
		super();
		this.start = start;
		this.edge = EdgeType.PROBABILISTIC;
	}

	public DependencyNode getStart() {
		return start;
	}

	private String styleForDOT() {
		switch(edge) {
			case DETERMINISTIC: return "dashed";
			case PROBABILISTIC: return "solid";
		}
		return "dotted";
	}

	String textForDOT() {
		return "label=\"\" style=" + styleForDOT();
	}
}
