package edu.wisc.cs.will.Boosting.RDN.Models;

// TODO(@hayesall): `textForDOT` and `styleForDOT` could probably be simplified.
//		dot-file concerns should probably be separated into their own class as well.

/*
 * @author Tushar Khot
 *
 */
public class DependencyNetworkEdge {
	private DependencyNode start;
	private DependencyNode end;
	public enum EdgeType {
		DETERMINISTIC,
		PROBABILISTIC,
	}
	
	private EdgeType edge;

	DependencyNetworkEdge(DependencyNode start,
						  DependencyNode end,
						  EdgeType edge) {
		super();
		this.start = start;
		this.end = end;
		this.edge = edge;
	}

	public DependencyNode getStart() {
		return start;
	}

	public DependencyNode getEnd() {
		return end;
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
