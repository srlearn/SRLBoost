package edu.wisc.cs.will.Boosting.RDN.Models;

import edu.wisc.cs.will.FOPC.Literal;

/*
 * @author tkhot
 */
public class DependencyExampleNode extends DependencyNode {
	// Note: Literals may have variables in them
	private final Literal example;
	
	private final ExampleType type;

	public enum ExampleType {
		QUERY,
		EVIDENCE,
		RECURSIVE,
		COMPUTED, 
		VARIABLIZED
	}
	
	DependencyExampleNode(Literal eg, ExampleType type) {
		super();
		example = eg;
		this.type = type;
	}

	public Literal getExample() {
		return example;
	}

	private String labelForDOT() {
		return example.toString();
	}

	private String colorForDOT() {
		switch(type) {
		case QUERY: return "gray52";
		case VARIABLIZED: return "gray62";
		case RECURSIVE: return "gray72";
		case COMPUTED: return "gray82";
		case EVIDENCE: return "gray92";
		}
		return "white";
	}

	@Override
	public String textForDOT() {
		return "style=\"filled\" label=\"" + labelForDOT() +"\" color=\"" + colorForDOT() + "\"";
	}

	@Override
	public boolean ignoreNodeForDOT() {
		return type == ExampleType.EVIDENCE;
	}
}
