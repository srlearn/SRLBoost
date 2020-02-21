package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.util.Collection;
import java.util.List;
import java.util.Map;

public abstract class TreeStructuredTheoryNode extends AllOfFOPC {
	
	double weightedCountOfPositiveExamples = 0;
	double weightedCountOfNegativeExamples = 0;
	private TreeStructuredTheoryInteriorNode parent = null;     // Need this in case tree-surgery is needed.
	protected int level = -1; // Level in the tree. Root=0.  I.e., this counts number of ancestor nodes.
	// Used for creating a graph in DOT format.
	int nodeNumber = 0;
	
	public TreeStructuredTheoryInteriorNode getParent() {
		return parent;
	}

	public void setParent(TreeStructuredTheoryInteriorNode parent) {
		this.parent = parent;
		level = (parent == null ? 0 : parent.level + 1);
	}

	public double getWeightedCountOfPositiveExamples() {
		return weightedCountOfPositiveExamples;
	}

	public double getWeightedCountOfNegativeExamples() {
		return weightedCountOfNegativeExamples;
	}

	public abstract String                   printRelationalTree(String newLineStarter, int precedenceOfCaller, int depth, BindingList bindingList);
	public abstract List<Clause>             collectPathsToRoots(TreeStructuredTheory treeTheory);
	public abstract TreeStructuredTheoryNode applyTheta(Map<Variable,Term> bindings);	
	public abstract Collection<Variable>     collectFreeVariables(Collection<Variable> boundVariables);

	static int counter=0;
	public abstract String writeDotFormat();

	public int getLevel() {
		return level;
	}

	public void setLevel(int level) {
		if (this.level >= 0 && this.level != level) { Utils.waitHere("Setting to level = " + level + " but level currently equals = " + this.level + ":\n  " + this); }
		this.level = Math.max(0, level);
	}
}
