package edu.wisc.cs.will.Boosting.RDN.Models;

import java.util.ArrayList;

public abstract class DependencyNode {

	private final ArrayList<DependencyNetworkEdge> parents;
	private final ArrayList<DependencyNetworkEdge> children;
	private int numberForDOTGraph = -1;

	DependencyNode() {
		parents = new ArrayList<>();
		children = new ArrayList<>();
	}

	public abstract String  textForDOT();
	public abstract boolean ignoreNodeForDOT();

	/*
	 * @param i - the index of parent edge
	 * @return the ith parent edge 
	 */
	public DependencyNetworkEdge getParent(int i) {
		return parents.get(i);
	}

	/*
	 * @return the number of parents
	 */
	int numParents() {
		return parents.size();
	}

	/*
	 * @param edge - add this edge to the dependency network as parent
	 */
	void addParent(DependencyNetworkEdge edge) {
		parents.add(edge);
	}

	/*
	 * @param edge - add this edge to the dependency network as child
	 */
	void addChild(DependencyNetworkEdge edge) {
		children.add(edge);
	}

	/*
	 * @return the children
	 */
	public ArrayList<DependencyNetworkEdge> getChildren() {
		return children;
	}


	/*
	 * @return the numberForDOTGraph
	 */
	int getNumberForDOTGraph() {
		return numberForDOTGraph;
	}


	/*
	 * @param numberForDOTGraph the numberForDOTGraph to set
	 */
	void setNumberForDOTGraph(int numberForDOTGraph) {
		this.numberForDOTGraph = numberForDOTGraph;
	}

}