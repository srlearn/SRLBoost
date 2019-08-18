package edu.wisc.cs.will.Boosting.RDN.Models;

import java.util.ArrayList;
import java.util.Collection;

public abstract class DependencyNode {

	protected ArrayList<DependencyNetworkEdge> parents;
	protected ArrayList<DependencyNetworkEdge> children;
	private int numberForDOTGraph = -1;

	DependencyNode() {
		parents = new ArrayList<>();
		children = new ArrayList<>();
	}

	public abstract String labelForDOT();
	public abstract String colorForDOT() ;
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
	 * @param i - the index of child edge
	 * @return the ith child edge
	 */
	DependencyNetworkEdge getChild(int i) {
		return children.get(i);
	}

	/*
	 * @return the number of parents
	 */
	int numParents() {
		return parents.size();
	}

	/*
	 * @return the number of children
	 */
	int numChildren() {
		return children.size();
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

	public Collection<DependencyNetworkEdge> getParents() {
		return parents;
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