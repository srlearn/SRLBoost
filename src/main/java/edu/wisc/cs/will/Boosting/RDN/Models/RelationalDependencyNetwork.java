package edu.wisc.cs.will.Boosting.RDN.Models;

import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.Models.DependencyNetworkEdge.EdgeType;
import edu.wisc.cs.will.Boosting.RDN.Models.DependencyPredicateNode.PredicateType;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author Tushar Khot
 *
 */
public class RelationalDependencyNetwork extends DependencyNetwork {

	private HashMap<String, HashMap<PredicateType, Set<PredicateName>>> predicateToAncestorMap;
	private HashMap<String,                        Set<PredicateName>> predicateToQueryParentsMap;	
	private HashMap<String,                        Set<PredicateName>> predicateToComputedChildrenMap;

	/*
	 * Set to true, if there is any target predicate that depends on another target predicate
	 */
	private Boolean needsJointInf = null;	
	
	/*
	 * Set to true, if there is any recursive node in RDN.
	 */
	private Boolean hasRecursion = null;	

	public RelationalDependencyNetwork(JointRDNModel fullModel, WILLSetup setup) {
		super();
		initializeRDNUsingModel(fullModel, setup);
		initializeRDNUsingPrecompute(setup);
		resetCache();
		intializeRDNBooleans();
	}
	
	/*
	 * Call this whenever a node or a link is added to the graph.
	 */
	private void resetCache() {
		predicateToAncestorMap = new HashMap<>();
		predicateToQueryParentsMap = new HashMap<>();
		predicateToComputedChildrenMap = new HashMap<>();
	}

	/*
	 * Sets the various booleans such as hasRecursion
	 */
	private void intializeRDNBooleans() {
		// Joint Inference
		needsJointInf = false;
		for (DependencyNode node : stringRepToNode.values()) {
			DependencyPredicateNode target  = (DependencyPredicateNode)node;
			if (target.getType() == PredicateType.QUERY) {
				Collection<PredicateName> ancestors = getAncestorsOfType(target.getPredicate().name, PredicateType.QUERY);
				if (ancestors.size() > 0) {
					needsJointInf = true;
					break;
				}
			}
		}

		hasRecursion = false;
		for (DependencyNode node : stringRepToNode.values()) {
			if (((DependencyPredicateNode)node).getType() == PredicateType.RECURSIVE) {
				hasRecursion = true;
				break;
			}
		}
	}

	public boolean hasRecursion() {
		if(hasRecursion == null) {
			Utils.error("hasRecursion not set.");
		}
		return hasRecursion;
	}

	public boolean isRecursive(String target) {
		return (getAncestorsOfType(target, PredicateType.RECURSIVE).size() > 0);
	}
	public boolean needsJointInference() {
		if(needsJointInf == null) {
			Utils.error("needsJointInf not set.");
		}
		return needsJointInf;
	}	

	private void initializeRDNUsingPrecompute(WILLSetup setup) {

		// TODO(hayesall): Precomputes are deprecated.

		HashMap<PredicateName, Set<PredicateName>> predicateToParents = new HashMap<>();

		for (Clause clause : setup.getContext().getClausebase().getBackgroundKnowledge()) {
			if (!clause.isDefiniteClause()) { 
				Utils.error("Ignoring clause: '" + clause + "'.");
				continue;
			}

			PredicateName pName = clause.posLiterals.get(0).predicateName;

			if (!predicateToParents.containsKey(pName)) {
				predicateToParents.put(pName, new HashSet<>());
			}
			Set<PredicateName> parents = predicateToParents.get(pName);
			if (clause.negLiterals == null || clause.negLiterals.size() <= 0) {
				// Utils.println("No neg literals in clause: " + clause);
				continue;
			}
			// Take parents from the body of the clause
			for (Literal lit : clause.negLiterals) {
				parents.add(lit.predicateName);
			}
		}

		for (PredicateName pName : predicateToParents.keySet()) {
			// Facts are sometimes(LazyHornClauseBase) stored as fact(x) :- .
			// This would be interpreted as "fact" being a precompute, which is wrong. 
			// So make sure that the rule has some predicates in the body, before labelling 
			// a predicate as precompute. 
			if (predicateToParents.get(pName) != null &&
				predicateToParents.get(pName).size() > 0) {
				// Rule has non-empty body, so it is a precomputed predicate.
				getDependencyNode(pName).setType(PredicateType.COMPUTED);
				// Add links for each parent
				for (PredicateName parent : predicateToParents.get(pName)) {
					if (parent.name.contains("wumpus") || pName.name.equals("wumpus")) {
						Utils.waitHere("Adding link between " + parent + " & " + pName);
					}
					addLink(parent, pName, EdgeType.DETERMINISTIC);
				}
			}
		}
	}

	private void initializeRDNUsingModel(JointRDNModel fullModel, WILLSetup setup) {
		if (fullModel == null) {
			// No model provided. Model is only for precomputes.
			return;
		}
		for (String pname : fullModel.keySet()) {
			PredicateName predname = setup.getHandler().getPredicateName(pname);
			// Set type to query
			getDependencyNode(predname).setType(PredicateType.QUERY);
			ConditionalModelPerPredicate model = fullModel.get(pname);
			Set<PredicateName> parents = new HashSet<>();
			model.getParentPredicates(parents);
			for (PredicateName parent : parents) {
				addLink(parent, predname, EdgeType.PROBABILISTIC);
			}
		}
	}

	private void addLink(PredicateName parent, PredicateName child, EdgeType type) {
		// Check if we have parent node
		DependencyNode parNode = getDependencyNode(parent);
		DependencyNode chiNode = getDependencyNode(child);
		DependencyNetworkEdge edge = getDependencyEdge(parNode, chiNode, type);
		parNode.addChild(edge);
		chiNode.addParent(edge);
		resetCache();
	}

	private DependencyNetworkEdge getDependencyEdge(
			DependencyNode parNode,
			DependencyNode chiNode,
			EdgeType type) {
		return new DependencyNetworkEdge(parNode, chiNode, type);
	}

	public DependencyPredicateNode getDependencyNode(PredicateName parent) {
		if (!stringRepToNode.containsKey(parent.name)) {
			DependencyPredicateNode newPar = new DependencyPredicateNode(parent); 
			stringRepToNode.put(parent.name, newPar);
			resetCache();
		}
		return (DependencyPredicateNode)stringRepToNode.get(parent.name);
	}

	public Collection<PredicateName> getQueryParents(String predicate) {
		if (!predicateToQueryParentsMap.containsKey(predicate)) {
			// Not in the cache. build the cache for node
			DependencyNode node = stringRepToNode.get(predicate);
			// Queue of ancestors
			Set<PredicateName> ancestors = new HashSet<>();
			Set<PredicateName> nodesConsidered = new HashSet<>();
			// Search for ancestors
			ArrayList<DependencyNetworkEdge> ancestors_queue = new ArrayList<>(node.getParents());
			while(!ancestors_queue.isEmpty()) {
				// Since we are looking at parents, we need source
				DependencyPredicateNode ancestor = (DependencyPredicateNode)ancestors_queue.remove(0).getStart();
				// Ignore nodes already seen.
				if (nodesConsidered.contains(ancestor.getPredicate())) {
					Utils.println("\n% getQueryParents: Already seen this ancestor: " + ancestor.getPredicate()); 
					continue;
				}
				nodesConsidered.add(ancestor.getPredicate());
				PredicateType aType = ancestor.getType();
				if (aType == PredicateType.QUERY) {
					ancestors.add(ancestor.getPredicate());
				}
				if (aType == PredicateType.COMPUTED) {
					// 	Add the parents of the ancestor, if this node is computed
					ancestors_queue.addAll(ancestor.getParents());
				}
			}
			predicateToQueryParentsMap.put(predicate, ancestors);
		}	
		return predicateToQueryParentsMap.get(predicate);
	}
	public Collection<PredicateName> getAncestorsOfType(String predicate,
			PredicateType type) {
		
		if (!predicateToAncestorMap.containsKey(predicate)) {
			// Not in the cache. build the cache for node
			DependencyNode node = stringRepToNode.get(predicate);
			if (node == null) {
				Utils.error("Doesn't contain the predicate " + predicate + " in the RDN");
			}
			// Queue of ancestors
			HashMap<PredicateType, Set<PredicateName>> ancestorsOfType = new HashMap<>();
			Set<PredicateName> nodesConsidered = new HashSet<>();

			// Search for ancestors
			ArrayList<DependencyNetworkEdge> ancestors = new ArrayList<>(node.getParents());
			while(!ancestors.isEmpty()) {
				// Since we are looking at parents, we need source
				DependencyPredicateNode ancestor = (DependencyPredicateNode)ancestors.remove(0).getStart();
				// Ignore nodes already seen.
				if (nodesConsidered.contains(ancestor.getPredicate())) {
					continue;
				}
				nodesConsidered.add(ancestor.getPredicate());

				PredicateType aType = ancestor.getType();
				if (!ancestorsOfType.containsKey(aType)) {
					ancestorsOfType.put(aType, new HashSet<>());
				}
				if (ancestorsOfType.get(aType).add(ancestor.getPredicate())) {
					// 	Add the parents of the ancestor, if this node was never seen before
					// ie if it is not already in the ancestor set, it is new.
					ancestors.addAll(ancestor.getParents());
				}
			}
			predicateToAncestorMap.put(predicate, ancestorsOfType);
		}	
		
		
		HashMap<PredicateType, Set<PredicateName>> map = predicateToAncestorMap.get(predicate);

		// We have already computed the ancestors for this node.
		if (map.containsKey(type)) {
			return map.get(type);
		}
		// No ancestors of this type found. Return empty list
		return new HashSet<>();
	}

	public Collection<PredicateName> getPredicatesComputedFrom(String predicate) {
		if (!predicateToComputedChildrenMap.containsKey(predicate)) {
			// Not in the cache. build the cache for node
			DependencyNode node = stringRepToNode.get(predicate);
			// Queue of ancestors
			Set<PredicateName> children = new HashSet<>();
			Set<PredicateName> nodesConsidered = new HashSet<>();

			if (node != null) {
				// Search for ancestors
				ArrayList<DependencyNetworkEdge> children_queue = new ArrayList<>(node.getChildren());
				while(!children_queue.isEmpty()) {
					// Since we are looking at children, we need dest
					DependencyPredicateNode child = (DependencyPredicateNode)children_queue.remove(0).getEnd();
					// Ignore nodes already seen.
					if (nodesConsidered.contains(child.getPredicate())) {
						continue;
					}
					nodesConsidered.add(child.getPredicate());

					PredicateType aType = child.getType();
					if (aType == PredicateType.COMPUTED) {
						children.add(child.getPredicate());
					}
					if (aType != PredicateType.QUERY) {
						children_queue.addAll(child.getChildren());
					}
				}
			}
			predicateToComputedChildrenMap.put(predicate, children);
		}	
		return predicateToComputedChildrenMap.get(predicate);
	}

}
