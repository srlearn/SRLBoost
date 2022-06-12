package edu.wisc.cs.will.Boosting.RDN.Models;

import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
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

	public RelationalDependencyNetwork(JointRDNModel fullModel, WILLSetup setup) {
		super();
		initializeRDNUsingModel(fullModel, setup);
		initializeRDNUsingPrecompute(setup);
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
				addLink(parent, predname);
			}
		}
	}

	private void addLink(PredicateName parent, PredicateName child) {
		// Check if we have parent node
		DependencyNode parNode = getDependencyNode(parent);
		DependencyNode chiNode = getDependencyNode(child);
		DependencyNetworkEdge edge = getDependencyEdge(parNode);
		parNode.addChild(edge);
		chiNode.addParent(edge);
	}

	private DependencyNetworkEdge getDependencyEdge(
			DependencyNode parNode) {
		return new DependencyNetworkEdge(parNode);
	}

	public DependencyPredicateNode getDependencyNode(PredicateName parent) {
		if (!stringRepToNode.containsKey(parent.name)) {
			DependencyPredicateNode newPar = new DependencyPredicateNode(parent); 
			stringRepToNode.put(parent.name, newPar);
		}
		return (DependencyPredicateNode)stringRepToNode.get(parent.name);
	}

}
