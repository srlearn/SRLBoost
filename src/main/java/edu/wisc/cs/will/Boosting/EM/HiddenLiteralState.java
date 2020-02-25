package edu.wisc.cs.will.Boosting.EM;

import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * Class to store one world state
 * @author tkhot
 *
 */
public class HiddenLiteralState {

	/*
	 * Hash maps from predicate name to literals and their assignments in this world state
	 * Can't rely on the "sampledState" within each example as that may keep changing.
	 * Used Integer instead of Boolean. For multi-class examples, it indicates the index of 
	 * the class label.
	 */
	// TODO(@hayesall): Where is `predNameToLiteralMap` initialized?
	private final Map<String, List<RegressionRDNExample>> predNameToLiteralMap = null;
	private Map<String, List<Integer>> predNameToAssignMap;

	private final List<Literal> trueFacts = null;
	private final List<Literal> falseFacts = null;

	@Override
	public int hashCode()  {
		return getStringRep().hashCode();
	}
	
	
	@Override
	public boolean equals(Object obj) {
		if (obj == null) { return false;}
		if (! (obj instanceof HiddenLiteralState)) {
			return false;
		}
		HiddenLiteralState other = (HiddenLiteralState)obj;
		String otherRep = other.getStringRep();
		String rep = this.getStringRep();
		return otherRep.equals(rep);
	}
	
	String getStringRep() {
		// Generate string that can uniquely determine this world state
		// Note we assume that all world states use the same order of literals for a given predicate
		StringBuilder rep = new StringBuilder();
		for (String key : predNameToAssignMap.keySet()) {
			rep.append(key).append(":");
			for (Integer val : predNameToAssignMap.get(key)) {
				rep.append(val);
			}
			rep.append(".");
		}
		return rep.toString();
	}

	Integer getAssignment(Example eg) {
		// Compare string rep
		String egRep =  eg.toString();

		String pred = eg.predicateName.name;
		List<RegressionRDNExample> litList = predNameToLiteralMap.get(pred);
		
		for (int i = 0; i <  litList.size(); i++) {
			String thisRep = ((Example)litList.get(i)).toString(); 
			if (egRep.equals(thisRep)) {
				return predNameToAssignMap.get(pred).get(i);
			}
		}
		Utils.waitHere("Example: " + eg + " not stored in worldState");
		return 0;
	}


	public static void statePredicateDifference(HiddenLiteralState lastState,
												HiddenLiteralState newState,
												Set<PredicateName> modifiedPredicates,
												String target) {
		if (newState == null) { 
			Utils.waitHere("newState not expected to be null. Will not update the facts.");
			return;
		}
		Utils.error("Expected the true facts for this state to be built.");

		for (Literal addLit : newState.trueFacts) {
			// We know its modified, no need to check it.
			if (modifiedPredicates.contains(addLit.predicateName)) {
				continue;
			}
			// Do not add facts for the target predicate
			if (addLit.predicateName.name.equals(target)) {
				continue;
			}
			if (lastState == null) {
				modifiedPredicates.add(addLit.predicateName);
			} else {
				boolean addThisLit = true;
				String addLitRep = addLit.toString();
				for (Literal oldStateLit : lastState.trueFacts) {
					// If true in the last state, no need to add
					if (oldStateLit.toString().equals(addLitRep)) {
						addThisLit = false;
						break;
					}
				}
				if (addThisLit) {
					modifiedPredicates.add(addLit.predicateName);
				}
			}
		}
		
		for (Literal rmLit : newState.falseFacts) {
			// We know its modified, no need to check it.
			if (modifiedPredicates.contains(rmLit.predicateName)) {
				continue;
			}
			// Do not rm facts for the target predicate
			if (rmLit.predicateName.name.equals(target)) {
				continue;
			}
			if (lastState == null) {
				modifiedPredicates.add(rmLit.predicateName);
			} else {
				boolean rmThisLit = true;
				String rmLitRep = rmLit.toString();
				for (Literal oldStateLit : lastState.falseFacts) {
					// If true in the last state, no need to add
					if (oldStateLit.toString().equals(rmLitRep)) {
						rmThisLit = false;
						break;
					}
				}
				if (rmThisLit) {
					modifiedPredicates.add(rmLit.predicateName);
				}
			}
		}
	}

	/*
	 * Returns the examples that need to be added/removed from the fact base to move from
	 * lastState to newstate
	 * @param lastState Old assignment of facts
	 * @param newState New assignment of facts
	 * @param addExamples Facts to be added
	 * @param rmExamples Facts to be removed
	 */
	public static void stateDifference(HiddenLiteralState lastState,
									   HiddenLiteralState newState,
									   List<Literal> addExamples,
									   List<Literal> rmExamples,
									   String target) {
		if (newState == null) { 
			Utils.waitHere("newState not expected to be null. Will not update the facts.");
			return;
		}
		Utils.error("Expected the true facts for this state to be built.");

		for (Literal addLit : newState.trueFacts) {
			// Do not add facts for the target predicate
			if (addLit.predicateName.name.equals(target)) {
				rmExamples.add(addLit);
				continue;
			}
			if (lastState == null) {
				addExamples.add(addLit);
			} else {
				boolean addThisLit = true;
				String addLitRep = addLit.toString();
				for (Literal oldStateLit : lastState.trueFacts) {
					// If true in the last state, no need to add
					if (oldStateLit.toString().equals(addLitRep)) {
						addThisLit = false;
						break;
					}
				}
				if (addThisLit) {
					addExamples.add(addLit);
				}
			}
		}

		rmExamples.addAll(newState.falseFacts);

	}
}


