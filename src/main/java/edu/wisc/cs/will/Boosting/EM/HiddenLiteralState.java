package edu.wisc.cs.will.Boosting.EM;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.MLN.MLNInference;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.SingleModelSampler;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;

/**
 * Class to store one world state
 * @author tkhot
 *
 */
public class HiddenLiteralState {
	/**
	 * Hash maps from predicate name to literals and their assignments in this world state
	 * Can't rely on the "sampledState" within each example as that may keep changing.
	 * Used Integer instead of Boolean. For multi-class examples, it indicates the index of 
	 * the class label.
	 */
	private Map<String, List<RegressionRDNExample>> predNameToLiteralMap;
	private Map<String, List<Integer>> predNameToAssignMap;
	
	// Cache the string representation of literal to assignment map;
	private Map<String, Integer> literalRepToAssignMap = null;
	private Map<String, ProbDistribution> literalRepToCondDistrMap = null;
	private List<Literal> trueFacts = null;
	private List<Literal> falseFacts = null;

	private double statePseudoProbability  = 1;

	private HiddenLiteralState(Map<String, List<RegressionRDNExample>> jointExamples, Map<String, List<Integer>> assignment) {
		predNameToLiteralMap = new HashMap<>(jointExamples);
		predNameToAssignMap = new HashMap<>(assignment);
	}
	HiddenLiteralState(Map<String, List<RegressionRDNExample>> jointExamples) {
		predNameToLiteralMap = new HashMap<>(jointExamples);
		initAssignment();
	}

	public void addNewExamplesFromState(HiddenLiteralState newState) {
		for (String newPred : newState.predNameToLiteralMap.keySet()) {
			if (!this.predNameToLiteralMap.containsKey(newPred)) {
				this.predNameToLiteralMap.put(newPred, new ArrayList<>());
				this.predNameToAssignMap.put(newPred, new ArrayList<>());
			}
			List<RegressionRDNExample> newExamples = newState.predNameToLiteralMap.get(newPred);
			for (int i = 0; i < newExamples.size(); i++) {
				this.predNameToLiteralMap.get(newPred).add(newExamples.get(i));
				this.predNameToAssignMap.get(newPred).add(newState.predNameToAssignMap.get(newPred).get(i));
			}
		}
	}
	
	private void initAssignment() {
		predNameToAssignMap = new HashMap<>();
		for (String predName : predNameToLiteralMap.keySet()) {
			for (RegressionRDNExample lit : predNameToLiteralMap.get(predName)) {
				if (!predNameToAssignMap.containsKey(predName)) {
					predNameToAssignMap.put(predName, new ArrayList<>());
				}
				predNameToAssignMap.get(predName).add(lit.getSampledValue());
			}
		}
	}
	
	
	public String toPrettyString() {
		StringBuilder sb = new StringBuilder();
		for (String predName : predNameToLiteralMap.keySet()) {
			for (int i = 0; i < predNameToLiteralMap.get(predName).size(); i++) {
				sb.append(predNameToLiteralMap.get(predName).get(i).toPrettyString(""));
				sb.append(":");
				sb.append(predNameToAssignMap.get(predName).get(i));
				sb.append("\n");
			}
		}
		return sb.toString();
	}

	HiddenLiteralState marginalizeOutPredicate(String predicate) {
		HiddenLiteralState marginState = new HiddenLiteralState(this.predNameToLiteralMap, this.predNameToAssignMap);
		marginState.predNameToLiteralMap.remove(predicate);
		marginState.predNameToAssignMap.remove(predicate);
		return marginState;
	}
	
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

	public Set<String> getPredicates() {
		return predNameToLiteralMap.keySet();
	}
	
	void buildLiteralToAssignMap() {
		literalRepToAssignMap = new HashMap<>();
		for (String predName : predNameToLiteralMap.keySet()) {
			for (int i = 0; i < predNameToLiteralMap.get(predName).size(); i++) {
				String litRep = predNameToLiteralMap.get(predName).get(i).toPrettyString("");
				Integer assign = predNameToAssignMap.get(predName).get(i);
				literalRepToAssignMap.put(litRep, assign);
			}
		}
	}
	
	public Integer getAssignment(Example eg) {
		// Compare string rep
		String egRep =  eg.toString();
				
		if (literalRepToAssignMap != null) {
			if (literalRepToAssignMap.get(egRep) == null) { 
				Utils.waitHere("Example: " + eg + " not stored in cached worldState");
			}
			return literalRepToAssignMap.get(egRep);
		}
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
	
	public Iterable<Literal> getPosExamples() {
		return new ExampleIterable(this, 1);
	}
	
	public Iterable<Literal> getNegExamples() {
		return new ExampleIterable(this, 0);
	}
	

	public static class ExampleIterable implements Iterable<Literal> {

		HiddenLiteralState state;
		Integer match;
		ExampleIterable(HiddenLiteralState state, Integer match) {
			this.state = state;
			this.match = match;
		}
		@Override
		public Iterator<Literal> iterator() {
			return new ExampleIterator(state, match);
		}
		
	}
	
	public static class ExampleIterator implements Iterator<Literal> {

		Iterator<String> predKeyIterator;
		String currentPred;
		int exampleIndex;
		HiddenLiteralState state;
		Integer matchState;
		boolean gotoNext;
		ExampleIterator(HiddenLiteralState state, Integer match) {
			this.state = state;
			matchState = match;
			predKeyIterator = state.predNameToLiteralMap.keySet().iterator();
			currentPred = predKeyIterator.next();
			exampleIndex = -1;
			gotoNext = true;
		}

		@Override
		public boolean hasNext() {
			// Already called hasNext
			if (!gotoNext) {
				return currentPred != null;
			} else {
				if (updateToNextMatchingLiteral()) {
					gotoNext = false;
					return true;
				} else {
					gotoNext = false;
					return false;
				}
			}
			
		}
		
		boolean updateToNextMatchingLiteral() {
			// hasNext has already updated the index for the next literal.
			if (!gotoNext) {
				return true;
			}
			do {
				List<RegressionRDNExample> egs = state.predNameToLiteralMap.get(currentPred);
				for (int i = exampleIndex+1; i < egs.size(); i++) {
					if (egs.get(i).isHasRegressionVector()) {
						// Mutli-class examples always stored as positive examples
						if (matchState == 1) {
							exampleIndex = i;
							return true;
						}
					} else {
						if (state.predNameToAssignMap.get(currentPred).get(i).equals(matchState)) {
							exampleIndex = i;
							return true;
						}
					}
				}
				exampleIndex  = -1;
				if (predKeyIterator.hasNext()) { 
					currentPred = predKeyIterator.next();
				} else {
					currentPred = null;
				}
			} while(currentPred != null);
			
			return false;
		}

		@Override
		public Literal next() {
			if (updateToNextMatchingLiteral()) {
				gotoNext = true;
				return state.predNameToLiteralMap.get(currentPred).get(exampleIndex);
			}
			throw new NoSuchElementException();
		}

		@Override
		public void remove() {
			state.predNameToLiteralMap.get(currentPred).remove(exampleIndex);
			state.predNameToAssignMap.get(currentPred).remove(exampleIndex);
			
		}
		
	}

	void buildExampleToCondProbMap(WILLSetup setup, JointRDNModel jtModel) {
		
		if (literalRepToAssignMap == null) {
			Utils.error("Make sure to call buildLiteralToAssignMap before this method call");
		}
		literalRepToCondDistrMap = new HashMap<>();
		statePseudoProbability   = 1;
		SRLInference.updateFactsFromState(setup, this);
		for (String predName : predNameToLiteralMap.keySet()) {
			SRLInference sampler;
			if (setup.useMLNs) {
				sampler = new MLNInference(setup, jtModel);
			} else {
				// Since we are only calculating the conditional probabilities given all the other assignments
				// to the hidden states as facts, we do not need to worry about recursion (last arg).
				sampler= new SingleModelSampler(jtModel.get(predName), setup, jtModel, false);
			}
			List<RegressionRDNExample> literalList = predNameToLiteralMap.get(predName);
			// Create a new list since we modify the example probabilities
			List<RegressionRDNExample> newList = new ArrayList<>();
			for (RegressionRDNExample rex : literalList) {
				newList.add(new RegressionRDNExample(rex));
			}
			sampler.getProbabilities(newList);

			for (RegressionRDNExample newRex : newList) {
				ProbDistribution distr = newRex.getProbOfExample();
				String rep = newRex.toPrettyString("");
				literalRepToCondDistrMap.put(rep, distr);
				if (!literalRepToAssignMap.containsKey(rep)) {
					Utils.error("No assignment for: " + rep);
				}
				statePseudoProbability *= distr.probOfTakingValue(literalRepToAssignMap.get(rep));
			}
		}
	}

	public void updateStateFacts(WILLSetup setup) {
		trueFacts = new ArrayList<>();
		falseFacts=new ArrayList<>();
		for (Literal posEx : getPosExamples()) {

			if (posEx.predicateName.name.startsWith(WILLSetup.multiclassPredPrefix)) {
				RegressionRDNExample mcRex = (RegressionRDNExample)posEx;
				int maxVec = mcRex.getOutputVector().length;
				int assign = getAssignment((Example)posEx);
				if (assign < 0 || assign >= maxVec) { Utils.waitHere("Assignment: " + assign + " not within bound: " + maxVec);}
				for (int i = 0; i < maxVec; i++) {
					Example eg =  setup.getMulticlassHandler().createExampleFromClass(mcRex, i);
					if (i == assign) {
						trueFacts.add(eg);
						if (setup.allowRecursion) {
							Literal lit = setup.getHandler().getLiteral(setup.getHandler().getPredicateName(
									WILLSetup.recursivePredPrefix + eg.predicateName.name), eg.getArguments());
							trueFacts.add(lit);

						}
					} else {
						falseFacts.add(eg);
						if (setup.allowRecursion) {
							Literal lit = setup.getHandler().getLiteral(setup.getHandler().getPredicateName(
									WILLSetup.recursivePredPrefix + eg.predicateName.name), eg.getArguments());
							falseFacts.add(lit);

						}
					}
				}
			} else {
				trueFacts.add(posEx);
				if (setup.allowRecursion) {
					Literal lit = setup.getHandler().getLiteral(setup.getHandler().getPredicateName(
							WILLSetup.recursivePredPrefix + posEx.predicateName.name), posEx.getArguments());
					trueFacts.add(lit);
				}
			}
		}
		for (Literal negEx : getNegExamples()) {
			falseFacts.add(negEx);
			if (setup.allowRecursion) {
				Literal lit = setup.getHandler().getLiteral(setup.getHandler().getPredicateName(
						WILLSetup.recursivePredPrefix + negEx.predicateName.name), negEx.getArguments());
				falseFacts.add(lit);
			}
		}
	}
	
	/**
	 * @return the statePseudoProbability
	 */
	public double getStatePseudoProbability() {
		return statePseudoProbability;
	}

	public ProbDistribution getConditionalDistribution(Literal ex) {
		String rep  = ex.toPrettyString("");
		if (literalRepToCondDistrMap == null) {
			Utils.error("Conditional distribution not set.");
		}
		if (!literalRepToCondDistrMap.containsKey(rep)) {
			Utils.error("Example: " + rep + " unseen in the hidden state");
		}
		return literalRepToCondDistrMap.get(rep);
	}
	
	
	public static void statePredicateDifference(HiddenLiteralState lastState, 
												HiddenLiteralState newState,
												Set<PredicateName> modifiedPredicates,
												String target) {
		if (newState == null) { 
			Utils.waitHere("newState not expected to be null. Will not update the facts.");
			return;
		}
		if (newState.trueFacts == null) {
			Utils.error("Expected the true facts for this state to be built.");
		}
		
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
	/**
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
		if (newState.trueFacts == null) {
			Utils.error("Expected the true facts for this state to be built.");
		}
		
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


