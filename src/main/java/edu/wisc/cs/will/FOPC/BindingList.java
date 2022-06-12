package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.util.*;
import java.util.Map.Entry;

/*
 * @author shavlik
 * 
 * Binding lists return the results of unification.
 *
 */
public class BindingList extends AllOfFOPC {
	public final HashMap<Variable,Term> theta;

	public BindingList() {
		theta = createMap(0);
	}
	public BindingList(HashMap<Variable,Term> theta) {
		this.theta = theta;
	}
	
	// This is rarely used, but keep it for debugging etc (it is currently only used when in the read-eval-print loop of the resolution theorem prover.
	public BindingList(List<Binding> bindings) {
		theta = createMap(0);

		if (bindings != null) {
            for (Binding bind : bindings) {
                theta.put(bind.var, bind.term);
            }
        }
	}
	
	private void addBindings(List<Binding> bindings) {
		if (bindings != null) for (Binding bind : bindings) { 
			Term existingBinding = lookup(bind.var);
			if (existingBinding == null) { theta.put(bind.var, bind.term);
			}
			else if (existingBinding != bind.term) {
				if (bind.term instanceof Variable && existingBinding == lookup((Variable) bind.term)) { continue; } // Both bound to same thing, which is fine.
				Utils.error("Asking to bind '" + bind.var + "' to '" + bind.term + "', but it is already bound to '" + existingBinding + "'.");
			}
		}
	}
	
	public void addBindings(BindingList bl) {
		addBindings(bl.collectBindingsInList());
	}

	public BindingList copy() {
		if (theta.isEmpty()) { return new BindingList(); }

        HashMap newMap = createMap(theta.size());
        newMap.putAll(theta);

		return new BindingList(newMap);
	}

    /* Creates a new theta map.
     *
     * I offloading this to a small helper so that I could easily change the type of
     * map that was created without changing it in 5 different places.
     *
     * @return A new theta map.
     */
    private HashMap<Variable,Term> createMap(int size) {

        int realSize = Math.max(16, (int)Math.ceil(size * 0.75f)+1);

        return new HashMap<>(realSize);
    }

	public List<Literal> applyTheta(List<Literal> literals) { // Note that the above code assumes this will make a top-level copy (but the above wont call this if theta is empty or the list is).
		if (literals == null) { return null; }
		if (theta    == null || theta.size() == 0) { return literals; } // No need to apply the empty list of bindings.
		List<Literal> result = new ArrayList<>(literals.size());
		for (Literal literal : literals) {	
			result.add(literal.applyTheta(theta));  // Since Java doesn't do dynamic casting, need to put applyTheta's in the FOPC classes.
		}
		return result;
	}

	/* Returns the current mapping of variable to term, recursively.
     *
     * This does a lookup of the variable recursively.  @see getMapping(Variable)
     * for non-recursive lookups.  Only variables are looked up
     * recursively.  Terms containing variables are not and will require
     * an applyTheta call to resolve completely.
     */
	public Term lookup(Variable var) { // Could save this method call.
		Term result = theta.get(var);
		if (result == null) { return null; }
        if (result == var ) { return result; }
		if (result instanceof Variable) { // Do a recursive lookup.
			Term result2 = lookup((Variable) result);
			if (result2 == null) { return result; } { return result2; }
		}
		return result;
	}

    /* Returns the current mapping of variable to term, non-recursively.
     *
     * This does a lookup of the variable non-recursively.  @see lookup(Variable)
     * for recursive lookups.
     */
    public Term getMapping(Variable var) {
		return theta.get(var);
	}

	public int size() {
        return theta.size();
    }


	Variable reverseLookup(Term term) { // Could save this method call.
		boolean hold = term.stringHandler.usingStrictEqualsForFunctions();
		term.stringHandler.setUseStrictEqualsForFunctions(false);
		if (theta == null || !theta.containsValue(term)) {
			term.stringHandler.setUseStrictEqualsForFunctions(hold);
			return null; // Saves time?
		}
		
		for (Variable var : theta.keySet()) {
			Term trm = theta.get(var);
			
			if (term.equals(trm)) { 
				term.stringHandler.setUseStrictEqualsForFunctions(hold);
				return var; 
			}
		}
		Utils.error("ContainsValue found " + term + " in " + theta + ", but this code could not.");
		term.stringHandler.setUseStrictEqualsForFunctions(hold);
		return null;
	}

	boolean addBindingFailSoftly(Variable var, Term term) {
		if (help_addBinding(var, term, false)) { return true; }
		if (term instanceof Variable) { return help_addBinding((Variable) term, var, false); } // This is probably already checked below, but try again nevertheless.
		return false;
	}
	public void addBinding(Variable var, Term term) {
		help_addBinding(var, term, true);
	}
	private boolean help_addBinding(Variable var, Term term, boolean errorIfProblem) {
		if (theta.containsKey(var)) { 
			Term oldAnswer = theta.get(var);
			if (oldAnswer == term) { return true; } // Already there, which is fine.
			if (oldAnswer instanceof Variable) { addBinding((Variable) oldAnswer, term); return true; }
			else if (term instanceof Variable) {
				Variable v = (Variable) term;
				// Have something like ?X->term and asking to do ?X->?Y.  Then do ?Y->term if ?Y is not yet bound.
				if (!theta.containsKey(v)) {  // If this term is a variable and is not already in the binding list, then just return the binding for it.
					theta.put(v, oldAnswer);	
					return true;
				} // Could handle more, but wait on this until a concrete case arises.
			}
			if (errorIfProblem) {
				Utils.error("Cannot addBinding(" + var + "," + term +") because '" + var + "' is already bound to '" + theta.get(var) + "'.");
			}
			return false;
		}
		theta.put(var, term);
		return true;
	}

	// Collect all the bindings in the HashMap.
	public List<Binding> collectBindingsInList() {
		if (Utils.getSizeSafely(theta) < 1) { return null; }  // Might want to instead return the empty list?
		List<Binding> results = new ArrayList<>(theta.size());
		for (Variable var : theta.keySet()) {
			results.add(new Binding(var, theta.get(var)));
		}
		return results;
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return theta.toString();
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		StringBuilder stringBuilder = new StringBuilder();
        stringBuilder.append("{");
        boolean first = true;
		for (Variable var : theta.keySet()) {
			Term trm = theta.get(var);
			
			if (!first) { stringBuilder.append(", "); } else { first = false; }
            stringBuilder.append(var.toString(bindingList)).append("=").append(trm.toString(bindingList));
		}
        stringBuilder.append("}");

        return stringBuilder.toString();
	}

    public String toString() {
        return toString(null);
    }

	@Override
	public BindingList applyTheta(Map<Variable, Term> bindings) {
		Utils.error("Should not call applyTheta on a Binding List.");
		return this;
	}

    /*
	 * Applies the Theta bindings to all of the terms of this bindingList.
     *
     * This method is used to apply the bindings in the provided map to the
     * terms in this map.
     *
     */
    public void applyThetaInPlace(Map<Variable, Term> bindings) {

        for (Entry<Variable, Term> entry : theta.entrySet()) {
            Term t2 = entry.getValue().applyTheta(bindings);
            entry.setValue(t2);
        }
    }
	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return (theta.containsKey(v) ? 1 : 0);
	}

}
