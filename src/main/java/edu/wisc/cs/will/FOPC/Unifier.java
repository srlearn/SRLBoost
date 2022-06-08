package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;
import java.util.List;
import java.util.Map;

// TODO(@hayesall): Many of the `unify()` methods return `null`, this should probably be rethought.

public class Unifier extends AllOfFOPC implements Serializable {

	public final static Unifier UNIFIER = new Unifier();
    
	// Could use statics to perform unification since no "state" involved, but use an instance for safety.  
	// Notice that the binding list is changed (rather than copied).
	// So be careful when passing in binding lists (notice the first method below creates a fresh binding list).
	
	// To save space, do NOT rename expressions via substitution of bound variables, but instead always recursively look up in the binding list.
	// This code is basically the same as in the next method.  But save a function call (and allow different reporting when debugging).
	public BindingList unify(Literal lit1, Literal lit2) {
		if (lit1.predicateName == lit2.predicateName && lit1.numberArgs() == lit2.numberArgs()) {
			return unify(lit1.getArguments(), lit2.getArguments(), new BindingList());
		}
		else {
			return null;
		}
	}
	public BindingList unify(Literal lit1, Literal lit2, BindingList bindingList) {		
		if (lit1.predicateName == lit2.predicateName && lit1.numberArgs() == lit2.numberArgs()) {
			return unify(lit1.getArguments(), lit2.getArguments(), bindingList);
		}
		else {
			return null;  // We need to be be sure we differentiate a FAILED unification from one with no variable bindings.  NULL means failed and an empty list means success w/o needing any bindings.
		}
	}

	private BindingList unify(List<Term> args1, List<Term> args2, BindingList bindingList) {
		// The calling code checks arguments sizes, so no need to do that here.
		// TAW: I normally wouldn't trust an external check...the check should probably be skipped
		// TAW: on the outside call and done internally here.  JWS: I'd agree, except this is a 'private'		
		
		// Since the unifier is being mainly used in a learning-from-examples setting, there will be lots of constants.
		// so do a quick skim to see if ever paired arguments involve different constants.  If so, can fail immediately.
		if (args1 == null) { return bindingList; } // Since #args checked already, can do this simple check.
		int count = args1.size();
		for(int index = 0; index < count; index++) {
			Term term1 = args1.get(index);
			Term term2 = args2.get(index);
			
			if (term1 != term2 && term1 instanceof Constant && term2 instanceof Constant) {
				return null;
			}
		}
		
		for(int index = 0; index < count; index++) {
			Term term1 = args1.get(index);
			Term term2 = args2.get(index);
			
			bindingList = unify(term1, term2, bindingList);
			if (bindingList == null) {
				return null;
			}
		}

		return bindingList;
	}
	
	// The built-in EQUALS(Term1, Term2) needs to access this.
	public BindingList unify(Term term1, Term term2, BindingList bindingList) {
		if (term1 instanceof Constant && term2 instanceof Constant) {			
			return term1 == term2 ? bindingList : null;  // Could call 'equivalent' here, but save the function call since this called quite often.
		}
		else if (term1 instanceof Variable) {
			return unifyVariable((Variable) term1, term2, bindingList);			
		}
		else if (term2 instanceof Variable) {
			return unifyVariable((Variable) term2, term1, bindingList);	
		}
		else if (term1 instanceof Function && term2 instanceof Function) {
			Function f1 = ((Function) term1);
			Function f2 = ((Function) term2);
			
			if (f1.functionName == f2.functionName && f1.numberArgs() == f2.numberArgs()) {
				return unify(f1.getArguments(), f2.getArguments(), bindingList);
			}
			else {
				return null;
			}
		}
		else {
			return null;
		}
	}
	
	private BindingList unifyVariable(Variable var, Term term, BindingList bindingList) {
		Term lookedupVar  = var;
		Term lookedupTerm = term;
		Term temp_lookedupVar = bindingList.lookup(var);
		
		if (temp_lookedupVar != null) { lookedupVar = temp_lookedupVar; }
		if (term instanceof Variable) {
			Term temp_lookedupTerm = bindingList.lookup((Variable) term);
			
			if (temp_lookedupTerm != null) { lookedupTerm =  temp_lookedupTerm; }
		}
		
		// If anything changed in a lookup, recur (note that either of the two variables might become a more complex term after lookup.
		if ((var != null && !var.equals(lookedupVar)) || (term != null &&!term.equals(lookedupTerm))) { // If anything changed due to a lookup, recur.
			return unify(lookedupVar, lookedupTerm, bindingList);
		}
		else if (var != null && var.equals(term)) {
			return bindingList;
		}
		// We are NOT implementing the 'occurs check' but if we did it would go here.  JWS added (7/25/10) a partial occurs check (for functions that are lists).
		else {
			boolean success = bindingList.addBindingFailSoftly(var, term);
			if (!success) { return null; }
			return bindingList;
		}
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return toString(precedenceOfCaller, bindingList);
	}
	protected String toString(int precedenceOfCaller, BindingList bindingList) {
		return "<this is an instance of the Unifier class>";
	}

	@Override
	public Unifier applyTheta(Map<Variable, Term> bindings) {
		Utils.println("Why call this on a unifier?");
		return null;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}


}
