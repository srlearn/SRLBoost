package edu.wisc.cs.will.FOPC;

import java.util.Collection;
import java.util.Map;

/*
 * @author shavlik
 *
 */
public class ObjectAsTerm extends Term {
	public final Object item = null;

	// TODO(hayesall): Constructor was never used, this can almost certainly be removed by rewriting parts of `Theory`.

	public Term applyTheta(Map<Variable,Term> bindings) {
		return this; // BUGGY if item is a variable that should have theta applied to it or contains such a variable (but this shouldn't be used in this case).
	}
	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
		return null;
	}
	public Term copy(boolean recursiveCopy) {
		return this;
	}

    @Override
    public Term copy2(boolean recursiveCopy, BindingList bindingList) {
        return this;
    }


	@Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    
	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + 0;
		return result;
	}	
	public boolean equals(Object other) {
		if (this == other) { return true; }
		return other instanceof ObjectAsTerm;
	}
	public boolean containsVariables() {
		return false;
	}
	public BindingList variants(Term term, BindingList bindings) {
		if (equals(term)) { return bindings; }
		return null;
	}
	
	public boolean freeVariablesAfterSubstitution(BindingList theta) {
		return false;
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return toString(precedenceOfCaller, bindingList);
	}
	protected String toString(int precedenceOfCaller, BindingList bindingList) {
		return "objectAsTerm(" + item + ")";
	}
	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return (item == v ? 1 : 2); // This is probably inadequate.  Maybe always return 2 if a non-match to be safe?
	}

}
