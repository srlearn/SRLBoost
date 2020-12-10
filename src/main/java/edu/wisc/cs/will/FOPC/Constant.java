package edu.wisc.cs.will.FOPC;

import java.util.Collection;
import java.util.Map;

/**
 * @author shavlik
 */
public abstract class Constant extends Term {

	Constant() { } // Compiler complains without this (for subtypes).

	public Constant applyTheta(Map<Variable,Term> theta) {
		return this;
	}

	public Constant copy(boolean recursiveCopy) { // No need to dive into constants (even to change their type spec's?).
		return this;
	}

    @Override
    public Term copy2(boolean recursiveCopy, BindingList bindingList) {
        return this;
    }
	
	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
		return null;
	}

    @Override
    public Sentence asSentence() {
        return null;
    }

	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		return super.hashCode();
	}
	public boolean equals(Object other) {
		return (this == other);
	}
	
	public boolean containsVariables() {
		return false;
	}
	
	// Variants and Equivalent mean the same for constants.
	public BindingList variants(Term other, BindingList bindings) {
		if (this == other) { return bindings; }
		return null;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}

}
