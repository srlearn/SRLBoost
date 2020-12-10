package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import edu.wisc.cs.will.Utils.Utils;

import java.io.IOException;
import java.io.Serializable;
import java.util.Collection;
import java.util.Collections;
import java.util.Map;

/*
 * @author shavlik
 */
public abstract class Term extends AllOfFOPC implements Serializable, SLDQuery, Comparable<Term> {
	TypeSpec          typeSpec;
	transient HandleFOPCstrings stringHandler; // Add another field to everything so it can access this, and hence access things like lowercaseMeansVariable.

	Term() {} // DON'T CALL THESE DIRECTLY.  GO VIA HandleFOPCstrings.

	public TypeSpec getTypeSpec() {
		return typeSpec;
	}

	// Only allow ONE type per term?  Note: numbers should not have spec's.

	public void setTypeSpec(TypeSpec typeSpec) {
		if (     typeSpec == null) { return; }
		if (this.typeSpec == null) { this.typeSpec = typeSpec; return; }

		if (!this.typeSpec.equals(typeSpec)) {
			this.typeSpec.isNotYetSet();
		}
		int newMode =      typeSpec.mode;
		int oldMode = this.typeSpec.mode;
		if (newMode != oldMode) { this.typeSpec.mode = newMode; }
		Type newType = typeSpec.isaType;
		Type oldType = this.typeSpec.isaType;
		if (newType == oldType) { return; }
		if ( stringHandler.isaHandler.isa(oldType, newType)) { return; } // Keep the more specific type.
		if (!stringHandler.isaHandler.isa(newType, oldType)) { Utils.error("Cannot set the type of '" + this + "' to '" + typeSpec + "' since it already is of type '" + this.typeSpec + "'\nand neither is an subclass of the other"); }
		this.typeSpec.isaType = newType;
	}

	Term copyAndRenameVariables() {
		stringHandler.pushVariableHash();
		Term result = copy(true);
		stringHandler.popVariableHash();
		result.typeSpec = typeSpec;
		return result;
	}

	public abstract Term           applyTheta(Map<Variable,Term> bindings) ;
	public abstract Term           copy(boolean recursiveCopy);
    public abstract Term           copy2(boolean recursiveCopy, BindingList bindingList);
	public abstract BindingList    variants(Term term, BindingList bindings);
	public abstract boolean        containsVariables();
	public abstract boolean        freeVariablesAfterSubstitution(BindingList theta);
	public abstract Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables);
	
	public boolean isGrounded() { return !containsVariables(); }


	@Override
	public int compareTo(Term otherTerm) { // Could be made more efficient for subclasses if this ends up taking too much time.
		return toString().compareTo(otherTerm.toString());
	}
	
    /* Returns the term in the form of a sentence.
     *
     * Not all terms have sentence representations.  For example, there is no
     * sentence representation for a NumericConstant.  If no sentence representation
     * exists, null is returned.
     *
     * @return Sentence representation of this term, or null if one does not exist.
     */
    public abstract Sentence       asSentence();

    /* Returns the Term as a clause.
     * @return Clause represented by the term, or null if one does not exist.
     */
    public Clause         asClause() { return null; }

	public Literal asLiteral() {
        Utils.error("Term '" + this + "' can not be converted to a Literal.");
        return null;
    }

    public <Return,Data> Return accept(TermVisitor<Return,Data> visitor, Data data) {
        return visitor.visitOtherTerm(this);
    }


	public Clause getNegatedQueryClause() throws IllegalArgumentException {
        // We are going to just wrap the term in a literal for now.  The prover
        // probably won't know how to handle this yet, but that should be an easy enough
        // change to make.

        return stringHandler.getClause(null, Collections.singletonList(stringHandler.getTermAsLiteral(this)));
    }

	public abstract BindingList          isEquivalentUptoVariableRenaming(Term that, BindingList bindings);

	
   /* Methods for reading a Object cached to disk.
    */
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        if (!(in instanceof FOPCInputStream)) {
            throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject() input stream must support FOPCObjectInputStream interface");
        }

        in.defaultReadObject();

        FOPCInputStream fOPCInputStream = (FOPCInputStream) in;

        this.stringHandler = fOPCInputStream.getStringHandler();
    }

    public HandleFOPCstrings getStringHandler() {
        return stringHandler;
    }
}
