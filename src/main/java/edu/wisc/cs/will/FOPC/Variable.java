package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import edu.wisc.cs.will.Utils.Utils;

import java.io.IOException;
import java.util.*;

public class Variable extends Term {

    private static final boolean useShortNames = true; // If false, will write out x1, x2, etc so printouts are more readable during debugging.

    public String name;

    public long counter; // This isn't used in the internal code (instead, instances are compared, not string names), but each variable has a unique counter value, and printing this can help with debugging.

    private Variable() {
    }
    /*
     * The way this works is that a request for variable 'x' will always return the SAME instance,
     * UNTIL Variable.resetAllVariables() is called or a new instance is pushed onto the stack.  Each time a new sentence is created, this reset
     * method should be called, so that new occurrences of 'x' become different instances (and hence wont unify).  The variables of a
     * quantifier should be pushed then popped when the scope of the quantifier is exited.
     *
     */
    Variable(HandleFOPCstrings stringHandler, String name, long counter, TypeSpec typeSpec) { // This is protected because getVariable(String name) should be used instead.
        this(stringHandler, name, counter, typeSpec, false);
    }
    Variable(HandleFOPCstrings stringHandler, String name, long counter, TypeSpec typeSpec, boolean isaGeneratedVar) { // This is protected because getVariable(String name) should be used instead.
    	this();
        this.name = name; // DON'T CALL THESE DIRECTLY.  GO VIA HandleFOPCstrings.
        this.counter = 2 * counter; if (isaGeneratedVar) { this.counter++; } // Odd values indicate variables that are generated (say adding another instance variable).
        this.setTypeSpec(typeSpec);
        this.stringHandler = stringHandler;
    }

    // Note: here we are recursively looking up until no more lookup's possible.  Note this means that if not found, we return the var itself.
    @Override
    public Term applyTheta(Map<Variable, Term> theta) {
        Term lookup = theta.get(this);

        if (lookup == this) {
            return this;
        } // When dealing with isVariant, need to match ?X to ?X sometimes, so prevent an infinite loop.
        return (lookup == null ? this : lookup.applyTheta(theta)); // If not in the binding list (i.e., theta) then stays the same.
    }

    @Override
    public Variable copy(boolean recursiveCopy) {
        // June 2010: JWS added the null below to skip the check for isaConstantType since we know this is a variable (but possibly some flag changed in between?).
        Variable copy = (isaGeneratedVariable()
        					? stringHandler.getGeneratedVariable(typeSpec, getNameToUse(name), false)
        					: stringHandler.getExternalVariable( typeSpec, getNameToUse(name), false)); // If we make a copy, use the correct name for the settings of what denotes a variable.
        if (typeSpec != null) {
            copy.typeSpec = (recursiveCopy ? typeSpec.copy() : typeSpec);
        }
        return copy;
    }

    @Override
    public Variable copy2(boolean recursiveCopy, BindingList bindingList) {

        Variable copy;

        if ( bindingList == null ) {
            return this;
        }
        else {
            Term term = bindingList.lookup(this);
            if ( term != null ) {
                copy = (Variable) term;
            }
            else {

                if (isaGeneratedVariable()) {
                    if ( name == null ) {
                        copy = stringHandler.getNewUnamedVariable();
                    }
                    else {
                        copy = stringHandler.getGeneratedVariable(typeSpec, name, true);
                    }
                }
                else {
                    copy = stringHandler.getExternalVariable(typeSpec, getNameToUse(name), true); // If we make a copy, use the correct name for the settings of what denotes a variable.
                }

                if (typeSpec != null) {
                    copy.typeSpec = (recursiveCopy ? typeSpec.copy() : typeSpec);
                }

                bindingList.addBinding(this, copy);
            }

            return copy;
        }
    }


    
    private boolean isaGeneratedVariable() {
    	return (counter % 2 == 1);
    }

    @Override
    public Sentence asSentence() {
        return null;
    }

    @Override
    public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
        if (boundVariables != null && boundVariables.contains(this)) {
            return null;
        } // In the list, so not free.
        Collection<Variable> result = new ArrayList<>(1);
        result.add(this);
        return result;
    }

    @Override
    public BindingList variants(Term other, BindingList bindings) {
        if (!(other instanceof Variable)) {
            return null;
        } // Both must be variables.
        Term lookupA = bindings.theta.get(this);
        Term lookupB = bindings.theta.get(other);

        if (lookupA == null && lookupB == null) { // Need to record these two are matched.
            bindings.theta.put(this, other);
            if (this != other) {
                bindings.theta.put((Variable) other, this);
            } // Need to map both to the other.
            return bindings;
        }
        if (lookupA == other && lookupB == this) {
            return bindings;
        } // If one is bound to something, then they must both be bound to each other.
        return null;
    }

    // Are these two variables equals?  Must be the same instance by construction.  Note: this is more strict than asking if two variables unify.

    @Override
    public boolean equals(Object other) {  //Utils.println("are these eq: " + this + " and " + other);
        return (this == other);
    }

    // Append two lists, but don't include any duplicates (assume the two lists already are duplicate free).
    static Collection<Variable> combineSetsOfVariables(Collection<Variable> listA, Collection<Variable> listB) {

        if (listA == null && listB == null) {
            return null;
        }
        if (listA == null) {
            return listB;
        }
        if (listB == null) {
            return listA;
        }
        List<Variable> result = new ArrayList<>(listA.size() + listB.size());

        for (Variable v : listA) {
            if (!result.contains(v)) {
                result.add(v);
            }
        }
        for (Variable v : listB) {
            if (!result.contains(v)) {
                result.add(v);
            }
        }

        return result;
    }

    @Override
    public boolean containsVariables() {
        return true;
    }

    @Override
    public boolean freeVariablesAfterSubstitution(BindingList theta) {
        if (theta == null) {
            return false;
        }
        // Unbound.
        return theta.lookup(this) == null;
    }

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        if (!(that instanceof Variable)) {
            return null;
        }

        Variable thatVar = (Variable) that;

        Term boundTo = bindings.lookup(this);
        // If the lookup fails, there is still
        // a chance that the variable was mapped
        // to itself.  If that is so, then the new variable
        // must map through correctly too.
        if ( boundTo == null ) {
            boundTo = bindings.getMapping(this);
        }

        if (boundTo != null) {
            if (boundTo == thatVar) {
                return bindings;
            }
            else {
                return null;
            }
        }

        Variable reverseBinding = bindings.reverseLookup(thatVar);

        if (reverseBinding == null) {
            bindings.addBinding(this, thatVar);
            return bindings;
        }

        return null;

    }

    private String toTypedString() {
        StringBuilder sb = new StringBuilder();
        appendTypedString(sb);
        return sb.toString();
    }

    private String getNameToUse(String name) {
    	if (name == null) { return getAnonNameToUse(); }
        // See if we need to print this variable using a different notation for what was used when read.
        if (name.charAt(0) == '_') {
            return name;
        } // Variables starting with an underscores are the same in all notations.
        if (stringHandler.doVariablesStartWithQuestionMarks()) {
            if (name.charAt(0) != '?') {
                return "?" + name;
            }
            return name;
        }
        else if (stringHandler.isaConstantType(name)) {
            if (name.charAt(0) == '?') {
                return getNameToUse(name.substring(1)); // Drop the leading question mark.
            }
			return Utils.changeCaseFirstChar(name);
        }
        return name;
    }

    @Override
    public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
        return toString(precedenceOfCaller, bindingList);
    }
    
    private String getAnonNameToUse() {
        if (!stringHandler.underscoredAnonymousVariables) {
            if (stringHandler.doVariablesStartWithQuestionMarks()) { return "?anon" + counter; }
            if (stringHandler.usingStdLogicNotation())             { return  "anon" + counter; }
            return "Anon" + counter;
        }
		if (stringHandler.doVariablesStartWithQuestionMarks()) { return "?_" + counter; }
		if (stringHandler.usingStdLogicNotation())             { return  "_" + counter; }
		return   "_" + counter;
    }

    public String toString(int precedenceOfCaller) {
        return toString(precedenceOfCaller, null);
    }

    @Override
    protected String toString(int precedenceOfCaller, BindingList bindingList) {
        if (stringHandler.printTypedStrings) {
            return toTypedString();
        }

        String stringToPrint = null;

        if (bindingList != null) {
            Term term = bindingList.lookup(this);
            if (term != null) {
                stringToPrint = ((StringConstant)term).getBareName();
            }
            else {
                StringConstant t = stringHandler.getAlphabeticalVariableName(bindingList.size());
                bindingList.addBinding(this, t);
                stringToPrint = t.getBareName();
            }
        }
        if (stringToPrint == null) {
            if (getName() == null) {
                stringToPrint = getAnonNameToUse();
            }
            else {
                stringToPrint = getNameToUse(getName());
                if (stringHandler.printVariableCounters) {
                    stringToPrint += "_" + counter;
                }
                else if (!useShortNames && counter > 0) {
                    stringToPrint += "_v" + counter;
                }
            }
        }
        return stringToPrint;
    }

    private void appendTypedString(Appendable appendable) {
        String nameToUse = getNameToUse(getName());

        try {
            if (typeSpec != null) {
                String modeString = typeSpec.getModeString();
                appendable.append(modeString).append(typeSpec.isaType.typeName).append(":").append(nameToUse);
            }
            else {
                appendable.append(nameToUse);
            }

            if (stringHandler.printVariableCounters) {
                String counterString = Long.toString(counter);
                appendable.append(":").append(counterString);
            }
            else if (!useShortNames && counter > 0) {
                String counterString = Long.toString(counter);
                appendable.append(" v").append(counterString);
            }

            if (typeSpec != null) {
                String s = typeSpec.getCountString();
                appendable.append(s);
            }
        } catch (IOException ignored) {
        }
    }

    /* Replace with the cached version from stringHandler.
     */
    private Object readResolve() {
    	if (isaGeneratedVariable()) {
    		return stringHandler.getGeneratedVariable(typeSpec, getNameToUse(getName()), false);
    	}
        return     stringHandler.getExternalVariable( typeSpec, getNameToUse(getName()), false); // Use the current name for a variable.
    }

    @Override
    public <Return, Data> Return accept(TermVisitor<Return, Data> visitor, Data data) {
        return visitor.visitVariable(this, data);
    }
    
	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return (this == v ? 1 : 0);
	}

    public String getName() {
        if ( name != null ) {
            return name;
        }
        else {
            return getNameToUse(null);
        }
    }


    @Override
    public int hashCode() {
        return Objects.hash(name, counter);
    }
}

