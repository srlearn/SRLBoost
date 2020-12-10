package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class PredicateSpec extends AllOfFOPC implements Serializable {
	private static final long serialVersionUID = -3286520989727441117L;
	private List<Term> signature;
	private List<TypeSpec> typeSpecList;
	private PredicateName  owner;
	private boolean        isaILPmode; // If true, then can be used to generate children in an ILP search.

	
	private PredicateSpec() {		
	}

	PredicateSpec(List<Term> signature, List<TypeSpec> typeSpecList, PredicateName owner) {
		this.signature    = signature;
		this.typeSpecList = typeSpecList;
		this.owner        = owner;
		this.isaILPmode   = true;
	}
	
	// Create a copy, but without all the type specifications.
	PredicateSpec strip() {
		PredicateSpec newSpec = new PredicateSpec();
		newSpec.typeSpecList = new ArrayList<>(this.typeSpecList.size());
		for (TypeSpec tspec : typeSpecList) {
			newSpec.typeSpecList.add(new TypeSpec(tspec.isaType, tspec.stringHandler));
		}
		newSpec.owner        = this.owner;
		newSpec.isaILPmode   = this.isaILPmode;
		newSpec.signature    = this.signature;
		return newSpec;
	}

	// Stick these arguments in the leaf nodes of this spec's signature.
	public List<Term> applyArgsToSignature(HandleFOPCstrings stringHandler, List<Term> args) {
		return help_applyArgsToSignature(stringHandler, signature, 0, args);
	}

	private List<Term> help_applyArgsToSignature(HandleFOPCstrings stringHandler, List<Term> sig, int counter, List<Term> args) {
		assert args != null;
		assert sig != null;

		List<Term> result = new ArrayList<>(sig.size());
		if (args.size() != sig.size()) { Utils.error("Have args = " + args + " but sig = " + sig); }
		for (Term item : sig) {
			if (item instanceof Constant) {
				result.add(args.get(counter));
				counter++;
			} else if (item instanceof Function) {
				Function f = (Function) item;
				result.add(stringHandler.getFunction(f.functionName, help_applyArgsToSignature(stringHandler, f.getArguments(), counter, args), f.typeSpec));
				counter += f.countLeaves();				
			} else { Utils.error("Should not have item=" + item + " sig=" + sig + " args=" + args); }
		}
		return result;
	}
	
	public List<Term> getSignature() {
		return signature;
	}

	public List<TypeSpec> getTypeSpecList() {
		return typeSpecList;
	}

    public TypeSpec getTypeSpec(int argument) {
        if (typeSpecList == null) {
            return null;
        }
        else {
            return typeSpecList.get(argument);
        }
    }

	public int getArity() {
        if (typeSpecList == null) {
            return 0;
        }
        return typeSpecList.size();
    }

	public boolean isaILPmode() {
		return isaILPmode;
	}

	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((owner        == null) ? 0 : owner.hashCode());
		result = prime * result + ((typeSpecList == null) ? 0 : typeSpecList.hashCode());
		result = prime * result + ((signature    == null) ? 0 : signature.hashCode());
		return result;
	}

    @Override
	public boolean equals(Object otherAsObject) {
		if (!(otherAsObject instanceof PredicateSpec)) { return false; }
		PredicateSpec other = (PredicateSpec) otherAsObject;
		if (owner        != other.owner)         { return false; }
		if (typeSpecList == other.typeSpecList)  { return true;  } // This will handle case where both are null.
		if (typeSpecList == null || other.typeSpecList == null) { return false; }
		if (typeSpecList.size() != other.typeSpecList.size())   { return false; }
		int size = typeSpecList.size();
		for (int i = 0; i < size; i++) {
			TypeSpec one = typeSpecList.get(i);
			TypeSpec two = other.typeSpecList.get(i);
			if (one == null || two == null) { 
				if (one == null && two == null) { continue; }
				return false;
			}
			if (!one.equals(two)) { return false; }
		}
		return true;
	}

    @Override
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return "signature = " + signature + ", types = " + typeSpecList;
	}

    @Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return "signature = " + signature + ", types = " + typeSpecList;
	}

	@Override
	public PredicateSpec applyTheta(Map<Variable, Term> bindings) {
		return this;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}

}
