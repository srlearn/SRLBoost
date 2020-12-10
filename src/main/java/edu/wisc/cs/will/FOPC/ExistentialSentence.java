package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author shavlik
 *
 */
public class ExistentialSentence extends QuantifiedSentence {
	private static final long serialVersionUID = -2183308218806549657L;

	ExistentialSentence(HandleFOPCstrings stringHandler, Collection<Variable> variables, Sentence body) {
		this.stringHandler = stringHandler;
		this.variables     = variables;
		this.body          = body;
		if (variables == null || variables.size() < 1) { Utils.error("Must have at least one quantified variable in a quantified sentences."); }
		if (body      == null) { Utils.error("Cannot have an empty body in a quantified sentences."); }
	}
	
    @Override
	public ExistentialSentence copy(boolean recursiveCopy) { // recursiveCopy=true means that the copying recurs down to the leaves. 
		if (recursiveCopy) {
			stringHandler.stackTheseVariables(variables);
			Collection<Variable> newVariables = new ArrayList<>(variables.size());
			for (Variable var : variables) {
				newVariables.add(var.copy(true));
			}
			Sentence            newBody = body.copy(true);
			ExistentialSentence result  = (ExistentialSentence) stringHandler.getExistentialSentence(newVariables, newBody).setWeightOnSentence(wgtSentence);
			stringHandler.unstackTheseVariables(variables);
			return result;	
		}
		return (ExistentialSentence) stringHandler.getExistentialSentence(variables, body).setWeightOnSentence(wgtSentence);
	}

    @Override
	public ExistentialSentence copy2(boolean recursiveCopy, BindingList bindingList) { // recursiveCopy=true means that the copying recurs down to the leaves.
		if (recursiveCopy) {
			Collection<Variable> newVariables = new ArrayList<>(variables.size());
			for (Variable var : variables) {
				newVariables.add(var.copy2(true, bindingList));
			}
			Sentence            newBody = body.copy2(true, bindingList);
			return (ExistentialSentence) stringHandler.getExistentialSentence(newVariables, newBody).setWeightOnSentence(wgtSentence);
		}
		return (ExistentialSentence) stringHandler.getExistentialSentence(variables, body).setWeightOnSentence(wgtSentence);
	}

    @Override
	public boolean containsFreeVariablesAfterSubstitution(BindingList theta) {
		if (body == null || theta == null) { return false; }
		return body.containsFreeVariablesAfterSubstitution(theta);
	}

    @Override
	public ExistentialSentence applyTheta(Map<Variable,Term> bindings) {
		Sentence newBody = body.applyTheta(bindings);
		return (ExistentialSentence) stringHandler.getExistentialSentence(variables, newBody).setWeightOnSentence(wgtSentence);
	}

	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((variables == null) ? 0 : variables.hashCode());
		result = prime * result + ((body      == null) ? 0 : body.hashCode());
		return result;
	}	
    @Override
	public boolean equals(Object other) { // This doesn't handle permuted variable binding lists.
		if (!(other instanceof ExistentialSentence)) { return false; }
		
		ExistentialSentence otherUsent = (ExistentialSentence) other;
		if (variables.size() != otherUsent.variables.size()) { return false; }
		for (Iterator<Variable> vars1 = variables.iterator(), vars2 = otherUsent.variables.iterator(); vars1.hasNext(); ) {
			Variable var1 = vars1.next();
			Variable var2 = vars2.next();
			
			if (!var1.equals(var2)) { return false; }
		}
		return body.equals(((ExistentialSentence) other).body);
	}
	
    @Override
	public BindingList variants(Sentence other, BindingList bindings) { // This doesn't handle permuted variable binding lists.
		if (!(other instanceof ExistentialSentence)) { return null; }
		
		BindingList bList2 = bindings;
		ExistentialSentence otherUsent = (ExistentialSentence) other;
		if (variables.size() != otherUsent.variables.size()) { return null; }
		for (Iterator<Variable> vars1 = variables.iterator(), vars2 = otherUsent.variables.iterator(); vars1.hasNext(); ) {
			Variable var1 = vars1.next();
			Variable var2 = vars2.next();
			
			bList2 = var1.variants(var2, bindings);
			if (bList2 == null) { return null; }
		}
		return body.variants(((ExistentialSentence) other).body, bList2);
	}

	// Clausal-form converter stuff.
    @Override
	protected boolean containsThisFOPCtype(String marker) {
		if (marker.equalsIgnoreCase("thereExists") || marker.equalsIgnoreCase("exists")) { return true; }
		return body.containsThisFOPCtype(marker);
	}
    @Override
	protected ExistentialSentence convertEquivalenceToImplication() {
		Sentence newBody = body.convertEquivalenceToImplication();
		return (ExistentialSentence) stringHandler.getExistentialSentence(variables, newBody).setWeightOnSentence(wgtSentence);
	}
    @Override
	protected ExistentialSentence eliminateImplications() {
		Sentence newBody = body.eliminateImplications();
		return (ExistentialSentence) stringHandler.getExistentialSentence(variables, newBody).setWeightOnSentence(wgtSentence);
	}
	// 'not ThereExists p' is equivalent to 'ForAll not(p)'
    @Override
	protected UniversalSentence negate() { // According to the original MLN paper (page 11), negative weights when moving a negation inward.  BUT since we're KEEPING the negation, we don't negate the weight here.
		Sentence negatedBody = body.negate();
		return (UniversalSentence) stringHandler.getUniversalSentence(variables, negatedBody).setWeightOnSentence(wgtSentence);
	}
    @Override
	protected ExistentialSentence moveNegationInwards() {
		Sentence newBody = body.moveNegationInwards();
		return (ExistentialSentence) stringHandler.getExistentialSentence(variables, newBody).setWeightOnSentence(wgtSentence);
	}
    @Override
	protected Sentence skolemize(List<Variable> outerUniversalVars) {
		BindingList bindings = new BindingList(); // Create a binding list for each existential variable here.
		for (Variable v : variables) {
			bindings.addBinding(v, stringHandler.createNewSkolem(outerUniversalVars, v.typeSpec));
		}
		Sentence newBody1 = body.applyTheta(bindings.theta); // Replace all these existential variables with their Skolem functions.
		if (body.wgtSentence < Sentence.maxWeight) { Utils.error("Dont know what to do when the weight on the body of an existential is not infinite."); }
		return newBody1.skolemize(outerUniversalVars).setWeightOnSentence(wgtSentence); // Pass the weight of the existential to the body (which has infinite weight).
	}	

    @Override
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		int    precedence = 1500;
		StringBuilder result     = new StringBuilder(returnWeightString() + "Exists ");
		if (variables.size() == 1) { return result.toString() + Utils.getIthItemInCollectionUnsafe(variables, 0) + " " + body.toPrettyString(newLineStarter, precedence, bindingList); }
		result.append("{");
		boolean firstTime = true;
		for (Variable var : variables) {
			if (firstTime) { firstTime = false; } else { result.append(", "); }
			result.append(var.toString());
		}
		return result + "} " + body.toPrettyString(newLineStarter, precedence, bindingList);
	}
    @Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		int    precedence = 1500;
		StringBuilder result     = new StringBuilder(returnWeightString() + "Exists ");
		if (variables.size() == 1) { return result.toString() + Utils.getIthItemInCollectionUnsafe(variables, 0) + " " + body.toString(precedence, bindingList); }
		result.append("{");
		boolean firstTime = true;
		for (Variable var : variables) {
			if (firstTime) { firstTime = false; } else { result.append(", "); }
			result.append(var.toString());
		}
		return result + "} " + body.toString(precedence, bindingList);
	}

    @Override
    public ExistentialSentence replaceVariablesAndBody(Collection<Variable> variables, Sentence body) {
        return getStringHandler().getExistentialSentence(variables, body);
    }

}
