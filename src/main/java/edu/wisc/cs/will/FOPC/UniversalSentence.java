package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author shavlik
 */
public class UniversalSentence extends QuantifiedSentence {

	UniversalSentence(HandleFOPCstrings stringHandler, Collection<Variable> variables, Sentence body) {
		this.variables = variables;
		this.body      = body;
		this.stringHandler = stringHandler;
		if (variables == null || variables.size() < 1) { Utils.error("Must have at least one quantified variable in a quantified sentences."); }
		if (body      == null)                         { Utils.error("Cannot have an empty body in a quantified sentences."); }
	}
	
    @Override
	public UniversalSentence copy(boolean recursiveCopy) { // recursiveCopy=true means that the copying recurs down to the leaves. 
		if (recursiveCopy) {
			stringHandler.stackTheseVariables(variables);
			List<Variable> newVariables = new ArrayList<>(variables.size());
			for (Variable var : variables) {
				newVariables.add(var.copy(true));
			}
			Sentence newBody = body.copy(true);
			UniversalSentence result  = (UniversalSentence) stringHandler.getExistentialSentence(newVariables, newBody).setWeightOnSentence(wgtSentence);
			stringHandler.unstackTheseVariables(variables);
			return result;
		}
		return (UniversalSentence) stringHandler.getUniversalSentence(variables, body).setWeightOnSentence(wgtSentence);
	}

   @Override
	public UniversalSentence copy2(boolean recursiveCopy, BindingList bindingList) { // recursiveCopy=true means that the copying recurs down to the leaves.
		if (recursiveCopy) {
			List<Variable> newVariables = new ArrayList<>(variables.size());
			for (Variable var : variables) {
				newVariables.add(var.copy2(true, bindingList));
			}
			Sentence newBody = body.copy2(true, bindingList);
			return (UniversalSentence) stringHandler.getExistentialSentence(newVariables, newBody).setWeightOnSentence(wgtSentence);
		}
		return (UniversalSentence) stringHandler.getUniversalSentence(variables, body).setWeightOnSentence(wgtSentence);
	}


    @Override
	public boolean containsFreeVariablesAfterSubstitution(BindingList theta) {
		if (body == null || theta == null) { return false; }
		return body.containsFreeVariablesAfterSubstitution(theta);
	}

    @Override
	public UniversalSentence applyTheta(Map<Variable,Term> bindings) {
		Sentence newBody = body.applyTheta(bindings);
		return (UniversalSentence) new UniversalSentence(stringHandler, variables, newBody).setWeightOnSentence(wgtSentence);
	}


	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((body      == null) ? 0 : body.hashCode());
		result = prime * result + ((variables == null) ? 0 : variables.hashCode());
		return result;
	}	
    @Override
	public boolean equals(Object other) { // This doesn't handle permuted variable binding lists.
		if (!(other instanceof UniversalSentence)) { return false; }
		
		UniversalSentence otherUsent = (UniversalSentence) other;
		if (variables.size() != otherUsent.variables.size()) { return false; }
		for (Iterator<Variable> vars1 = variables.iterator(), vars2 = otherUsent.variables.iterator(); vars1.hasNext(); ) {
			Variable var1 = vars1.next();
			Variable var2 = vars2.next();
			
			if (!var1.equals(var2)) { return false; }
		}
		return body.equals(((UniversalSentence) other).body);
	}
	
    @Override
	public BindingList variants(Sentence other, BindingList bindings) { // This doesn't handle permuted variable binding lists.
		if (!(other instanceof UniversalSentence)) { return null; }
		
		BindingList bList2 = bindings;
		UniversalSentence otherUsent = (UniversalSentence) other;
		if (variables.size() != otherUsent.variables.size()) { return null; }
		for (Iterator<Variable> vars1 = variables.iterator(), vars2 = otherUsent.variables.iterator(); vars1.hasNext(); ) {
			Variable var1 = vars1.next();
			Variable var2 = vars2.next();
			
			bList2 = var1.variants(var2, bindings);
			if (bList2 == null) { return null; }
		}
		return body.variants(((UniversalSentence) other).body, bList2);
	}

	// Clausal-form converter stuff.
    @Override
	protected boolean containsThisFOPCtype(String marker) {
		if (marker.equalsIgnoreCase("forAll")) { return true; }
		return body.containsThisFOPCtype(marker);
	}
    @Override
	protected UniversalSentence convertEquivalenceToImplication() {
		Sentence newBody = body.convertEquivalenceToImplication();
		return (UniversalSentence) stringHandler.getUniversalSentence(variables, newBody).setWeightOnSentence(wgtSentence);
	}
    @Override
	protected UniversalSentence eliminateImplications() {
		Sentence newBody = body.eliminateImplications();
		return (UniversalSentence) stringHandler.getUniversalSentence(variables, newBody).setWeightOnSentence(wgtSentence);
	}
	// 'not ForAll p' is equivalent to 'ThereExists not(p)'
    @Override
	protected ExistentialSentence negate() { // According to the original MLN paper (page 11), negative weights when moving a negation inward.  BUT since we're KEEPING the negation, we don't negate the weight here.
		Sentence negatedBody = body.negate();
		return (ExistentialSentence) stringHandler.getExistentialSentence(variables, negatedBody).setWeightOnSentence(wgtSentence);
	}
    @Override
	protected UniversalSentence moveNegationInwards() {
		Sentence newBody = body.moveNegationInwards();
		return (UniversalSentence) stringHandler.getUniversalSentence(variables, newBody).setWeightOnSentence(wgtSentence);
	}
	// Also DROP the universal quantifiers at this point.
    @Override
	protected Sentence skolemize(List<Variable> outerUniversalVars) {
		List<Variable> newVariablesList = (outerUniversalVars == null ? new ArrayList<>(variables.size()) // Make a fresh list for possible later appending.
																	  : outerUniversalVars);
		newVariablesList.addAll(variables);
		Sentence newBody = body.skolemize(newVariablesList);
		if (body.wgtSentence < Sentence.maxWeight) { Utils.error("Don't know what to do when the weight on the body of an existential is not infinite."); }
		return newBody.setWeightOnSentence(wgtSentence); // Pass the weight of the universal to the body (which has infinite weight).
	}

    @Override
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		int    precedence = 1500;
		StringBuilder result     = new StringBuilder(returnWeightString() + "ForAll ");
		if (variables.size() == 1) { return result.toString() + Utils.getIthItemInCollectionUnsafe(variables, 0) + " " + body.toPrettyString(newLineStarter, precedence, bindingList); }
		result.append("{");
		boolean firstTime = true;
		for (Variable var : variables) {
			if (firstTime) { firstTime = false; } else { result.append(", "); }
			result.append(var.toPrettyString(newLineStarter, precedence, bindingList));
		}
		return result + "} " + body.toPrettyString(newLineStarter, precedence, bindingList);
	}

    @Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		int    precedence = 1500;
		StringBuilder result     = new StringBuilder(returnWeightString() + "ForAll ");
		if (variables.size() == 1) { return result.toString() + Utils.getIthItemInCollectionUnsafe(variables, 0) + " " + body.toString(precedence, bindingList); }
		result.append("{");
		boolean firstTime = true;
		for (Variable var : variables) {
			if (firstTime) { firstTime = false; } else { result.append(", "); }
			result.append(var.toString());
		}
		return result + "} " + body.toString(precedence, bindingList);
	}

}
