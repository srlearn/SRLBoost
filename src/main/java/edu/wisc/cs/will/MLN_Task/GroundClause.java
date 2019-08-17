package edu.wisc.cs.will.MLN_Task;
import java.util.ArrayList;
import java.util.List;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.Utils.Utils;

/**
 * A GroundClause class composed of GroundLiterals.
 * Contains utility methods like the change of cost
 * when a particular literal is flipped.
 * 
 * 
 * Make cases of these for use by GroundThisMarkovNetwork
 *  - only those literals that are satisfiable
 *  - keep a representsThisMany int
 *  
 *  - assume ALWAYS true, so need to 'subtract' out the #false
 *  - if always false: if current settings are in the false's
 * 
 * @author pavan and shavlik
 */
public class GroundClause extends Clause {

	private static final long serialVersionUID = 1L;
	// TODO the FOPC classes probably should have these as well, but then need to be careful about adding or subtracting literals.
	private boolean isSatisfiedCached = true;  // Store this so no need to repeatedly compute.  Default is that clauses are satisfied.
	private boolean isActive          = false; // use this instead of making sets. 
	private Object  marker            = null;
	short   age               = 0; // Used to get rid of old 'lazy' clauses.
	private List<Term> freeVarBindings = null; //  Sometimes we need to use VARIABLE bindings to show that two ground clauses are the same.
	
	GroundClause(MLN_Task task, Clause parent, double multiplier, List<Term> freeVarBindings, TimeStamp timeStamp) {
		super(task.stringHandler, null, null);
		// Now need to convert the parent's literals to grounded versions.
		if (parent.posLiterals != null) for (Literal pLit : parent.posLiterals) {
			if (posLiterals == null) { posLiterals = new ArrayList<Literal>(1); }
			posLiterals.add(task.getCanonicalRepresentative(pLit));
		}
		if (parent.negLiterals != null) for (Literal nLit : parent.negLiterals) {
			if (negLiterals == null) { negLiterals = new ArrayList<Literal>(1); }
			negLiterals.add(task.getCanonicalRepresentative(nLit));
		}
		this.freeVarBindings = freeVarBindings;
		setWeightOnSentence(parent.getWeightOnSentence());
		setLiteralInfo(timeStamp);  // Need to recompute length, etc.
	}

	GroundClause(Clause parent, List<Literal> posLiterals, List<Literal> negLiterals, double multiplier, List<Term> freeVarBindings, TimeStamp timeStamp) { // These literals should be GroundLiterals, but need to be Literal for the super() constructor.
		super(parent.getStringHandler(), posLiterals, negLiterals);
		this.setWeightOnSentence(multiplier * parent.getWeightOnSentence());
		this.freeVarBindings = freeVarBindings;
		setWeightOnSentence(parent.getWeightOnSentence());
		setLiteralInfo(timeStamp);
	}

	private void setLiteralInfo(TimeStamp timeStamp) {
		// Connect this ground clause and its ground literals.
		if (negLiterals != null) for (Literal nLit : negLiterals) {
			((GroundLiteral) nLit).addGndClause(this);
		}
		if (posLiterals != null) for (Literal pLit : posLiterals) {
			((GroundLiteral) pLit).addGndClause(this);
		}
		checkIfSatisfied(timeStamp);
	}
	
	public void setMarker(Object marker) {
		if (marker != null) { age = 0; } // In case this is a lazy clause, also note that it was recently marked.
		this.marker = marker;
	}
	public Object getMarker() {
		return marker;
	}
	
    @Override
	public int hashCode() {
		if (stringHandler.usingStrictEqualsForClauses()) { return super.hashCode(); }
		final int prime = 31;
		int result = 1;
		result = prime * result + ((freeVarBindings == null) ? 0 : freeVarBindings.hashCode());
		return result;
	}
	
    @Override
	public boolean equals(Object other) {
		if (this == other) { return true; } 

		if (stringHandler.usingStrictEqualsForClauses()) { return false; }
		return sameGroundingDifferentInstances(other); // Note: we already did the "same instance" test.
	}
	
	// We want to see here if duplicate groundings from the SAME PARENT.
	private boolean sameGroundingDifferentInstances(Object other) {
		if (this == other) { return false; } // SAME instances
				
		if (!(other instanceof GroundClause)) { return false; }
		GroundClause otherAsGroundClause = (GroundClause) other;
	
		if (freeVarBindings == null) { Utils.error("Should not call this if size = 0"); } // Note: for clauses with NO variables, make an empty list.
		if (getLength() != otherAsGroundClause.getLength()) { return false; }
		if (freeVarBindings.size() != otherAsGroundClause.freeVarBindings.size()) { return false; }
		for (int i = 0 ; i < freeVarBindings.size(); i++) {
			if (freeVarBindings.get(i) != otherAsGroundClause.freeVarBindings.get(i)) { return false; }
		}
		return true;
	}
	
	boolean sameClause(GroundClause gndClause) {
		if (this == gndClause) { return true; }
		if (getLength() != gndClause.getLength()) { return false; }
		for (int i = 0; i < getLength(); i++) {
			if (getIthLiteral(i) != gndClause.getIthLiteral(i)) { return false; }
		}
		return true;
	}
	
	// Override by updating the type.
    @Override
	public GroundLiteral getIthLiteral(int i) {
		return (GroundLiteral) super.getIthLiteral(i);
	}

	boolean checkIfSatisfied(TimeStamp timeStamp) {
		boolean newSat = checkIfSatisfiedIfThisGroundLiteralIsFlipped(null);
		if (isSatisfiedCached != newSat) { 
			isSatisfiedCached         = newSat;
		}
		return isSatisfiedCached;
	}	
	public String getInfo() {
		String result = "";
		return result + groundClauseSettingToString();
	}

	// See if this clause is satisfied IF the truth value of this ground literal is flipped.
	private boolean checkIfSatisfiedIfThisGroundLiteralIsFlipped(GroundLiteral gLit) { // Be sure to check ALL literals here, even if not marked.
		if (getLength() < 1) { return false; }
		for (int i = 0; i < getLength(); i++) {
			GroundLiteral thisLit = getIthLiteral(i); if (thisLit == null) { Utils.error("should not have thisLit=null"); }
			if (thisLit == gLit) { if (thisLit.getValue() != getSignOfIthLiteral(i)) { return true; } }
			else                   if (thisLit.getValue() == getSignOfIthLiteral(i)) { return true; }
		}		
		return false;
	}
	
	boolean isSatisfiedCached() {
		return isSatisfiedCached;
	}
	public boolean isActive() {
		return isActive; // Let external code define and compute this.
	}
	public void setActive(boolean value) {
		isActive = value;
	}
	
	// Create a string the shows the literals and their current values.
	private String groundClauseSettingToString() {
		int counter = 0;
		String result = returnWeightString() + "[ ";
		if (posLiterals != null) for (Literal posLit : posLiterals) {
			if (++counter > 25) { return result += " ... ]"; }
			result += "posLit: " + posLit + "=" + ((GroundLiteral) posLit).getValueAndInfo() + " ";
		}
		if (negLiterals != null) for (Literal negLit : negLiterals) {
			if (++counter > 25) { return result += " ... ]"; }
			result += "negLit: " + negLit + "=" + ((GroundLiteral) negLit).getValueAndInfo() + " ";
		}
		return result + "]";
	}	
	String groundClauseSettingToString(GroundThisMarkovNetwork groundedMarkovNetwork) {
		int counter = 0;
		String result = returnWeightString() + markerForGndClause(groundedMarkovNetwork) + "[ ";
		if (posLiterals != null) for (Literal posLit : posLiterals) {
			if (++counter > 25) { return result += " ... ]"; }
			result += "posLit: " + markerForGndLit((GroundLiteral) posLit, groundedMarkovNetwork) + posLit + "=" + ((GroundLiteral) posLit).getValueAndInfo() + " ";
		}
		if (negLiterals != null) for (Literal negLit : negLiterals) {
			if (++counter > 25) { return result += " ... ]"; }
			result += "negLit: " + markerForGndLit((GroundLiteral) negLit, groundedMarkovNetwork) + negLit + "=" + ((GroundLiteral) negLit).getValueAndInfo() + " ";
		}
		return result + "]";
	}
	private String markerForGndClause(GroundThisMarkovNetwork groundedMarkovNetwork) {
		if (groundedMarkovNetwork.isaMarkedGroundClause(this)) { return "*"; } else { return ""; }
	}
	private String markerForGndLit(GroundLiteral gLit, GroundThisMarkovNetwork groundedMarkovNetwork) {
		if (groundedMarkovNetwork.isaMarkedGroundLiteral(gLit)) { return "*"; } else { return ""; }
	}

	@Override
	public String toPrettyString() {
		String result = super.toPrettyString(Integer.MIN_VALUE);
		result += " (is_satisfied_cached = " + isSatisfiedCached + ") ";
		return result;
	}

}
