package edu.wisc.cs.will.MLN_Task;

import edu.wisc.cs.will.FOPC.BindingList;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.Utils.Utils;

/**
 * A GroundLiteral class.
 * 
 * Note: GroundLiterals are never negated (nor should they have weights other than infinity).  This is done so they can be canonically represented.
 *       Users of GroundLiterals need to manage whether or not they are negated (e.g., by keeping them in separate lists, sets, etc.).
 * 
 * @author pavan and shavlik
 */
public class GroundLiteral extends Literal {
	private static final long serialVersionUID = 1L;
	private boolean            value = false; // The truth value of the GroundLiteral.  These default to false.
	boolean  hasBeenInterned = false; //  All the ground clauses containing this literal have been computed.
	private Block                      block; // The block this ground literal is contained in.
	private Set<GroundClause>   gndClauseSet; // Ground literals need to point to the ground clauses in which they appear.
	private Object                    marker;

	// These are protected because ground literals should be created via MLN_Task.getCanonicalRepresentative().
	private GroundLiteral(HandleFOPCstrings stringHandler, PredicateName pName) {
		super(stringHandler, pName);
		block = null;
	}

	GroundLiteral(Literal parent) { // Note we don't check here that all arguments are constants (and some facts do slip through, intentionally, with variables in them - see factsWithVariables in GroundThisMarkovNetwork).
		this(parent.getStringHandler(), parent.predicateName);
		List<Term> arguments2 = new ArrayList<>(parent.numberArgs());  // For zero-arity literals, we do this to prevent accessing nulls and also so parentheses print, ie 'p()' instead of 'p'.
		if (parent.numberArgs() > 0) {
			arguments2.addAll(parent.getArguments());
		}
		setArguments(arguments2);
		this.setWeightOnSentence(parent.getWeightOnSentence());
	}
	
	public void setMarker(Object marker) {
		this.marker = marker;
	}
	public Object getMarker() {
		return marker;
	}

	public Set<GroundLiteral> getNeighbors() {
		Set<GroundLiteral> neighbors = null;
		for (GroundClause gndClause : gndClauseSet) {
			int length = gndClause.getLength();
			for (int i = 0; i < length; i++) {
				GroundLiteral gLit = gndClause.getIthLiteral(i);
				if (gLit != this && (neighbors == null || !neighbors.contains(gLit))) {
					if (neighbors == null) { neighbors = new HashSet<>(4); }
					neighbors.add(gLit);
				}
			}
		}
		if (debugLevel > 1) { Utils.println("Neighbors: "); for (GroundLiteral gndLit : neighbors) { Utils.println("   " + gndLit);	} }
		return neighbors;
	}

	/**
	 * @return The Set of GroundClauses this literal appears in.
	 */
	Set<GroundClause> getGndClauseSet() {
		return gndClauseSet;
	}
	
	/**
	 * Empties the GroundClauseList
	 */
	void clearGndClauseSet() {
		if (gndClauseSet == null) { gndClauseSet = new HashSet<>(4); }
		else { gndClauseSet.clear(); }
	}
	
	
	/**
	 * @param gndClause The GroundClause to be added to the GroundClause List.
	 */
	void addGndClause(GroundClause gndClause) {
		if (gndClauseSet == null) { clearGndClauseSet(); }
		gndClauseSet.add(gndClause); // Since a set, will handle duplicates.
	}	
	
	/**
	 * @param value Assign this to the truth value of the GroundLiteral.
	 */
	void setValue(boolean value, GroundedMarkovNetwork groundedMarkovNetwork, TimeStamp timeStamp) {
		setValue(value, groundedMarkovNetwork, timeStamp, true);
	}
	private void setValue(boolean value, GroundedMarkovNetwork groundedMarkovNetwork, TimeStamp timeStamp, boolean complain) {
		this.value = value;
		if (groundedMarkovNetwork == null) { return; }
		updateAllContainingGroundClauses(groundedMarkovNetwork, timeStamp, complain);
	}
	void setValueOnly(boolean value, TimeStamp timeStamp) {
		this.value = value; // Only set this value.  Don't update all clauses containing this literal.  Note: this is dangerous unless another setValue is called soon!
	}
	
	String getValueAndInfo() {
		String result = "";
		if (value) { return "true" + result; }
		return "false" + result;
	}
	
	private void updateAllContainingGroundClauses(GroundedMarkovNetwork groundedMarkovNetwork, TimeStamp timeStamp, boolean complainIfInconsistent) {
		if (gndClauseSet == null) { Utils.error("Have gndClauseSet=null for '" + this + "'."); }
		for (GroundClause gndClause : gndClauseSet) if (groundedMarkovNetwork.isaMarkedGroundClause(gndClause)) {
			boolean old    = gndClause.isSatisfiedCached();
			boolean result = gndClause.checkIfSatisfied(timeStamp);  // TODO - depending on sign and value of ground lit and clause state, might not need to check
			if (complainIfInconsistent && gndClause.getWeightOnSentence() > 0 && !old &&  result && !gndClause.isActive()) { Utils.error("due to, '" + this + "' = " + value + ", this clause is becoming satisfied (and inactive) but it is already inactive: " + gndClause.getInfo()); }
			if (complainIfInconsistent && gndClause.getWeightOnSentence() > 0 &&  old && !result &&  gndClause.isActive()) { Utils.error("due to, '" + this + "' = " + value + ", this clause is becoming unsatisfied (and active) but it is already active: "   + gndClause.getInfo()); }
			if (complainIfInconsistent && gndClause.getWeightOnSentence() < 0 &&  old && !result && !gndClause.isActive()) { Utils.error("due to, '" + this + "' = " + value + ", this clause is becoming satisfied (and inactive) but it is already inactive: " + gndClause.getInfo()); }
			if (complainIfInconsistent && gndClause.getWeightOnSentence() < 0 && !old &&  result &&  gndClause.isActive()) { Utils.error("due to, '" + this + "' = " + value + ", this clause is becoming unsatisfied (and active) but it is already active: "   + gndClause.getInfo()); }
	 	}
	}
	
	/**
	 * @return The truth value of the GroundLiteral.
	 */
	public boolean getValue() {
		return value;
	}
	
	public void setBlock(Block block) {
		this.block = block;
	}
	
	public Block getBlock() {
		return block;
	}

	boolean matchesThisGroundLiteral(Literal other) {
		if (this == other) { return true; }
		if (predicateName != other.predicateName)   { return false; }
		int thisNumberOfArgs = numberArgs();
		if (thisNumberOfArgs != other.numberArgs()) { return false; }
		for (int i = 0; i < thisNumberOfArgs; i++) {
			Term thisTerm  =       getArgument(i);
			Term otherTerm = other.getArgument(i);
			if (!thisTerm.equals(otherTerm)) { return false; }
		}
		return true;
	}

	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return "{ value = " + value + " : " + super.toString(precedenceOfCaller, bindingList) + "}";
	}

		
}