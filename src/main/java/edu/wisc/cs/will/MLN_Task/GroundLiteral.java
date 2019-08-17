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

	Set<GroundClause> getGndClauseSet() {
		return gndClauseSet;
	}

	void clearGndClauseSet() {
		if (gndClauseSet == null) { gndClauseSet = new HashSet<>(4); }
		else { gndClauseSet.clear(); }
	}

	void addGndClause(GroundClause gndClause) {
		if (gndClauseSet == null) { clearGndClauseSet(); }
		gndClauseSet.add(gndClause); // Since a set, will handle duplicates.
	}

	void setValueOnly() {
		this.value = false; // Only set this value.  Don't update all clauses containing this literal.  Note: this is dangerous unless another setValue is called soon!
	}
	
	String getValueAndInfo() {
		String result = "";
		if (value) { return "true" + result; }
		return "false" + result;
	}

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