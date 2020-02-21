package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

/*
 * @author shavlik
 *
 * Instances of this class hold information needed for a pruning a node from an ILP search.
 * This doesn't really belong in the FOPC class, but the PredicateName instance needs it, and putting it here avoids a circularity.
 *
 */
public class Pruner {
	private final Literal prunableLiteral;  // No need to add this literal to a clause that contains 'ifPresentLiteral.'
	private final Literal ifPresentLiteral;
	public final int     warnIfPresentLiteralCount; // If 'ifPresentLiteral' is the head of this many or more clauses, throw an error.  A negative value means "ignore this test."
	final int     truthValue;            // TruthValue: -1 means 'prune because false', 1 means because true, and 0 means unknown.

	Pruner(Literal prunableLiteral, Literal ifPresentLiteral, int warnIfPresentLiteralCount, int truthValue) {
		this.prunableLiteral           = prunableLiteral;
		this.ifPresentLiteral          = ifPresentLiteral;
		this.warnIfPresentLiteralCount = warnIfPresentLiteralCount;
		this.truthValue                = truthValue;
		if (warnIfPresentLiteralCount == 0) {
			Utils.error("Setting warnIfPresentLiteralCount=0 in a Pruner instance is invalid since it will always lead to a warning.\n  Use a negative number to mean 'do not check.'");
		}
	}

	public boolean isaMatch(Literal thisPrunableLiteral, Literal thisIfPresentLiteral) {
		BindingList bindings = Unifier.UNIFIER.unify(thisPrunableLiteral, prunableLiteral);
		
		if (bindings == null) { return false; }		
		if (thisIfPresentLiteral != null) { // NULL in this case means nothing needs to be present in the body.
			bindings = Unifier.UNIFIER.unify(thisIfPresentLiteral, ifPresentLiteral, bindings);
		}
		return (bindings != null);
	}

	public String toString() {
		if (warnIfPresentLiteralCount > 0) { return "pruner("+ prunableLiteral + ", " + ifPresentLiteral + ", " + warnIfPresentLiteralCount + ")"; }
		return "pruner("+ prunableLiteral + ", " + ifPresentLiteral + ")";
	}

}
