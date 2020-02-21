package edu.wisc.cs.will.FOPC;

import java.util.Objects;

/*
 * Allow the user to say that some predicate is relevant to the concept being learned.
 * The anticipated use is that the relevance strength will be mapped to a cost on a literal in a clause,
 * with higher relevance being lower cost.  However that is up to the code that uses this class.
 * 
 * There (currently) is no 'neutral' relevance - it is assumed that predicate/arity's not in a RelevantLiteral will implicitly have that value.
 *
 * @author shavlik
 *
 */
class RelevantLiteral {
	
	private final PredicateName     pName;
	private int               arity    = -1;  // If negative, any arity is fine. 
    private RelevanceStrength strength = RelevanceStrength.RELEVANT; // Default to saying something is relevant.

	/*
	 * Constructors for RelevantLiteral instances.
	 */
	private RelevantLiteral(PredicateName pName) {
		this.pName = pName;	
	}
	private RelevantLiteral(PredicateName pName, int arity) {
		this(pName);
		this.arity = arity;	
	}

	RelevantLiteral(PredicateName pName, int arity, RelevanceStrength strength) {
		this(pName, arity);
		this.strength = strength;		
	}

	public String toString() {
		return "Relevant: " + pName + "/" + arity + " strength=" + strength;
	}

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final RelevantLiteral other = (RelevantLiteral) obj;
        if (!Objects.equals(this.pName, other.pName)) {
            return false;
        }
        if (this.arity != other.arity) {
            return false;
        }
        return this.strength == other.strength;
	}

    @Override
    public int hashCode() {
        int hash = 5;
        hash = 23 * hash + (this.pName != null ? this.pName.hashCode() : 0);
        hash = 23 * hash + this.arity;
        // If set, says which ARGUMENT is relevant (counts from 1).
        int argument = -1;
        hash = 23 * hash + argument;
        hash = 23 * hash + (this.strength != null ? this.strength.hashCode() : 0);
        return hash;
    }
}
