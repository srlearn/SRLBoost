package edu.wisc.cs.will.FOPC;

/*
 * @author twalker
 */
public class PruneDuplicatesIfTrueRule implements PruningRule {

    public PruneDuplicatesIfTrueRule(Clause condition) {

        if ( ((DefiniteClause) condition).getDefiniteClauseHead().getArity() != 2 ) {
            throw new IllegalArgumentException("Pruning rule for duplicates requires form:  prune(ExistingLiteral, AddedLiteral) :- body.");
        }
    }

}
