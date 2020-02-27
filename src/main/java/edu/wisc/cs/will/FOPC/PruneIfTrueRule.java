package edu.wisc.cs.will.FOPC;

/*
 *
 * @author twalker
 */
public class PruneIfTrueRule implements PruningRule {

    public PruneIfTrueRule(Clause condition) {

        if (((DefiniteClause) condition).getDefiniteClauseHead().getArity() != 1) {
            throw new IllegalArgumentException("Pruning rule for duplicates requires form:  prune(AddedLiteral) :- body.");
        }
    }

}
