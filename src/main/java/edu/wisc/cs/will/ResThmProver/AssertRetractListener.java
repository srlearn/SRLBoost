package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.DefiniteClause;

/**
 * @author twalker
 */
public interface AssertRetractListener {
    void clauseAsserted(HornClausebase context, DefiniteClause clause);
    void clauseRetracted(HornClausebase context, DefiniteClause clause);
}
