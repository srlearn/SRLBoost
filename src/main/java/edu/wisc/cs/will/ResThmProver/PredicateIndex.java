package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/* This is an index of definite clauses (either Clauses or Literal or a mix of both) indexed on the predicateName and arity.
 *
 * @param <T> Type of object to be indexed.
 *
 * @author twalker
 */
class PredicateIndex<T extends DefiniteClause> {

    private final Map<PredicateNameAndArity, List<T>> definiteClausesByPredicateIndex = new HashMap<>();

    void removeDefiniteClause(PredicateNameAndArity key, T definiteClause) {
        List<T> definiteClausesForKey = definiteClausesByPredicateIndex.get(key);
        if (definiteClausesForKey != null) {
            definiteClausesForKey.remove(definiteClause);
            if ( definiteClausesForKey.isEmpty()) {
                definiteClausesByPredicateIndex.remove(key);
            }
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (Map.Entry<PredicateNameAndArity, List<T>> entry : definiteClausesByPredicateIndex.entrySet()) {
            sb.append("  ").append(entry.getKey()).append(":\n");
            for (T definiteClause : entry.getValue()) {
                sb.append("    ").append(definiteClause).append(".\n");
            }
            sb.append("\n");
        }
        return sb.toString();
    }


}
