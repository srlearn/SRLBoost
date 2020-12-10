package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;

import java.util.ArrayList;
import java.util.List;

/*
 * @author twalker
 */
public class DefiniteClauseList extends ArrayList<DefiniteClause> {

    private static final long serialVersionUID = -1871184376324148010L;
    private boolean containsOnlyFacts = true;

    DefiniteClauseList() {
        super(1);
    }

    DefiniteClauseList(List<DefiniteClause> list) {
        super(list);
    }

    public boolean remove(Object o) {
        boolean result = super.remove(o);

        if (result && !containsOnlyFacts && ((DefiniteClause) o).isDefiniteClauseRule()) {
            updateContainsOnlyFacts();
        }

        return result;
    }

    public boolean add(DefiniteClause e) {

        if (containsOnlyFacts && e.isDefiniteClauseRule()) {
            containsOnlyFacts = false;
        }

        return super.add(e);
    }

    private void updateContainsOnlyFacts() {
        boolean result = true;
        for (DefiniteClause definiteClause : this) {
            if (definiteClause.isDefiniteClauseRule()) {
                result = false;
                break;
            }
        }
        containsOnlyFacts = result;
    }

    boolean containsOnlyFacts() {
        return containsOnlyFacts;
    }

    Iterable<Literal> getFactIterable() {
        return new DefiniteClauseToLiteralIterable(this);
    }

    Iterable<Clause> getClauseIterable() {
        return new DefiniteClauseToClauseIterable(this);
    }
}
