package edu.wisc.cs.will.ResThmProver;

import java.util.List;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.Utils.MapOfLists;

/*
 * @author twalker
 */
public class MapOfDefiniteClauseLists extends MapOfLists<PredicateNameAndArity, DefiniteClause> implements Iterable<DefiniteClause> {

    @Override
    protected List<DefiniteClause> createValueList() {
        return new DefiniteClauseList();
    }

    @Override
    public DefiniteClauseList getValues(PredicateNameAndArity key) {
        return (DefiniteClauseList) super.getValues(key);
    }

}
