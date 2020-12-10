package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.Utils.MapOfLists;

import java.util.List;

/*
 * @author twalker
 */
public class MapOfDefiniteClauseLists extends MapOfLists<PredicateNameAndArity, DefiniteClause> {

    @Override
    protected List<DefiniteClause> createValueList() {
        return new DefiniteClauseList();
    }

    @Override
    public DefiniteClauseList getValues(PredicateNameAndArity key) {
        return (DefiniteClauseList) super.getValues(key);
    }

}
