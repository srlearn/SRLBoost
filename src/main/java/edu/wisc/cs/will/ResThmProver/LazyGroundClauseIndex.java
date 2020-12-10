package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.Utils.Utils;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

// TODO(@hayesall): Lots of duplicated code with `LazyGroundNthArgumentClauseIndex`

/* This is an index of definite clauses (either Clauses or Literal or a mix of both) with ground heads.
 *
 * @author twalker
 */
public class LazyGroundClauseIndex {

    private final HornClausebase clausebase;

    private static int maximumIndexSizeDefault = 150;
    private final int maximumIndexSize        = maximumIndexSizeDefault;
	public  static void setMaximumIndexSize(int maximumIndexSizeToUse) {
		maximumIndexSizeDefault = maximumIndexSizeToUse;
	}

	private int indicesConstructed = 0;

    private int indicesRemoved = 0;

    private final Map<PredicateNameAndArity, Map<List<Term>, DefiniteClauseList>> definiteClausesAllArgsIndex = new LRUMap();

    /* Store clauses in which one or more of the args is not ground.
     *
     * This is used to as a starting place for new definiteClause lists indexed by the
     * all args.  This is necessary to make sure unseen term combinations
     * start with the unground clauses in their index.
     */
    private final Map<PredicateNameAndArity, DefiniteClauseList> definiteClausesWithUngroundArgs = new HashMap<>();

    public LazyGroundClauseIndex(HornClausebase clausebase) {
        this.clausebase = clausebase;
    }

    void indexDefiniteClause(PredicateNameAndArity key, DefiniteClause definiteClause) {

        if (definiteClausesAllArgsIndex.containsKey(key)) {
            Literal headLiteral = definiteClause.getDefiniteClauseHead();

            Map<List<Term>, DefiniteClauseList> mapForKey = definiteClausesAllArgsIndex.get(key);
            if (mapForKey == null) {
                mapForKey = new HashMap<>();
                definiteClausesAllArgsIndex.put(key, mapForKey);

                Utils.println("% [ LazyGroundClauseIndex ]  Creating ground clause index for " + key + ".");
            }

            if (headLiteral.isGrounded()) {

                DefiniteClauseList definiteClauseList = mapForKey.get(headLiteral.getArguments());

                if (definiteClauseList == null) {
                    definiteClauseList = new DefiniteClauseList(getDefiniteClausesSeedList(key));
                    mapForKey.put(headLiteral.getArguments(), definiteClauseList);
                }

                definiteClauseList.add(definiteClause);
            }
            else {

                // This is an non-ground literal, so we just need to throw into all of the appropriate
                // places was well as the seed list.
                for (DefiniteClauseList list : mapForKey.values()) {
                    list.add(definiteClause);
                }

                addDefiniteClausesSeedDefiniteClause(key, definiteClause);
            }
        }

    }

    void removeDefiniteClause(PredicateNameAndArity key, DefiniteClause definiteClause) {

        if (definiteClausesAllArgsIndex.containsKey(key)) {
            Literal headLiteral = definiteClause.getDefiniteClauseHead();

            Map<List<Term>, DefiniteClauseList> mapForKey = definiteClausesAllArgsIndex.get(key);
            if (mapForKey != null) {

                if (headLiteral.isGrounded()) {
                    DefiniteClauseList definiteClauseList = mapForKey.get(headLiteral.getArguments());

                    if (definiteClauseList != null) {
                        definiteClauseList.remove(definiteClause);
                    }

                    assert definiteClauseList != null;
                    if (definiteClauseList.isEmpty()) {
                        mapForKey.remove(headLiteral.getArguments());
                    }
                }
                else {
                    // This is an non-ground literal, so we just need to throw into all of the appropriate
                    // places was well as the seed list.
                    for (DefiniteClauseList list : mapForKey.values()) {
                        list.remove(definiteClause);
                    }

                    removeDefiniteClausesSeedDefiniteClause(key, definiteClause);
                }
            }
        }
    }

    DefiniteClauseList lookupDefiniteClauses(Literal lookupLiteral) {
        if (lookupLiteral != null && lookupLiteral.isGrounded()) {
            PredicateNameAndArity key = lookupLiteral.getPredicateNameAndArity();
            Map<List<Term>, DefiniteClauseList> mapForKey = definiteClausesAllArgsIndex.get(key);


            if (mapForKey == null) {
                // We haven't had DefiniteClause build the index for this guy yet...we should probably do that.
                mapForKey = buildIndexForKey(key);
            }

            DefiniteClauseList definiteClauseList = mapForKey.get(lookupLiteral.getArguments());

            // If we got this far, than we know that the predicate/arity does have entries.
            // So, if definiteClauseList is null, then there must be no completions and we
            // should return an empty list.
            if (definiteClauseList == null) {
                return getDefiniteClausesSeedList(key);
            }
            else {
                return definiteClauseList;
            }
        }

        return null;
    }

    private DefiniteClauseList getDefiniteClausesSeedList(PredicateNameAndArity key) {

        DefiniteClauseList definiteClausesForKey = definiteClausesWithUngroundArgs.get(key);
        if (definiteClausesForKey != null) {
            return definiteClausesForKey;
        }
        else {
            return new DefiniteClauseList();
        }
    }

    private void addDefiniteClausesSeedDefiniteClause(PredicateNameAndArity key, DefiniteClause definiteClause) {
        DefiniteClauseList definiteClausesForKey = definiteClausesWithUngroundArgs.get(key);

        if (definiteClausesForKey == null) {
            definiteClausesForKey = new DefiniteClauseList();
            definiteClausesWithUngroundArgs.put(key, definiteClausesForKey);
        }

        definiteClausesForKey.add(definiteClause);
    }

    private void removeDefiniteClausesSeedDefiniteClause(PredicateNameAndArity key, DefiniteClause definiteClause) {
        DefiniteClauseList definiteClausesForKey = definiteClausesWithUngroundArgs.get(key);

        if (definiteClausesForKey != null) {
            definiteClausesForKey.remove(definiteClause);

            if (definiteClausesForKey.isEmpty()) {
                definiteClausesWithUngroundArgs.remove(key);
            }
        }
    }

    @Override
    public String toString() {
        return "LazyGroundClauseIndex:\n" +
                "  maximumIndexSize  : " + maximumIndexSize + ".\n" +
                "  currentIndexSize  : " + definiteClausesAllArgsIndex.size() + ".\n" +
                "  indicesConstructed: " + indicesConstructed + ".\n" +
                "  indicesRemoved    : " + indicesRemoved + ".\n";
    }

    private Map<List<Term>, DefiniteClauseList> buildIndexForKey(PredicateNameAndArity key) {
        if (definiteClausesAllArgsIndex.containsKey(key)) {
            throw new IllegalStateException("LazyGroundClauseIndex.buildIndexForKey(): Predicate " + key + " already indexed.");
        }

        indicesConstructed++;


        MapOfDefiniteClauseLists assertions = clausebase.getAssertionsMap();
        DefiniteClauseList clauses = assertions.getValues(key);

        Map<List<Term>, DefiniteClauseList> mapForKey;

        Utils.println("% [ LazyGroundClauseIndex ]  Building full index for " + key + " with " + Utils.comma(clauses) + " assertions.");

        mapForKey = new HashMap<>((int) Math.max(16, clauses.size() / 0.75 + 10));

        for (DefiniteClause definiteClause : clauses) {
            Literal headLiteral = definiteClause.getDefiniteClauseHead();

            if (headLiteral.isGrounded()) {
                DefiniteClauseList definiteClauseList = mapForKey.get(headLiteral.getArguments());

                if (definiteClauseList == null) {
                    definiteClauseList = new DefiniteClauseList(getDefiniteClausesSeedList(key));
                    mapForKey.put(headLiteral.getArguments(), definiteClauseList);
                }

                definiteClauseList.add(definiteClause);
            }
            else {
                // This is an non-ground literal, so we just need to throw into all of the appropriate
                // places was well as the seed list.
                for (DefiniteClauseList list : mapForKey.values()) {
                    list.add(definiteClause);
                }

                addDefiniteClausesSeedDefiniteClause(key, definiteClause);
            }
        }

        definiteClausesAllArgsIndex.put(key, mapForKey);

        return mapForKey;
    }

    private class LRUMap extends LinkedHashMap<PredicateNameAndArity, Map<List<Term>, DefiniteClauseList>> {

        private static final long serialVersionUID = -2151797847494179763L;

        protected boolean removeEldestEntry(
                Map.Entry<PredicateNameAndArity, Map<List<Term>, DefiniteClauseList>> eldest) {
        	
            if (size() > maximumIndexSize) {          	

                definiteClausesWithUngroundArgs.remove(eldest.getKey());
                indicesRemoved++;
                return true;
            }
            else {
                return false;
            }
        }
    }
}
