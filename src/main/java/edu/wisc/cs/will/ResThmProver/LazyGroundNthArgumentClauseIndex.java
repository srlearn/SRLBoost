package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.Utils.Utils;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

/* This is an index of definite clauses (either Clauses or Literal or a mix of both) with ground Nth arguments in the head.
 *
 * @author twalker
 */
public class LazyGroundNthArgumentClauseIndex {

    private final HornClausebase clausebase;

    private static int maximumIndexSizeDefault = 50;
    private final int maximumIndexSize;

    public static void setMaximumIndexSize(int maximumIndexSizeToUse) {
    	maximumIndexSizeDefault = maximumIndexSizeToUse;
	}

	private int indicesConstructed = 0;
    private int indicesRemoved = 0;
    
    private int indexedArgument;

    private int minimumClauseLengthToIndex;

    /* Index of clauses which might match a constant arg N.
     */
    private Map<PredicateNameAndArity, Map<Term, DefiniteClauseList>> definiteClausesByArgNIndex = new HashMap<>();

    /* Store clauses in which the Nth arg is not ground.
     *
     * This is used to as a starting place for new definiteClause lists indexed by the
     * Nth args.  This is necessary to make sure unseen
     */
    private final Map<PredicateNameAndArity, DefiniteClauseList> definiteClausesWithUngroundNthArg = new HashMap<>();


    public LazyGroundNthArgumentClauseIndex(HornClausebase clausebase, int indexedArgument) {
        this.clausebase = clausebase;
        maximumIndexSize = maximumIndexSizeDefault;
        setIndexedArgument(indexedArgument);
    }

    void indexDefiniteClause(PredicateNameAndArity key, DefiniteClause definiteClause) {
        if (definiteClausesByArgNIndex.containsKey(key)) {
            Literal literal = definiteClause.getDefiniteClauseHead();

            if (literal.numberArgs() >= minimumClauseLengthToIndex) {
                if (definiteClausesByArgNIndex == null) {
                    definiteClausesByArgNIndex = new HashMap<>();
                }

                Map<Term, DefiniteClauseList> mapForKey = definiteClausesByArgNIndex.get(key);
                if (mapForKey == null) {
                    mapForKey = new HashMap<>();
                    definiteClausesByArgNIndex.put(key, mapForKey);

                    Utils.println("% [ LazyGroundNthArgumentClauseIndex ]  Argument " + indexedArgument + ":  Creating index for " + key + ".");
                }

                Term key2 = literal.getArgument(indexedArgument);

                if (key2.isGrounded()) {
                    
                    DefiniteClauseList definiteClauseList = mapForKey.get(key2);

                    if (definiteClauseList == null) {
                        definiteClauseList = new DefiniteClauseList(getDefiniteClauseByNthArgSeedList(key));
                        mapForKey.put(key2, definiteClauseList);
                    }

                    definiteClauseList.add(definiteClause);
                }
                else {
                    
                    for (DefiniteClauseList list : mapForKey.values()) {
                        list.add(definiteClause);
                    }

                    addDefiniteClauseByNthArgSeedSentence(key, definiteClause);
                }
            }
        }
    }

    void removeDefiniteClause(PredicateNameAndArity key, DefiniteClause definiteClause) {
        if (definiteClausesByArgNIndex.containsKey(key)) {
            Literal literal = definiteClause.getDefiniteClauseHead();

            if (literal.numberArgs() >= minimumClauseLengthToIndex) {
                if (definiteClausesByArgNIndex != null) {

                    Map<Term, DefiniteClauseList> mapForKey = definiteClausesByArgNIndex.get(key);
                    if (mapForKey != null) {

                        Term key2 = literal.getArgument(indexedArgument);

                        if (key2.isGrounded()) {

                            DefiniteClauseList definiteClauseList = mapForKey.get(key2);

                            if (definiteClauseList != null) {
                                definiteClauseList.remove(definiteClause);
                            }
                        }
                        else {
                            // If key2 isn't grounded, we have a problem.  We have to add
                            // this definiteClause to every single index entry currently existing.
                            // We also must add it to a list of unground Nth arg clauses
                            // that will later be used as a seed for unseed ground Nth args.
                            for (DefiniteClauseList list : mapForKey.values()) {
                                list.remove(definiteClause);
                            }

                            removeDefiniteClauseByNthArgSeedSentence(key, definiteClause);
                        }
                    }
                }
            }
        }
    }

    private DefiniteClauseList getDefiniteClauseByNthArgSeedList(PredicateNameAndArity key) {

        DefiniteClauseList definiteClausesForKey = definiteClausesWithUngroundNthArg.get(key);
        if (definiteClausesForKey != null) {
            return definiteClausesForKey;
        }
        else {
            return new DefiniteClauseList();
        }
    }

    private void addDefiniteClauseByNthArgSeedSentence(PredicateNameAndArity key, DefiniteClause definiteClause) {
        DefiniteClauseList definiteClausesForKey = definiteClausesWithUngroundNthArg.get(key);

        if (definiteClausesForKey == null) {
            definiteClausesForKey = new DefiniteClauseList();
            definiteClausesWithUngroundNthArg.put(key, definiteClausesForKey);
        }

        definiteClausesForKey.add(definiteClause);
    }

    private void removeDefiniteClauseByNthArgSeedSentence(PredicateNameAndArity key, DefiniteClause definiteClause) {
        DefiniteClauseList definiteClausesForKey = definiteClausesWithUngroundNthArg.get(key);

        if (definiteClausesForKey != null) {
            definiteClausesForKey.remove(definiteClause);

            if (definiteClausesForKey.isEmpty()) {
                definiteClausesWithUngroundNthArg.remove(key);
            }
        }
    }

    /* Return a list of possible matches for <code>literalToLookup</code> based upon the Nth argument.
     *
     * @param literalToLookup Literal to look for possible matches of.
     * @return List of all possible matches to <code>literalToLookup</code>'s nth argument currently in the fact base.
     * This method can return null if the index doesn't contain a complete list of the possible matches.  This happen,
     * for example, if the Nth argument of literalToLookup is unground.
     */
    DefiniteClauseList lookupDefiniteClauses(Literal literalToLookup) {
        if (definiteClausesByArgNIndex != null && literalToLookup != null && literalToLookup.numberArgs() >= minimumClauseLengthToIndex && literalToLookup.getArgument(indexedArgument).isGrounded()) {
            PredicateNameAndArity key = new PredicateNameAndArity(literalToLookup.predicateName, literalToLookup.numberArgs());

            Map<Term, DefiniteClauseList> mapForKey = definiteClausesByArgNIndex.get(key);

            if (mapForKey == null) {
                mapForKey = buildIndex(key);
            }

            if (mapForKey != null) {
                DefiniteClauseList definiteClauseList = mapForKey.get(literalToLookup.getArgument(indexedArgument));

                // If we got this far, than we know that the predicate/arity does have entries.
                // So, if definiteClauseList is null, then there must be no completions and we
                // should return an empty list.
                if (definiteClauseList == null) {
                    return getDefiniteClauseByNthArgSeedList(key);
                }
                else {
                    return definiteClauseList;
                }
            }
        }

        return null;
    }

    @Override
    public String toString() {

        return "LazyGroundNthArgumentClauseIndex[" + indexedArgument + "]:\n" +
                "  maximumIndexSize  : " + maximumIndexSize + ".\n" +
                "  currentIndexSize  : " + definiteClausesByArgNIndex.size() + ".\n" +
                "  indicesConstructed: " + indicesConstructed + ".\n" +
                "  indicesRemoved    : " + indicesRemoved + ".\n";
    }

    private void setIndexedArgument(int indexedArgument) {
        this.indexedArgument = indexedArgument;
        this.minimumClauseLengthToIndex = Math.max(2, indexedArgument + 1);
    }

    private Map<Term, DefiniteClauseList> buildIndex(PredicateNameAndArity predicateNameAndArity) {

        Map<Term, DefiniteClauseList> mapForKey = null;

        if (predicateNameAndArity.getArity() >= minimumClauseLengthToIndex) {
            MapOfDefiniteClauseLists allAssertions = clausebase.getAssertionsMap();

            DefiniteClauseList keyAssertions = allAssertions.getValues(predicateNameAndArity);

            if (keyAssertions != null) {
                
            	 // Changed by JWS.
                Utils.println("% [ LazyGroundNthArgumentClauseIndex ]  Argument " + indexedArgument + ":  Building full index for " + predicateNameAndArity + ".");

                if (definiteClausesByArgNIndex == null) {
                    definiteClausesByArgNIndex = new MyMap();
                }

                mapForKey = new HashMap<>();

                for (DefiniteClause definiteClause : keyAssertions) {
                    Literal literal = definiteClause.getDefiniteClauseHead();

                    Term nthArgument = literal.getArgument(indexedArgument);

                    if (nthArgument.isGrounded()) {

                        DefiniteClauseList definiteClauseList = mapForKey.get(nthArgument);

                        if (definiteClauseList == null) {
                            definiteClauseList = new DefiniteClauseList(getDefiniteClauseByNthArgSeedList(predicateNameAndArity));
                            mapForKey.put(nthArgument, definiteClauseList);
                        }

                        definiteClauseList.add(definiteClause);
                    }
                    else {
                        for (DefiniteClauseList list : mapForKey.values()) {
                            list.add(definiteClause);
                        }

                        addDefiniteClauseByNthArgSeedSentence(predicateNameAndArity, definiteClause);
                    }
                }

                definiteClausesByArgNIndex.put(predicateNameAndArity, mapForKey);
                indicesConstructed++;
            }
        }
        return mapForKey;
    }

    private class MyMap extends LinkedHashMap<PredicateNameAndArity, Map<Term, DefiniteClauseList>> {

        private static final long serialVersionUID = -345307187601453425L;

        protected boolean removeEldestEntry(Map.Entry<PredicateNameAndArity, Map<Term, DefiniteClauseList>> eldest) {
            if (size() > maximumIndexSize) {
                definiteClausesWithUngroundNthArg.remove(eldest.getKey());
                indicesRemoved++;
                return true;
            }
            else {
                return false;
            }
        }
    }
}
