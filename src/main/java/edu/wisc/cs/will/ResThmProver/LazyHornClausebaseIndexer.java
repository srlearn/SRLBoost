package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.*;

/*
 * @author twalker
 */
class LazyHornClausebaseIndexer {

  private final HornClausebase clausebase;

    private final int indexWidth;

    private LazyGroundNthArgumentClauseIndex[] singleGroundArgIndexArray = null;

    private LazyGroundClauseIndex groundClauseIndex = null;

    private PredicateIndex<DefiniteClause> predicateIndex = null;

    private long[] singleGroundArgIndexLookupCount = null;

    private long groundClauseLookupCount = 0;

    private long predicateLookupCount = 0;

    private long[] singleGroundArgIndexHitCount = null;

    private long groundClauseHitCount = 0;

    private long predicateHitCount = 0;

    LazyHornClausebaseIndexer(HornClausebase clausebase) {
        this(clausebase, 2);
    }

    private LazyHornClausebaseIndexer(HornClausebase clausebase, int indexWidth) {
        this.clausebase = clausebase;
        this.indexWidth = indexWidth;
        resetIndex();
    }

    final void resetIndex() {
    	if (singleGroundArgIndexArray != null) { // Added by JWS to get a glimpse of how often this is happening.
    		System.out.println("\nResetting the LazyGroundNthArgumentClauseIndex.");
    	}
        singleGroundArgIndexArray = new LazyGroundNthArgumentClauseIndex[indexWidth];

        for (int indexedArgument = 0; indexedArgument < indexWidth; indexedArgument++) {
                singleGroundArgIndexArray[indexedArgument] = new LazyGroundNthArgumentClauseIndex(clausebase, indexedArgument);
        }
        
        predicateIndex = new PredicateIndex<>();
        groundClauseIndex = new LazyGroundClauseIndex(clausebase);

        singleGroundArgIndexLookupCount = new long[indexWidth];
        groundClauseLookupCount = 0;
        predicateLookupCount = 0;

        singleGroundArgIndexHitCount = new long[indexWidth];
        groundClauseHitCount = 0;
        predicateHitCount = 0;
    }

    void indexAssertion(DefiniteClause definiteClause) {

        if (definiteClause != null && definiteClause.isDefiniteClause()) {

            PredicateNameAndArity key = new PredicateNameAndArity(definiteClause);

            // Even though we are lazy, we still need to notify the subindices that
            // new clauses came along, just in case they have indexed that predicate
            // already.

            indexDefiniteClauseByAllArgs(key, definiteClause);
            for (int i = 0; i < indexWidth && i < key.getArity(); i++) {
                indexDefiniteClauseByNthArg(i, key, definiteClause);
            }
            
        }
    }

    void removeAssertion(DefiniteClause definiteClause) {

        PredicateNameAndArity key = new PredicateNameAndArity(definiteClause);

        removeDefiniteClauseByPredicate(key, definiteClause);
        removeDefiniteClauseByAllArgs(key, definiteClause);
        for (int i = 0; i < indexWidth && i < key.getArity(); i++) {
            removeDefiniteClauseByNthArg(i, key, definiteClause);
        }
    }

    DefiniteClauseList getPossibleMatchingAssertions(Literal clauseHead, BindingList currentBindings) {
        if (clauseHead != null) {
            DefiniteClauseList set;

            PredicateNameAndArity pnaa = clauseHead.getPredicateNameAndArity();

            if (!clausebase.getAssertionsMap().containsKey(pnaa)) {
                // Fast fail for predicates that don't exist in the clausebase.
                // We might want to move this into the clausebase itself...
                return null;
            }

            // Short term, we are just going to apply the binding list to the clause head.
            Literal boundClauseHead = (clauseHead.isGrounded() || currentBindings == null) ? clauseHead : clauseHead.applyTheta(currentBindings.theta);

            set = lookupDefiniteClauseByAllArgs(boundClauseHead);
            if (set != null) {
                groundClauseHitCount++;
            }
            else {
                DefiniteClauseList aSet;

                int arity = clauseHead.numberArgs();

                if (arity >= 2) {
                    for (int i = 0; i < indexWidth && i < arity; i++) {
                        aSet = lookupDefiniteClausesByNthArgs(i, boundClauseHead);

                        if (aSet != null) {
                            singleGroundArgIndexHitCount[i]++;
                            if (set == null || aSet.size() < set.size()) {
                                set = aSet;
                            }
                        }
                    }
                }

                if (set == null) {
                    set = lookupDefiniteClausesByPredicate(pnaa);
                    if (set != null && !set.isEmpty()) {
                        predicateHitCount++;
                    }
                }
            }
            return set;
        }

        return null;
    }

    DefiniteClauseList getPossibleMatchingAssertions(PredicateName predicateName, int arity) {
        PredicateNameAndArity pnaa = new PredicateNameAndArity(predicateName, arity);

        return lookupDefiniteClausesByPredicate(pnaa);
    }

    private void indexDefiniteClauseByNthArg(int indexedArgument, PredicateNameAndArity key, DefiniteClause sentence) {
        if (indexedArgument < indexWidth) {
            singleGroundArgIndexArray[indexedArgument].indexDefiniteClause(key, sentence);
        }
    }

    private void removeDefiniteClauseByNthArg(int indexedArgument, PredicateNameAndArity key, DefiniteClause sentence) {
        if (indexedArgument < indexWidth) {
            if (singleGroundArgIndexArray[indexedArgument] != null) {
                singleGroundArgIndexArray[indexedArgument].removeDefiniteClause(key, sentence);
            }
        }
    }

    private DefiniteClauseList lookupDefiniteClausesByNthArgs(int indexedArgument, Literal literal) {
        if (singleGroundArgIndexArray[indexedArgument] != null) {
            singleGroundArgIndexLookupCount[indexedArgument]++;
            return singleGroundArgIndexArray[indexedArgument].lookupDefiniteClauses(literal);
        }
        return null;
    }

    private void indexDefiniteClauseByAllArgs(PredicateNameAndArity key, DefiniteClause sentence) {
        groundClauseIndex.indexDefiniteClause(key, sentence);
    }

    private void removeDefiniteClauseByAllArgs(PredicateNameAndArity key, DefiniteClause sentence) {
        if (groundClauseIndex != null) {
            groundClauseIndex.removeDefiniteClause(key, sentence);
        }
    }

    private DefiniteClauseList lookupDefiniteClauseByAllArgs(Literal literalToLookup) {
        if (groundClauseIndex != null && literalToLookup != null && literalToLookup.isGrounded()) {
            groundClauseLookupCount++;
            return groundClauseIndex.lookupDefiniteClauses(literalToLookup);
        }
        return null;
    }

    private void removeDefiniteClauseByPredicate(PredicateNameAndArity key, DefiniteClause sentence) {
        if (predicateIndex != null) {
            predicateIndex.removeDefiniteClause(key, sentence);
        }
    }

    private DefiniteClauseList lookupDefiniteClausesByPredicate(PredicateNameAndArity pnaa) {
        if (predicateIndex != null) {
            predicateLookupCount++;
            return clausebase.getAssertionsMap().getValues(pnaa);
        }
        return null;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("% DefaultHornClauseFactbaseIndexer:\n");
        for (int i = 0; i < indexWidth; i++) {
            sb.append(String.format("%%   Ground Argument %d  : Lookups = %d, Hits = %d, Efficiency = %.2f%%.\n", i, singleGroundArgIndexLookupCount[i], singleGroundArgIndexHitCount[i], 100.0 * singleGroundArgIndexHitCount[i] / singleGroundArgIndexLookupCount[i]));
        }

        sb.append(String.format("%%   All ground index    : Lookups = %d, Hits = %d, Efficiency = %.2f%%.\n", groundClauseLookupCount, groundClauseHitCount, 100.0 * groundClauseHitCount / groundClauseLookupCount));
        sb.append(String.format("%%   Predicates Index    : Lookups = %d, Hits = %d, Efficiency = %.2f%%.\n", predicateLookupCount, predicateHitCount, 100.0 * predicateHitCount / predicateLookupCount));

        if ( groundClauseIndex != null ) sb.append(groundClauseIndex.toString());
        for (LazyGroundNthArgumentClauseIndex lazyGroundNthArgumentClauseIndex : singleGroundArgIndexArray) {
            if (lazyGroundNthArgumentClauseIndex != null) sb.append(lazyGroundNthArgumentClauseIndex);
        }

        return sb.toString();
    }

}
