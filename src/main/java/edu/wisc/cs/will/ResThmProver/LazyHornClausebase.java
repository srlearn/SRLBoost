package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 *
 * @author twalker
 */
public class LazyHornClausebase implements HornClausebase {

    /* Set of all asserted sentences.
     *
     * To maintain prolog semantics, we need to have all assertions in order,
     * independent of whether they are facts (definite clauses with no body, stored
     * as bare Literals) or rules (definite clauses with one or more Literals in
     * the body, stored as DefiniteClauses).
     */
    private MapOfDefiniteClauseLists assertions = null;

    private HandleFOPCstrings stringHandler;

    // TODO(@hayesall): Drop the `LazyHornClausebase.DEBUG`
    static final int DEBUG = 0;

    /* Index for all assertions.
     *
     * This should never be used directly.  Always use the accessor method since
     * indices are build lazily and the index may not yet be built if you use this
     * directly.
     *
     * Guaranteed to be non-null.
     */
    private LazyHornClausebaseIndexer indexerForAllAssertions;

    private ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandler;

    private int duplicateRuleCount = 0;

    public LazyHornClausebase(HandleFOPCstrings stringHandler) {
        initializeClausebase(stringHandler);
    }

    private void initializeClausebase(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;
        this.userProcedurallyDefinedPredicateHandler = null;
        setupDataStructures();
    }

    /* Initializes the clausebase. */
    private void setupDataStructures() {
        assertions = new MapOfDefiniteClauseLists();
        // Check to see if the indexers are null, since someone might have tried to use other indexing class
        // if they knew something specific about their data.
        if (indexerForAllAssertions == null) {
            indexerForAllAssertions = new LazyHornClausebaseIndexer(this);
        }
        resetIndexes();
    }

    @Override
    public void assertBackgroundKnowledge(DefiniteClause definiteClause) throws IllegalArgumentException {
        if (definiteClause.isDefiniteClause()) {
            Clause clause = definiteClause.getDefiniteClauseAsClause();
            if (checkRule(clause)) {
                assertions.add(clause.getDefiniteClauseHead().getPredicateNameAndArity(), definiteClause);
                indexerForAllAssertions.indexAssertion(clause);
            }
        }
        else {
            throw new IllegalArgumentException("Attempted to assert non-definite clause into the HornClauseFactBase: " + definiteClause);
        }
    }

    @Override
    public void assertFact(Literal literal) {
        if (checkFact(literal)) {
            assertions.add(literal.getPredicateNameAndArity(), literal);
            indexerForAllAssertions.indexAssertion(literal);
        }
    }

    private void removeClauses(Collection<DefiniteClause> clausesToRemove) {
        if (clausesToRemove != null) {
            for (DefiniteClause definiteClause : clausesToRemove) {
                removeClause(definiteClause);
            }
        }
    }

    private void removeClause(DefiniteClause clauseToRemove) {
        PredicateNameAndArity pnaa = clauseToRemove.getDefiniteClauseHead().getPredicateNameAndArity();
        assertions.removeValue(pnaa, clauseToRemove);
        removeFromIndexes(clauseToRemove);
    }

    @Override
    public void retractAllClausesWithUnifyingBody(DefiniteClause definiteClause) {
        Literal clauseHead = definiteClause.getDefiniteClauseHead();
        Collection<DefiniteClause> matchAssertions = getAssertions(clauseHead.predicateName, clauseHead.numberArgs());
        if (matchAssertions != null) {
            Iterator<DefiniteClause> it = matchAssertions.iterator();
            DefiniteClauseList clausesToRemove = null;
            while (it.hasNext()) {
                DefiniteClause aClause = it.next();
                if (definiteClause.unifyDefiniteClause(aClause, null) != null) {
                    if (clausesToRemove == null) {
                        clausesToRemove = new DefiniteClauseList();
                    }
                    clausesToRemove.add(aClause);
                }
            }
            if (clausesToRemove != null) {
                removeClauses(clausesToRemove);
            }
        }
    }

    /* Checks to fact to make sure we should add it.
     *
     * Depending on the settings stringHandler.variantFactHandling settings, various checks will be performed.
     *
     * @param newFact Clause to check.
     * @return True if the fact is okay to add to the fact base.  False otherwise.
     */
    private boolean checkFact(Literal newFact) {
        boolean keep = true;
        boolean ground = newFact.isGrounded();
        // Report facts with variables in them.
        VariantClauseAction action = getStringHandler().variantFactHandling;
        boolean duplicate = false;
        if (action.isCheckRequired()) {
            if (ground) {
                duplicate = isFactAsserted(newFact);
            }
            else {
                Iterable<Literal> matching = getPossibleMatchingFacts(newFact, null);
                if (matching != null) {
                    for (Literal literal : matching) {
                        if (literal.isVariant(newFact)) {
                            duplicate = true;
                            break;
                        }
                    }
                }
            }
        }

        if (duplicate) {
            if (action.isRemoveEnabled()) {
                keep = false;
            }
        }
        return keep;
    }

    /* Checks to fact to make sure we should add it.
     *
     * Depending on the settings stringHandler.variantFactHandling settings, various checks will be performed.
     *
     * @param newRule Literal to check.
     * @return True if the fact is okay to add to the fact base.  False otherwise.
     */
    private boolean checkRule(Clause newRule) {
        boolean keep = true;
        VariantClauseAction action = getStringHandler().variantRuleHandling;
        boolean duplicate = false;
        if (action.isCheckRequired()) {
            Iterable<Clause> matching = getPossibleMatchingBackgroundKnowledge(newRule.getDefiniteClauseHead(), null);
            if (matching != null) {
                for (Clause clause : matching) {
                    if (clause.isVariant(newRule)) {
                        duplicate = true;
                        break;
                    }
                }
            }
        }
        if (duplicate) {
            duplicateRuleCount++;
            if (action.isWarnEnabled()) {
                Utils.println("% Duplicate rule #" + Utils.comma(++duplicateRuleCount) + ": '" + newRule + (action.isRemoveEnabled() ? "'  It will be deleted." : "'  (It will be kept.  Manually delete if you wish it removed.)"));
            }
            if (action.isRemoveEnabled()) {
                keep = false;
            }
        }
        return keep;
    }

    /* Resets the indexes.
     *
     * The indexes are built lazily, as needed.
     */
    private void resetIndexes() {
        indexerForAllAssertions.resetIndex();
    }

    private void removeFromIndexes(DefiniteClause definiteClause) {
        indexerForAllAssertions.removeAssertion(definiteClause);
    }

    @Override
    public DefiniteClauseList getPossibleMatchingAssertions(Literal clauseHead, BindingList currentBinding) {
        return getIndexerForAllAssertions().getPossibleMatchingAssertions(clauseHead, currentBinding);
    }

    @Override
    public Iterable<Clause> getPossibleMatchingBackgroundKnowledge(Literal clauseHead, BindingList currentBinding) {
        DefiniteClauseList list = getIndexerForAllAssertions().getPossibleMatchingAssertions(clauseHead, currentBinding);
        return list == null ? null : list.getClauseIterable();
    }

    @Override
    public Iterable<Literal> getPossibleMatchingFacts(Literal clauseHead, BindingList currentBinding) {
        DefiniteClauseList list = getIndexerForAllAssertions().getPossibleMatchingAssertions(clauseHead, currentBinding);
        return list == null ? null : list.getFactIterable();
    }

    public MapOfDefiniteClauseLists getAssertionsMap() {
        return assertions;
    }

    private DefiniteClauseList getAssertions(PredicateName predName, int arity) {
        return getIndexerForAllAssertions().getPossibleMatchingAssertions(predName, arity);
    }

    @Override
    public boolean checkForPossibleMatchingFacts(PredicateName predName, int arity) {
        DefiniteClauseList possibleMatches = getIndexerForAllAssertions().getPossibleMatchingAssertions(predName, arity);
        return (possibleMatches != null && possibleMatches.size() > 0);
    }

    @Override
    public boolean checkForPossibleMatchingBackgroundKnowledge(PredicateName predName, int arity) {
        return assertions.containsKey( new PredicateNameAndArity(predName, arity));
    }

    @Override
    public Iterable<Clause> getBackgroundKnowledge() {
        return new DefiniteClauseToClauseIterable(assertions);
    }

    @Override
    public HandleFOPCstrings getStringHandler() {
        return stringHandler;
    }

    @Override
    public ProcedurallyDefinedPredicateHandler getUserProcedurallyDefinedPredicateHandler() {
        return userProcedurallyDefinedPredicateHandler;
    }

    @Override
    public void setUserProcedurallyDefinedPredicateHandler(ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandler) {
        this.userProcedurallyDefinedPredicateHandler = userProcedurallyDefinedPredicateHandler;
    }

    @Override
    public boolean isOnlyInFacts(PredicateName predName, int arity) {

        DefiniteClauseList list = indexerForAllAssertions.getPossibleMatchingAssertions(predName, arity);

        return list != null && list.containsOnlyFacts();
    }

    @Override
    public String toString() {
        return "LazyHornClauseFactbase:\n" +
                "\nAll assertions indexer:\n" +
                indexerForAllAssertions;
    }

    private boolean isFactAsserted(Literal literal) {
        Iterable<Literal> possibleMatchingFacts = getPossibleMatchingFacts(literal, null);
        if (possibleMatchingFacts != null) {
            for (Literal anotherFact : possibleMatchingFacts) {
                BindingList bl = new BindingList();
                if (literal.variants(anotherFact, bl) != null) {
                    return true;
                }
            }
        }
        return false;
    }

    /* Returns the index for all assertions.
     *
     * If the index is not built yet, this method will build it.
     *
     * @return the indexerForAllAssertions
     */
    private LazyHornClausebaseIndexer getIndexerForAllAssertions() {
        return indexerForAllAssertions;
    }

}
