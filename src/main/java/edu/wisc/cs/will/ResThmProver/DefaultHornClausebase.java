package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.BuiltinProcedurallyDefinedPredicateHandler;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.ProcedurallyDefinedPredicateHandler;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.Utils.Utils;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * @author twalker
 */
public class DefaultHornClausebase implements HornClausebase {

    /** Set of all asserted sentences.
     *
     * To maintain prolog semantics, we need to have all assertions in order,
     * independent of whether they are facts (definite clauses with no body, stored
     * as bare Literals) or rules (definite clauses with one or more Literals in
     * the body, stored as DefiniteClauses).
     */
    protected List<DefiniteClause> assertions = new LinkedList<>();

    // Definite clauses with a body...
    private List<Clause> backgroundKnowledge = new LinkedList<>();

    // Definite clauses with no body, stored as bare Literals.
    protected List<Literal> facts = new LinkedList<>();

    private HandleFOPCstrings stringHandler;

    private Map<PredicateNameAndArity, List<AssertRetractListener>> listenerMap = null;

    /** Index for all assertions.
     *
     * This should never be used directly.  Always use the accessor method since
     * indices are build lazily and the index may not yet be built if you use this
     * directly.
     *
     * Guaranteed to be non-null.
     */
    private HornClausebaseIndexer<DefiniteClause> indexerForAllAssertions;

    /** Index for all facts.
     *
     * This should never be used directly.  Always use the accessor method since
     * indices are build lazily and the index may not yet be built if you use this
     * directly.
     *
     * Guaranteed to be non-null.
     */
    private HornClausebaseIndexer<Literal> indexerForFacts;

    /** Index for all background knowledge.
     *
     * This should never be used directly.  Always use the accessor method since
     * indeces are build lazily and the index may not yet be built if you use this
     * directly.
     *
     * Guaranteed to be non-null.
     */
    private HornClausebaseIndexer<Clause> indexerForBackgroundKnowledge;

    private ProcedurallyDefinedPredicateHandler builtinProcedurallyDefinedPredicateHandler;

    private ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandler;

    private int duplicateRuleCount = 0;

    DefaultHornClausebase(HandleFOPCstrings stringHandler, Collection<? extends Sentence> rules, Collection<? extends Sentence> facts) {
        initializeClausebase(stringHandler, rules, facts, null);
    }

    public DefaultHornClausebase(HandleFOPCstrings stringHandler) {
        initializeClausebase(stringHandler, null, null, null);
    }

    DefaultHornClausebase(HandleFOPCstrings stringHandler, Collection<? extends Sentence> rules, Collection<? extends Sentence> facts, ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandler) {
        initializeClausebase(stringHandler, rules, facts, userProcedurallyDefinedPredicateHandler);
    }

    private void initializeClausebase(HandleFOPCstrings stringHandler, Collection<? extends Sentence> rules, Collection<? extends Sentence> facts, ProcedurallyDefinedPredicateHandler userProcHandler) {
        this.stringHandler = stringHandler;
        this.userProcedurallyDefinedPredicateHandler = userProcHandler;

        this.builtinProcedurallyDefinedPredicateHandler = new BuiltinProcedurallyDefinedPredicateHandler(stringHandler);

        addAssertRetractListener(new SpyAssertRetractListener(), stringHandler.getPredicate(stringHandler.standardPredicateNames.spy, 1));

        setupDataStructures();

        if (rules != null) {
            assertBackgroundKnowledge(rules);
        }

        if (facts != null) {
            assertFacts(facts);
        }
    }

    /** Initializes the clausebase.
     *
     */
    private void setupDataStructures() {
        assertions = new ArrayList<>();
        backgroundKnowledge = new ArrayList<>();  // Definite clauses with a body...
        facts = new ArrayList<>(); // Definite clauses with no body, stored as bare Literals.

        // Check to see if the indexers are null, since someone might have tried to use other indexing class
        // if they knew something specific about their data.
        if (indexerForAllAssertions == null) {
            indexerForAllAssertions = new DefaultHornClausebaseIndexer<>(this, DefiniteClause.class);
        }
        if (indexerForFacts == null) {
            indexerForFacts = new DefaultHornClausebaseIndexer<>(this, Literal.class);
        }
        if (indexerForBackgroundKnowledge == null) {
            indexerForBackgroundKnowledge = new DefaultHornClausebaseIndexer<>(this, Clause.class);
        }

        resetIndexes();
    }

    public MapOfDefiniteClauseLists getAssertionsMap() {
        throw new UnsupportedOperationException("Not supported yet.");
    }


    @Override
    public void assertBackgroundKnowledge(DefiniteClause definiteClause) throws IllegalArgumentException {
        if (definiteClause.isDefiniteClause()) {
            Clause clause = definiteClause.getDefiniteClauseAsClause();

            if (checkRule(clause)) {
                assertions.add(clause);
                backgroundKnowledge.add(clause);
                indexBackgroundKnowledge(clause);

                fireAssertion(definiteClause);
            }

        }
        else {
            throw new IllegalArgumentException("Attempted to assert non-definite clause into the HornClauseFactBase: " + definiteClause);
        }
    }

    @Override
    public void assertBackgroundKnowledge(Collection<? extends Sentence> sentences) {
        for (Sentence sentence : sentences) {
            if (sentence instanceof DefiniteClause) {
                DefiniteClause definiteClause = (DefiniteClause) sentence;
                assertBackgroundKnowledge(definiteClause);
            }
            else {
                List<Clause> clauses = sentence.convertToClausalForm();
                if (clauses.size() != 1 || !clauses.get(0).isDefiniteClause()) {
                    throw new IllegalArgumentException("Sentence '" + sentence + "' is not a definite clause.");
                }
                assertBackgroundKnowledge(clauses.get(0));
            }
        }
    }

    @Override
    public void assertFact(Literal literal) {
        if (checkFact(literal)) {
            assertions.add(literal);
            facts.add(literal);
            indexFact(literal);

            fireAssertion(literal);
        }
    }

    @Override
    public void assertFacts(Collection<? extends Sentence> sentences) {
        for (Sentence sentence : sentences) {
            List<Clause> clauses = sentence.convertToClausalForm();
            if (clauses.size() != 1 || !clauses.get(0).isDefiniteClause()) {
                throw new IllegalArgumentException("Sentence '" + sentence + "' is not a definite clause fact.");
            }
            assertFact(clauses.get(0).getDefiniteClauseFactAsLiteral());
        }
    }

    @Override
    public boolean retract(DefiniteClause definiteClause, BindingList bindingList) {

        Literal clauseHead = definiteClause.getDefiniteClauseHead();

        Collection<DefiniteClause> matchAssertions = getAssertions(clauseHead.predicateName, clauseHead.numberArgs());

        boolean result = false;

        if (matchAssertions != null) {

            DefiniteClause clauseToRemove = null;

            for (DefiniteClause aClause : matchAssertions) {
                if (definiteClause.unifyDefiniteClause(aClause, bindingList) != null) {
                    clauseToRemove = aClause;
                    result = true;
                    break;
                }
            }

            if (clauseToRemove != null) {
                removeClause(clauseToRemove);
            }
        }

        return result;
    }

    private void removeClauses(Collection<DefiniteClause> clausesToRemove) {
        if (clausesToRemove != null) {
            for (DefiniteClause definiteClause : clausesToRemove) {
                removeClause(definiteClause);
            }
        }
    }

    public void removeClause(DefiniteClause clauseToRemove) {
        assertions.remove(clauseToRemove);
        backgroundKnowledge.remove(clauseToRemove.getDefiniteClauseAsClause());
        if (clauseToRemove.isDefiniteClauseFact()) {
            facts.remove(clauseToRemove.getDefiniteClauseFactAsLiteral());
        }
        removeFromIndexes(clauseToRemove);

        fireRetraction(clauseToRemove);
    }

    @Override
    public boolean retractAllClausesWithUnifyingBody(DefiniteClause definiteClause) {
        Literal clauseHead = definiteClause.getDefiniteClauseHead();

        Collection<DefiniteClause> matchAssertions = getAssertions(clauseHead.predicateName, clauseHead.numberArgs());

        boolean result = false;

        if (matchAssertions != null) {
            Iterator<DefiniteClause> it = matchAssertions.iterator();

            List<DefiniteClause> clausesToRemove = null;

            while (it.hasNext()) {
                DefiniteClause aClause = it.next();

                if (definiteClause.unifyDefiniteClause(aClause, null) != null) {
                    if (clausesToRemove == null) {
                        clausesToRemove = new ArrayList<DefiniteClause>();
                    }
                    clausesToRemove.add(aClause);
                    result = true;
                }
            }

            if (clausesToRemove != null) {
                removeClauses(clausesToRemove);
            }
        }

        return result;
    }

    @Override
    public boolean retractAllClauseWithHead(DefiniteClause definiteClause) {

        Literal clauseHead = definiteClause.getDefiniteClauseHead();

        Collection<DefiniteClause> matchAssertions = getAssertions(clauseHead.predicateName, clauseHead.numberArgs());

        List<DefiniteClause> clausesToRemove = null;

        boolean result = false;

        if (matchAssertions != null) {
            Iterator<DefiniteClause> it = matchAssertions.iterator();

            while (it.hasNext()) {
                DefiniteClause aClause = it.next();

                if (Unifier.UNIFIER.unify(clauseHead, aClause.getDefiniteClauseHead()) != null) {
                    if (clausesToRemove == null) {
                        clausesToRemove = new ArrayList<DefiniteClause>();
                    }
                    clausesToRemove.add(aClause);
                    result = true;
                }
            }

            if (clausesToRemove != null) {
                removeClauses(clausesToRemove);
            }
        }

        return result;
    }

    @Override
    public boolean retractAllClausesForPredicate(PredicateNameAndArity predicateNameAndArity) {

        Collection<DefiniteClause> matchAssertions = getAssertions(predicateNameAndArity.getPredicateName(), predicateNameAndArity.getArity());

        List<DefiniteClause> clausesToRemove;

        boolean result = false;

        if (matchAssertions != null) {
            clausesToRemove = new ArrayList<>();

            for (DefiniteClause definiteClause : matchAssertions) {
                clausesToRemove.add(definiteClause);
                result = true;
            }

            removeClauses(clausesToRemove);
        }

        return result;
    }

    public void retract(Collection<? extends Sentence> sentences) throws IllegalArgumentException {

        for (Sentence sentence : sentences) {
            if (sentence instanceof DefiniteClause) {
                DefiniteClause definiteClause = (DefiniteClause) sentence;
                retract(definiteClause, null);
            }
            else {
                List<Clause> clauses = sentence.convertToClausalForm();
                if (clauses.size() != 1 || !clauses.get(0).isDefiniteClause()) {
                    throw new IllegalArgumentException("Sentence '" + sentence + "' is not a definite clause.");
                }
                retract(clauses.get(0), null);
            }
        }
    }

    /** Checks to fact to make sure we should add it.
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
        boolean reportFactsWithVariables = false;
        if (reportFactsWithVariables && ground == false) {
            Utils.println("% Fact containing variables: '" + newFact + "'.");
        }

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

            if (action.isWarnEnabled()) {
                // Utils.println("% Duplicate grounded fact #" + Utils.comma(++duplicateFactCount) + ": '" + newFact + (action.isRemoveEnabled() ? "'  It will be deleted." : "'  (It will be kept.  Manually delete if you wish it removed.)"));
            }

            if (action.isRemoveEnabled()) {
                keep = false;
            }
        }

        return keep;
    }

    /** Checks to fact to make sure we should add it.
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

    /** Resets the indexes.
     *
     * The indexes are built lazily, as needed.
     */
    private void resetIndexes() {
        indexerForAllAssertions.resetIndex();
        indexerForFacts.resetIndex();
        indexerForBackgroundKnowledge.resetIndex();
    }

    private void indexBackgroundKnowledge(DefiniteClause definiteClause) {
        if (indexerForAllAssertions.isBuilt()) {
            indexerForAllAssertions.indexAssertion(definiteClause);
        }

        if (indexerForBackgroundKnowledge.isBuilt()) {
            indexerForBackgroundKnowledge.indexAssertion(definiteClause.getDefiniteClauseAsClause());
        }
    }

    private void indexFact(Literal literal) {
        if (indexerForAllAssertions.isBuilt()) {
            indexerForAllAssertions.indexAssertion(literal);
        }

        if (indexerForFacts.isBuilt()) {
            indexerForFacts.indexAssertion(literal);
        }
    }

    private void removeFromIndexes(DefiniteClause definiteClause) {
        if (indexerForAllAssertions.isBuilt()) {
            indexerForAllAssertions.removeAssertion(definiteClause);
        }

        if (indexerForBackgroundKnowledge.isBuilt()) {
            indexerForBackgroundKnowledge.removeAssertion(definiteClause.getDefiniteClauseAsClause());
        }

        if (indexerForFacts.isBuilt() && definiteClause.isDefiniteClauseFact()) {
            indexerForFacts.removeAssertion(definiteClause.getDefiniteClauseFactAsLiteral());
        }
    }

    private void buildAllAssertionsIndex() {
        if (!indexerForAllAssertions.isBuilt()) {
            indexerForAllAssertions.buildIndex(assertions);
        }
    }

    private void buildBackgroundKnowledgeIndex() {
        if (!indexerForBackgroundKnowledge.isBuilt()) {
            indexerForBackgroundKnowledge.buildIndex(backgroundKnowledge);
        }
    }

    private void buildFactsIndex() {
        if (!indexerForFacts.isBuilt()) {
            indexerForFacts.buildIndex(facts);
        }
    }

    @Override
    public List<DefiniteClause> getPossibleMatchingAssertions(Literal clauseHead, BindingList currentBinding) {
        return getIndexerForAllAssertions().getPossibleMatchingAssertions(clauseHead, currentBinding);
    }

    @Override
    public List<Clause> getPossibleMatchingBackgroundKnowledge(Literal clauseHead, BindingList currentBinding) {
        return getIndexerForBackgroundKnowledge().getPossibleMatchingAssertions(clauseHead, currentBinding);
    }

    @Override
    public List<Literal> getPossibleMatchingFacts(Literal clauseHead, BindingList currentBinding) {
        return getIndexerForFacts().getPossibleMatchingAssertions(clauseHead, currentBinding);
    }

    @Override
    public boolean checkForPossibleMatchingAssertions(PredicateName predName, int arity) {
        Collection<DefiniteClause> possibleMatches = getIndexerForAllAssertions().getPossibleMatchingAssertions(predName, arity);
        return (possibleMatches != null && possibleMatches.size() > 0);
    }

    @Override
    public List<DefiniteClause> getAssertions(PredicateName predName, int arity) {
        return getIndexerForAllAssertions().getPossibleMatchingAssertions(predName, arity);
    }

    @Override
    public boolean checkForPossibleMatchingFacts(PredicateName predName, int arity) {
        Collection<Literal> possibleMatches = getIndexerForFacts().getPossibleMatchingAssertions(predName, arity);
        return (possibleMatches != null && possibleMatches.size() > 0);
    }

    @Override
    public boolean checkForPossibleMatchingBackgroundKnowledge(PredicateName predName, int arity) {
        Collection<Clause> possibleMatches = getIndexerForBackgroundKnowledge().getPossibleMatchingAssertions(predName, arity);
        return (possibleMatches != null && possibleMatches.size() > 0);
    }

    @Override
    public List<DefiniteClause> getAssertions() {
        return assertions;
    }

    @Override
    public List<Literal> getFacts() {
        return facts;
    }

    @Override
    public List<Clause> getBackgroundKnowledge() {
        return backgroundKnowledge;
    }

    @Override
    public HandleFOPCstrings getStringHandler() {
        return stringHandler;
    }

    @Override
    public ProcedurallyDefinedPredicateHandler getBuiltinProcedurallyDefinedPredicateHandler() {
        return builtinProcedurallyDefinedPredicateHandler;
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
        return getIndexerForFacts().getPossibleMatchingAssertions(predName, arity) != null && getIndexerForBackgroundKnowledge().getPossibleMatchingAssertions(predName, arity) == null;
    }

    @Override
    public String toString() {
        return "DefaultHornClauseFactbase:\n" +
                "\nAll assertions indexer:\n" +
                indexerForAllAssertions +
                "\nRules indexer:\n" +
                indexerForBackgroundKnowledge +
                "\nFacts indexer:\n" +
                indexerForFacts;
    }

    public String toLongString() {
        StringBuilder sb = new StringBuilder();

        sb.append("DefaultHornClauseFactbase:\n");
        sb.append("\nAssertions:\n");
        for (DefiniteClause definiteClause : assertions) {
            sb.append("  ").append(definiteClause).append(".\n");
        }
        sb.append("\nAll assertions indexer:\n");
        sb.append(getIndexerForAllAssertions());
        sb.append("\nRules indexer:\n");
        sb.append(getIndexerForBackgroundKnowledge());
        sb.append("\nFacts indexer:\n");
        sb.append(getIndexerForFacts());

        return sb.toString();
    }

    @Override
    public boolean recorded(DefiniteClause definiteClause) {
        Clause definiteClauseAsClause = definiteClause.getDefiniteClauseAsClause();
        Literal clauseHead = definiteClause.getDefiniteClauseHead();
        Collection<DefiniteClause> possibleMatchingClauses = getIndexerForAllAssertions().getPossibleMatchingAssertions(clauseHead, null);
        if (possibleMatchingClauses != null) {
            BindingList bl = new BindingList();
            for (DefiniteClause anotherClause : possibleMatchingClauses) {
                // Variants will check for duplication without performing unification.
                bl.theta.clear();
                if (definiteClauseAsClause.variants(anotherClause.getDefiniteClauseAsClause(), bl) != null) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean isFactAsserted(Literal literal) {
        Collection<Literal> possibleMatchingFacts = getIndexerForFacts().getPossibleMatchingAssertions(literal, null);
        if (possibleMatchingFacts != null) {
            BindingList bl = new BindingList();
            for (Literal anotherFact : possibleMatchingFacts) {
                // Variants will check for duplication without performing unification.
                bl.theta.clear();
                if (literal.variants(anotherFact, bl) != null) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Returns the index for all assertions.
     *
     * If the index is not built yet, this method will build it.
     *
     * @return the indexerForAllAssertions
     */
    private HornClausebaseIndexer<DefiniteClause> getIndexerForAllAssertions() {
        buildAllAssertionsIndex();
        return indexerForAllAssertions;
    }

    /** Returns the index for all facts.
     *
     * If the index is not built yet, this method will build it.
     *
     * @return the indexerForFacts
     */
    private HornClausebaseIndexer<Literal> getIndexerForFacts() {
        buildFactsIndex();
        return indexerForFacts;
    }

    /** Returns the index for all background knowledge.
     *
     * If the index is not built yet, this method will build it.
     *
     * @return the indexerForBackgroundKnowledge
     */
    private HornClausebaseIndexer<Clause> getIndexerForBackgroundKnowledge() {
        buildBackgroundKnowledgeIndex();
        return indexerForBackgroundKnowledge;
    }

    public void addAssertRetractListener(AssertRetractListener assertRetractListener, PredicateNameAndArity predicate) {
        if (listenerMap == null) {
            listenerMap = new HashMap<>();
        }

        List<AssertRetractListener> list = listenerMap.computeIfAbsent(predicate, k -> new ArrayList<>());

        if (!list.contains(assertRetractListener)) {
            list.add(assertRetractListener);
        }
    }

    public void removeAssertRetractListener(AssertRetractListener assertRetractListener, PredicateNameAndArity predicate) {
        if (listenerMap != null) {
            List<AssertRetractListener> list = listenerMap.get(predicate);
            if (list != null) {
                list.remove(assertRetractListener);

                if (list.isEmpty()) {
                    listenerMap.remove(predicate);

                    if (listenerMap.isEmpty()) {
                        listenerMap = null;
                    }
                }
            }
        }
    }

    private void fireAssertion(DefiniteClause clause) {
        if (listenerMap != null) {
            PredicateNameAndArity pnaa = new PredicateNameAndArity(clause);

            List<AssertRetractListener> list = listenerMap.get(pnaa);

            if (list != null) {
                for (AssertRetractListener assertRetractListener : list) {
                    assertRetractListener.clauseAsserted(this, clause);
                }
            }
        }
    }

    private void fireRetraction(DefiniteClause clause) {
        if (listenerMap != null) {
            PredicateNameAndArity pnaa = new PredicateNameAndArity(clause);

            List<AssertRetractListener> list = listenerMap.get(pnaa);

            if (list != null) {
                for (AssertRetractListener assertRetractListener : list) {
                    assertRetractListener.clauseRetracted(this, clause);
                }
            }
        }
    }

    public List<DefiniteClause> getAssertions(PredicateNameAndArity predicateNameAndArity) {
        return getAssertions(predicateNameAndArity.getPredicateName(), predicateNameAndArity.getArity());
    }

    public boolean isDefined(PredicateNameAndArity pnaa) {

        if (getStringHandler().standardPredicateNames.buildinPredicates.contains(pnaa.getPredicateName())) {
            return true;
        }

        if (getUserProcedurallyDefinedPredicateHandler() != null && getUserProcedurallyDefinedPredicateHandler().canHandle(pnaa.getPredicateName(), pnaa.getArity())) {
            return true;
        }
        if (getBuiltinProcedurallyDefinedPredicateHandler() != null && getBuiltinProcedurallyDefinedPredicateHandler().canHandle(pnaa.getPredicateName(), pnaa.getArity())) {
            return true;
        }

        return checkForPossibleMatchingAssertions(pnaa.getPredicateName(), pnaa.getArity());
    }

    public class SpyAssertRetractListener implements AssertRetractListener {

        public void clauseAsserted(HornClausebase context, DefiniteClause clause) {
            if (clause.isDefiniteClauseFact()) {
                Literal fact = clause.getDefiniteClauseFactAsLiteral();
                if (fact.predicateName == context.getStringHandler().standardPredicateNames.spy && fact.getArity() == 1) {
                    try {
                        Term term = fact.getArgument(0);
                        Function function = (Function) term;
                        String predName = ((StringConstant) function.getArgument(0)).getBareName();
                        int predArity = ((NumericConstant) function.getArgument(1)).value.intValue();

                        getStringHandler().spyEntries.addLiteral(predName, predArity);
                    } catch (Exception e) {
                        Utils.warning("Encountered spy/1 statement.  Expected argument 1 to be function of form pred/arity.  Found: " + fact + ".");
                    }
                }
            }
        }

        public void clauseRetracted(HornClausebase context, DefiniteClause clause) {
            throw new UnsupportedOperationException("Not supported yet.");
        }
    }
}
