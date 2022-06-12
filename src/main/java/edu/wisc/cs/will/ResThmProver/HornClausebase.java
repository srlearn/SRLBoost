package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.*;

import java.util.List;

/*
 * @author twalker
 */
public interface HornClausebase {

    /* Returns the String handler for this fact base.
     * 
     * @return String handler for this fact base.
     */
    HandleFOPCstrings getStringHandler();

    MapOfDefiniteClauseLists getAssertionsMap();

    /* Returns the set of all asserted background knowledge.
     * 
     * The returned collection should be considered immutable.  Changing the
     * collection directly would be bad.
     *
     * @return Set of all asserted definite clauses background knowledge.
     */
    Iterable<Clause> getBackgroundKnowledge();

    /* Asserts a definite clause into the background knowledge.
     *
     * @param definiteClause Clause to assert into the background knowledge.
     * @throws IllegalArgumentException Throws an IllegalArgumentException if the
     * sentence is not a definite clause.
     */
    void assertBackgroundKnowledge(DefiniteClause definiteClause) throws IllegalArgumentException;

    /* Asserts a fact into the clause base.
     *
     * @param fact Fact to assert into the facts.
     */
    void assertFact(Literal fact);

    /*
     * Retract all the clauses which unify with definiteClause.
     *
     * Retracts all clauses from the clausebase which unify with definiteClause.
     * This version requires the full body of the clause to unify.  @See  retractAllClauseWithHead(Literal)
     * if you want to retract all clauses matching a given head literal.
     *
     * @param definiteClause Pattern of definite clauses to retract.
     */
    void retractAllClausesWithUnifyingBody(DefiniteClause definiteClause);

    /* Returns a Collection of definite clauses whose head might match the specified clauseHead.
     *
     * The DefiniteClause returned can be either a Literal or a Clause from either the background
     * knowledge or the facts.
     *
     * There is no guarantee that head of the clauses in the returned set will match the clauseHead requested.
     * Depending on the indexing method, other predicateNames or arities might be returned.  However,
     * it is guaranteed that all clauses in the background knowledge and/or facts whose head does match
     * will be returned.
     *
     * The iteration order of the collection returned is guaranteed to match the
     * order in which the clauses were oridinally asserted.
     *
     * @param clauseHead Literal to match against head of clauses in fact base.
     * @param currentBinding Bindings currently applied to clauseHead.  If non-null, the binding
     * list will be applied against the head prior to lookup in the fact base.
     * @return Collection of Sentences that may match predicateName/arity, possible null.
     */
    List<DefiniteClause> getPossibleMatchingAssertions(Literal clauseHead, BindingList currentBinding);

    /* Checks to see if there are any possible matching clauses in the background knowledge.
     *
     * @param predName Predicate name to lookup.
     * @param arity Arity of predicate.
     * @return True if the fact base contains possible matching rules.
     */
    boolean checkForPossibleMatchingBackgroundKnowledge(PredicateName predName, int arity);

    /* Returns a Collection of background knowledge whose head might match the specified clauseHead.
     *
     * There is no guarantee that head of the clauses in the returned set will match the clauseHead requested.
     * Depending on the indexing method, other predicateNames or arities might be returned.  However,
     * it is guaranteed that all clauses in the fact base whose head does match will be returned.
     *
     * @param clauseHead Literal to match against head of clauses.
     * @param currentBinding Bindings currently applied to clauseHead.  If non-null, the binding
     * list will be applied against the head prior to lookup in the fact base.
     * @return Collection of Rules that may match predicateName/arity, possible null.
     */
    Iterable<Clause> getPossibleMatchingBackgroundKnowledge(Literal clauseHead, BindingList currentBinding);

    /* Checks to see if there are any possible matching facts in the factbase.
     * 
     * @param predName Predicate name to lookup.
     * @param arity Arity of predicate.
     * @return True if the fact base contains possible matching facts.
     */
    boolean checkForPossibleMatchingFacts(PredicateName predName, int arity);

    /* Returns a Collection of facts which might match the specified clauseHead.
     *
     * There is no guarantee that head of the clauses in the returned set will match the clauseHead requested.
     * Depending on the indexing method, other predicateNames or arities might be returned.  However,
     * it is guaranteed that all clauses in the fact base whose head does match will be returned.
     *
     * @param clauseHead Literal to match against head of clauses.
     * @param currentBinding Bindings currently applied to clauseHead.
     * @return Collection of Sentences that may match predicateName/arity, possible null.
     */
    Iterable<Literal> getPossibleMatchingFacts(Literal clauseHead, BindingList currentBinding);

    ProcedurallyDefinedPredicateHandler getUserProcedurallyDefinedPredicateHandler();

    void setUserProcedurallyDefinedPredicateHandler(ProcedurallyDefinedPredicateHandler userDefinedPredicateHandler);

    boolean isOnlyInFacts(PredicateName predName, int arity);

}
