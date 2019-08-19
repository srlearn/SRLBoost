package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;

/*
 * @author twalker
 */
public interface HornClauseContext {

    HandleFOPCstrings getStringHandler();
    FileParser        getFileParser();
    HornClausebase    getClausebase();
    Unifier           getUnifier();

    /* Asserts the definite clause in the fact base of the prover.
     *
     * @param definiteClause A definite clause to be asserted in the fact base.
     * @throws IllegalArgumentException Throws an illegal argument exceptions if
     * the clause is not definite.
     */
    void assertDefiniteClause(Clause definiteClause) throws IllegalArgumentException;

    /* Asserts the definite clauses from the iterable into the clausebase.
     *
     * The sentences must definite clauses.  If any of the sentences are not
     * definite clauses, this method will throw an IllegalArgumentException
     * and none of the clauses will be asserted.
     *
     * @param sentences An iterator over a set of definite clauses.
     * @throws IllegalArgumentException Throws an illegal argument exceptions if
     * any of the clauses to be asserted are not definite clauses.
     */
    void assertSentences(Iterable<? extends Sentence> sentences) throws IllegalArgumentException;

    /*
     * Attempts to prove the clause <code>goal</code>.
     *
     * The goal should a single line string containing the a conjunct of literals
     * to prove.
     *
     * The theorem prover will attempt to prove the statement, given the currently
     * asserted fact base.
     *
     * @param goal A single line string containing a conjunct of literals to prove, given the
     * current asserted fact base.
     *
     * @return If the goal is successful, returns the BindingList for the first
     * sucessful proof found.
     *
     * @throws IllegalArgumentException Throws an IllegalArgumentException if the goal is
     * not parsable or if the
     */
    BindingList prove(String goal) throws IllegalArgumentException;

    /*
     * Attempts to prove the SLDQuery <code>goal</code>.
     *
     * The SLDQuery should be a legal SLD query.  This includes sentences which evaluate
     * to a single clause with no positive literals and one or more negative literals,
     * bare literals, and functions of terms.
     *
     * The theorem prover will attempt to prove the query, given the currently
     * asserted fact base.
     *
     * @param goal A legal SLD query.
     *
     * @return If the goal is successful, returns the BindingList for the first
     * successful proof found.
     *
     * @throws IllegalArgumentException Throws an IllegalArgumentException if the goal
     * can not be converted into a legal SLD query.
     */
    BindingList prove(SLDQuery goal) throws IllegalArgumentException;

}
