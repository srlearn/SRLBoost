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

}
