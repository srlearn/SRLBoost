package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;

import java.util.ArrayList;
import java.util.List;

/* This is a self contained Horn clause prover.
 *
 * This provides an easily usable API for performing proofs.
 *
 * @author twalker
 */
public class DefaultHornClauseContext implements HornClauseContext {

    private final HandleFOPCstrings stringHandler;

    private FileParser parser;

    private final HornClausebase clausebase;

    private Unifier unifier;

    public DefaultHornClauseContext(HornClausebase clausebase) {
        if (clausebase == null) {
            throw new IllegalStateException("Clausebase must be non-null.");
        }

        this.clausebase    = clausebase;
        this.stringHandler = clausebase.getStringHandler();

        checkSetup();
    }

    private void checkSetup() {
        if (clausebase != null && clausebase.getStringHandler() != stringHandler) {
            throw new IllegalStateException("Clausebase stringHandler does not match Context string handler.");
        }
        if (parser != null && parser.stringHandler != stringHandler) {
            throw new IllegalStateException("Parser stringHandler does not match Context string handler.");
        }
    }

    /* Asserts the definite clause in the fact base of the prover.
     *
     * @param definiteClause A definite clause to be asserted in the fact base.
     * @throws IllegalArgumentException Throws an illegal argument exceptions if
     * the clause is not definite.
     */
    @Override
    public void assertDefiniteClause(Clause definiteClause) throws IllegalArgumentException {
        if (!definiteClause.isDefiniteClause()) {
            throw new IllegalArgumentException("Clause '" + definiteClause + "' is not definite.");
        }

        getClausebase().assertBackgroundKnowledge(definiteClause);
    }

    @Override
    public void assertSentences(Iterable<? extends Sentence> sentences) throws IllegalArgumentException {
        if (sentences != null) {
            List<DefiniteClause> clausesToAssert = new ArrayList<>();

            // First parse the sentences and make sure the all evaluate to
            // definite clauses.
            for (Sentence sentence : sentences) {
                if (sentence instanceof Clause) {
                    Clause clause = (Clause) sentence;
                    if (clause.isDefiniteClause()) {
                        clausesToAssert.add(clause);
                    }
                }
                else if (sentence instanceof Literal) {
                    Literal literal = (Literal) sentence;
                    clausesToAssert.add(literal);
                }
                else {
                    List<Clause> clauses2 = sentence.convertToClausalForm();
                    for (Clause clause : clauses2) {
                        if (clause.isDefiniteClause()) {
                            clausesToAssert.add(clause);
                        }
                        else {
                            throw new IllegalArgumentException("Logic sentence '" + clause + "' is not a definite clause.");
                        }
                    }
                }
            }

            // Next assert the definite clauses into the clausebase.
            for (DefiniteClause clause : clausesToAssert) {
                if (clause instanceof Clause) {
                    Clause clause1 = (Clause) clause;
                    getClausebase().assertBackgroundKnowledge(clause1);
                }
                else if (clause instanceof Literal) {
                    Literal literal = (Literal) clause;
                    getClausebase().assertFact(literal);
                }
            }
        }
    }

    @Override
    public HornClausebase getClausebase() {
        return clausebase;
    }

    @Override
    public FileParser getFileParser() {
        if (parser == null) {
            parser = new FileParser(stringHandler);
        }

        return parser;
    }

    @Override
    public Unifier getUnifier() {
        if (unifier == null) {
            unifier = new Unifier();
        }

        return unifier;
    }

    @Override
    public HandleFOPCstrings getStringHandler() {
        return stringHandler;
    }

    @Override
    public String toString() {
        return "DefaultHornClauseContext [\n" + getClausebase() + "]";
    }

}
