package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.Utils.Utils;

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

    private HornClausebase clausebase;

    private Unifier unifier;

    private List<ProofListener> proofListenerList = null;


    public DefaultHornClauseContext() {
        this.stringHandler = new HandleFOPCstrings();
    }

    public DefaultHornClauseContext(HandleFOPCstrings stringHandler) {
    	this.stringHandler = (stringHandler != null ? stringHandler : new HandleFOPCstrings());  // Make sure we have one.
    }

    public DefaultHornClauseContext(HandleFOPCstrings stringHandler, FileParser parser) {
        this.stringHandler = (stringHandler != null ? stringHandler : new HandleFOPCstrings());
        this.parser        = parser;

        checkSetup();
    }

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

    /* Attempts to prove the clause <code>goal</code>.
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
    @Override
    public BindingList prove(String goal) throws IllegalArgumentException {
            SLDQuery sldQuery = parseGoal(goal);

            return prove(sldQuery);
    }

    @Override
    public BindingList prove(SLDQuery goal) throws IllegalArgumentException {
            try {
                HornClauseProver prover = new HornClauseProver(stringHandler, getClausebase());

                fireProving(goal);

                return prover.prove(goal);
            } catch (Throwable t) {
                Utils.warning("Error proving goal '" + goal + "!");
    			Utils.reportStackTrace(t);
                // Just catch everything and return null...
                return null;
            }
    }

    private SLDQuery parseGoal(String goal) throws IllegalArgumentException {
        if (!goal.endsWith(".")) {
            goal = goal + ".";
        }

        List<Sentence> sentences = getFileParser().readFOPCstream(goal);

        if ( sentences.isEmpty() ) {
            return getStringHandler().getClause();
        }

        if (sentences.size() != 1) {
            throw new IllegalArgumentException("Goal '" + goal + "' did not parse into a single conjunct of literals.");
        }


        List<Clause> clauses = sentences.get(0).convertToClausalForm();

        List<Literal> literalsToProve = new ArrayList<>();

        for (Clause clause : clauses) {
            if (clause.getNegLiteralCount() != 0) {
                throw new IllegalArgumentException("Negated literal '" + clause + "' found in goal '" + goal + "'.  Goal should be conjunct of positive literals.");
            }

            if (clause.posLiterals != null) {
                literalsToProve.addAll(clause.posLiterals);
            }
        }

        return getStringHandler().getClause(null, literalsToProve);
    }

    @Override
    public HornClausebase getClausebase() {
        if (clausebase == null) {
            this.clausebase = new DefaultHornClausebase(stringHandler);
        }

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

    private void fireProving(SLDQuery query) {
        if ( proofListenerList != null ) {
            for (ProofListener proofListener : proofListenerList) {
                proofListener.proving(query);
            }
        }
    }
}
