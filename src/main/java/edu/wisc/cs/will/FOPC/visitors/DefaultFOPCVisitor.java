package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.*;

import java.util.ArrayList;
import java.util.List;
 
/*
 * @author twalker
 */
public class DefaultFOPCVisitor<Data> implements SentenceVisitor<Sentence, Data>, TermVisitor<Term, Data> {

    protected DefaultFOPCVisitor() {
    }

    public Sentence visitOtherSentence(Sentence otherSentence) {
        return otherSentence;
    } 

    public Sentence visitConnectedSentence(ConnectedSentence sentence, Data data) {
        Sentence a = sentence.getSentenceA() == null ? null : sentence.getSentenceA().accept(this, data);
        Sentence b = sentence.getSentenceB() == null ? null : sentence.getSentenceB().accept(this, data);

        return getCombinedConnectedSentence(sentence, a, b);
    }

    /* Performs some "smart" recombining of connected sentences.
     *
     * This method attempts to handle cases where the subsentence visits return null.  In many
     * cases, specially handling will be required to maintain the semantics of the returned
     * sentence, but this provided a simple why to handle null values.
     */
    private static Sentence getCombinedConnectedSentence(ConnectedSentence originalSentence, Sentence newA, Sentence newB) {

        Sentence result;

        if (ConnectiveName.isaNOT(originalSentence.getConnective().name)) {
            if (newB == null) {
                newB = originalSentence.getStringHandler().trueLiteral;
            }
            result = originalSentence.getStringHandler().getConnectedSentence(originalSentence.getConnective(), newB);
        }
        else {
            if (newA == null && newB == null) {
                result = null;
            }
            else if (newB == null) {
                result = newA;
            }
            else if (newA == null) {
                result = newB;
            }
            else {
                result = originalSentence.getStringHandler().getConnectedSentence(newA, originalSentence.getConnective(), newB);
            }
        }

        return result;

    }

    public Sentence visitClause(Clause clause, Data data) {
        List<Literal> positiveLits = null;
        List<Literal> negativeLits = null;

        if (clause.getPosLiteralCount() > 0) {
            positiveLits = new ArrayList<>();
            for (Literal literal : clause.getPositiveLiterals()) {
                Sentence newStuff = literal.accept(this, data);
                if (newStuff != null) {
                    positiveLits.addAll(newStuff.asClause().getPositiveLiterals());
                }
            }
        }

        if (clause.getNegLiteralCount() > 0) {
            negativeLits = new ArrayList<>();
            for (Literal literal : clause.getNegativeLiterals()) {
                Sentence newStuff = literal.accept(this, data);
                if (newStuff != null) {
                    negativeLits.addAll(newStuff.asClause().getPositiveLiterals());
                }
            }
        }

        return clause.getStringHandler().getClause(positiveLits, negativeLits);
    }

    /* Visit the literal.
     *
     * The DefaultFOPCVisitor assumes that the return value of visitLiteral
     * is either a Literal, a Clause with all positive literals, or null.
     *
     * Children can return other sentence forms, but should be aware that
     * unexpected behavior will result.
     */
    public Sentence visitLiteral(Literal literal, Data data) {

        Literal result = literal;

        List<Term> newTerms;

        if (literal.getArity() != 0) {
            newTerms = new ArrayList<>();

            for (Term term : literal.getArguments()) {
                Term newTerm = term.accept(this, data);
                newTerms.add(newTerm);
            }

            result = literal.getStringHandler().getLiteral(literal, newTerms);
        }

        return result;
    }

    public Term visitFunction(Function function, Data data) {

        Function result = function;

        List<Term> newTerms;

        if (function.getArity() != 0) {
            newTerms = new ArrayList<>();
            for (Term term : function.getArguments()) {
                Term newTerm = term.accept(this, data);
                newTerms.add(newTerm);
            }

            result = function.getStringHandler().getFunction(function, newTerms);
        }

        return result;

    }

    public Term visitVariable(Variable variable, Data data) {
        return variable;
    }

    public Term visitNumericConstant(NumericConstant numericConstant) {
        return numericConstant;
    }

    public Term visitStringConstant(StringConstant stringConstant) {
        return stringConstant;
    }

    public Term visitOtherTerm(Term term) {
        return term;
    }
}
