package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC.visitors.ElementPositionVisitor.ElementPositionData;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 *
 * @author twalker
 */
public class ElementPositionVisitor<Data extends ElementPositionData> extends DefaultFOPCVisitor<Data> {

    private ElementPositionListener<Data> listener = null;

    public <T extends ElementPositionListener<Data>> ElementPositionVisitor(T listener) {
        this.listener = listener;
    }

    protected ElementPositionVisitor() {
    }

    public ConnectedSentence visitConnectedSentence(ConnectedSentence sentence, Data data) {

        if (listener != null) {
            if (!listener.visiting(sentence, data)) {
                return null;
            }
        }

        data.pushPosition(0);
        Sentence a = sentence.getSentenceA() == null ? null : sentence.getSentenceA().accept(this, data);
        data.popPosition();

        if (a == null) {
            return null;
        }

        data.pushPosition(1);
        Sentence b = sentence.getSentenceB() == null ? null : sentence.getSentenceB().accept(this, data);
        data.popPosition();

        if (b == null) {
            return null;
        }

        return sentence.getStringHandler().getConnectedSentence(a, sentence.getConnective(), b);
    }

    public QuantifiedSentence visitQuantifiedSentence(QuantifiedSentence sentence, Data data) {
        if (listener != null) {
            if (!listener.visiting(sentence, data)) {
                return null;
            }
        }

        data.pushPosition(0);
        Sentence newSentence = sentence.accept(this, data);
        data.popPosition();

        if (newSentence == null) {
            return null;
        }

        return sentence.replaceVariablesAndBody(sentence.variables, newSentence);
    }

    @Override
    public Term visitFunction(Function function, Data data) {
        if (listener != null) {
            if (!listener.visiting(function, data)) {
                return null;
            }
        }

        List<Term> newTerms = null;

        if (function.getArity() != 0) {
            newTerms = new ArrayList<>();

            for (int i = 0; i < function.getArity(); i++) {
                data.pushPosition(i);
                Term term = function.getArgument(i);
                Term newTerm = term.accept(this, data);
                data.popPosition();
                if (newTerm == null) {
                    return null;
                }
                else {
                    newTerms.add(newTerm);
                }
            }
        }
        return function.getStringHandler().getFunction(function, newTerms);
    }

    public Clause visitClause(Clause clause, Data data) {
        if (listener != null) {
            if (!listener.visiting(clause, data)) {
                return null;
            }
        }

        List<Literal> positiveLits = Collections.EMPTY_LIST;
        List<Literal> negativeLits = Collections.EMPTY_LIST;

        if (clause.getPosLiteralCount() > 0) {
            positiveLits = new ArrayList<>();
            for (int i = 0; i < clause.getPosLiteralCount(); i++) {
                Literal literal = clause.getPosLiteral(i);
                data.pushPosition(i);
                Literal newLit = (Literal) literal.accept(this, data);
                data.popPosition();

                if (newLit != null) {
                    positiveLits.add(newLit);
                }
            }
        }

        if (clause.getNegLiteralCount() > 0) {
            negativeLits = new ArrayList<>();
            for (int i = 0; i < clause.getNegLiteralCount(); i++) {
                Literal literal = clause.getNegLiteral(i);
                data.pushPosition(i);
                Literal newLit = (Literal) literal.accept(this, data);

                data.popPosition();
                if (newLit != null) {
                    negativeLits.add(newLit);
                }
            }
        }

        if (positiveLits.isEmpty() && negativeLits.isEmpty()) {
            return null;
        }
        else {
            return clause.getStringHandler().getClause(positiveLits, negativeLits);
        }
    }

    public Literal visitLiteral(Literal literal, Data data) {

        if (listener != null) {
            if (!listener.visiting(literal, data)) {
                return null;
            }
        }

        Literal result = literal;

        if (literal.getArity() != 0) {
            List<Term> newTerms = new ArrayList<>();
            for (int i = 0; i < literal.getArity(); i++) {
                Term term = literal.getArgument(i);
                data.pushPosition(i);
                Term newTerm = term.accept(this, data);
                data.popPosition();
                if (newTerm != null) {
                    newTerms.add(newTerm);
                }
            }

            result = newTerms.isEmpty() ? null : literal.getStringHandler().getLiteral(literal.predicateName, newTerms);
        }

        return result;
    }

    public Term visitListAsTerm(ListAsTerm listAsTerm, Data data) {

        if (listener != null) {
            if (!listener.visiting(listAsTerm, data)) {
                return null;
            }
        }

        Term result = listAsTerm;

        if (listAsTerm.getObjects() != null) {
            List<Term> objects = new ArrayList<>();
            result = listAsTerm.getStringHandler().getListAsTerm(objects);
        }

        return result;
    }

    @Override
    public Term visitNumericConstant(NumericConstant numericConstant, Data data) {
        if (listener != null) {
            if (!listener.visiting(numericConstant, data)) {
                return null;
            }
        }

        return numericConstant;
    }

    @Override
    public Term visitSentenceAsTerm(SentenceAsTerm sentenceAsTerm, Data data) {
        if (listener != null) {
            if (!listener.visiting(sentenceAsTerm, data)) {
                return null;
            }
        }

        data.pushPosition(0);
        Sentence s = sentenceAsTerm.sentence.accept(this, data);
        data.popPosition();
        if (s == null) {
            return null;
        }
        else {
            return s.asTerm();
        }
    }

    @Override
    public Term visitStringConstant(StringConstant stringConstant, Data data) {
        if (listener != null) {
            if (!listener.visiting(stringConstant, data)) {
                return null;
            }
        }

        return stringConstant;
    }

    @Override
    public Term visitVariable(Variable variable, Data data) {
        if (listener != null) {
            if (!listener.visiting(variable, data)) {
                return null;
            }
        }

        return variable;
    }

    public static class ElementPositionData {

        protected ElementPath currentPosition = new ElementPath(0);

        public ElementPositionData() {
        }

        public ElementPath getCurrentPosition() {
            return currentPosition;
        }

        void pushPosition(int position) {
            if (currentPosition == null) {
                currentPosition = new ElementPath(position);
            }
            else {
                currentPosition = new ElementPath(currentPosition, position);
            }
        }

        void popPosition() {
            if (currentPosition != null) {
                currentPosition = currentPosition.getParent();
            }
        }

        @Override
        public String toString() {
            return "ElementPositionData {" + "\n  currentPosition=" + currentPosition + "\n}";
        }
    }
}
