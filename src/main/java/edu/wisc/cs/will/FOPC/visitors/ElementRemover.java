package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.*;

/*
 * @author twalker
 */
public class ElementRemover {

    private static final ElementRemoverVisitor ELEMENT_REMOVER_VISITOR = new ElementRemoverVisitor();

    public static Sentence removeElement(Sentence sentence, ElementPath path) {
        ElementRemoverData data = new ElementRemoverData(path);

        return sentence.accept(ELEMENT_REMOVER_VISITOR, data);
    }

    private static class ElementRemoverData extends ElementPositionVisitor.ElementPositionData {
        ElementPath pathToRemove;

        ElementRemoverData(ElementPath pathToRemove) {
            this.pathToRemove = pathToRemove;
        }
    }

    private static class ElementRemoverVisitor extends ElementPositionVisitor<ElementRemoverData>{

        @Override
        public Clause visitClause(Clause clause, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitClause(clause, data);
        }

        @Override
        public ConnectedSentence visitConnectedSentence(ConnectedSentence sentence, ElementRemoverData data) {
            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitConnectedSentence(sentence, data);
        }

        @Override
        public Term visitFunction(Function function, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitFunction(function, data);
        }

        @Override
        public Term visitListAsTerm(ListAsTerm listAsTerm, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitListAsTerm(listAsTerm, data);
        }

        @Override
        public Literal visitLiteral(Literal literal, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitLiteral(literal, data);
        }

        @Override
        public Term visitNumericConstant(NumericConstant numericConstant, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitNumericConstant(numericConstant, data);
        }

        @Override
        public QuantifiedSentence visitQuantifiedSentence(QuantifiedSentence sentence, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitQuantifiedSentence(sentence, data);
        }

        @Override
        public Term visitSentenceAsTerm(SentenceAsTerm sentenceAsTerm, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitSentenceAsTerm(sentenceAsTerm, data);
        }

        @Override
        public Term visitStringConstant(StringConstant stringConstant, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitStringConstant(stringConstant, data);
        }

        @Override
        public Term visitVariable(Variable variable, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }
            
            return super.visitVariable(variable, data);
        }

    }

    private ElementRemover() {
    }
}
