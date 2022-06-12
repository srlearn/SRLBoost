package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.*;

/**
 * @author twalker
 */
public interface TermVisitor<Return, Data> {
    Return visitFunction(Function function, Data data);

    Return visitVariable(Variable variable, Data data);
    Return visitSentenceAsTerm(SentenceAsTerm sentenceAsTerm, Data data);
    Return visitLiteralAsTerm(LiteralAsTerm literalAsTerm, Data data);
    Return visitListAsTerm(ListAsTerm listAsTerm, Data data);
    Return visitNumericConstant(NumericConstant numericConstant);
    Return visitStringConstant(StringConstant stringConstant);
    Return visitOtherTerm(Term term);
}
