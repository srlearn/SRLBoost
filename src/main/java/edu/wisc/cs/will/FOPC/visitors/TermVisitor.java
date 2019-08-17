package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.ConsCell;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.ListAsTerm;
import edu.wisc.cs.will.FOPC.LiteralAsTerm;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.SentenceAsTerm;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;

/**
 * @author twalker
 */
public interface TermVisitor<Return, Data> {
    Return visitFunction(Function function, Data data);
    Return visitConsCell(ConsCell consCell, Data data);
    Return visitVariable(Variable variable, Data data);
    Return visitSentenceAsTerm(SentenceAsTerm sentenceAsTerm, Data data);
    Return visitLiteralAsTerm(LiteralAsTerm literalAsTerm, Data data);
    Return visitListAsTerm(ListAsTerm listAsTerm, Data data);
    Return visitNumericConstant(NumericConstant numericConstant, Data data);
    Return visitStringConstant(StringConstant stringConstant, Data data);
    Return visitOtherTerm(Term term, Data data);
}
