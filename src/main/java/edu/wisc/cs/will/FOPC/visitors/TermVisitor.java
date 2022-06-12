package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.*;

/**
 * @author twalker
 */
public interface TermVisitor<Return, Data> {
    Return visitFunction(Function function, Data data);

    Return visitVariable(Variable variable, Data data);

    Return visitNumericConstant(NumericConstant numericConstant);
    Return visitStringConstant(StringConstant stringConstant);
    Return visitOtherTerm(Term term);
}
