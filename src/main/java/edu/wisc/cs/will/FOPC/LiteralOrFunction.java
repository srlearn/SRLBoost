package edu.wisc.cs.will.FOPC;

import java.util.List;

/** Interface describing the operations common between literals and terms.
 *
 * Literal and terms often play a similar role.  Literals are the arguments
 * of Clauses while Terms are the arguments of Functions.  Literals are easily
 * representable as Term via a Function.  Terms are representable as Literals
 * via either the TermAsSentence class or as a more direct translation from
 * a Function to a Literal.
 *
 * @author twalker
 */
public interface LiteralOrFunction {

    Function asFunction();

    Literal asLiteral();

    PredicateName getPredicateName();

    FunctionName getFunctionName();

    int getArity();

    PredicateNameAndArity getPredicateNameAndArity();

    List<Term> getArguments();

    Term getArgument(int index);

    HandleFOPCstrings getStringHandler();
}
