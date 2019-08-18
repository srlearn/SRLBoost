package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.QuantifiedSentence;
import edu.wisc.cs.will.FOPC.Sentence;

/*
 * @author twalker
 */
public interface SentenceVisitor<Return, Data> {
    Return visitOtherSentence(Sentence otherSentence, Data data);
    Return visitConnectedSentence(ConnectedSentence sentence, Data data);
    Return visitQuantifiedSentence(QuantifiedSentence sentence, Data data);
    Return visitClause(Clause clause, Data data);
    Return visitLiteral(Literal literal, Data data);
}
