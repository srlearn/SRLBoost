package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.QuantifiedSentence;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;

import java.util.ArrayList;
import java.util.List;

/**
 * @author twalker
 */
public class DefaultSentenceVisitor<Data> implements SentenceVisitor<Sentence, Data>{

    private TermVisitor<Term, Data> termVisitor;

    protected DefaultSentenceVisitor() {}

    protected TermVisitor<Term, Data> getTermVisitor() {
        return termVisitor;
    }

    protected void setTermVisitor(TermVisitor<Term, Data> termVisitor) {
        this.termVisitor = termVisitor;
    }

    public Sentence visitOtherSentence(Sentence otherSentence, Data data) {
        return otherSentence;
    }

    public ConnectedSentence visitConnectedSentence(ConnectedSentence sentence, Data data) {
        Sentence a = sentence.getSentenceA() == null ? null : sentence.getSentenceA().accept(this, data);
        Sentence b = sentence.getSentenceB() == null ? null : sentence.getSentenceB().accept(this, data);

        return sentence.getStringHandler().getConnectedSentence(a, sentence.getConnective(), b);
    }

    public QuantifiedSentence visitQuantifiedSentence(QuantifiedSentence sentence, Data data) {
        Sentence newBody = sentence.body.accept(this, data);
        return sentence.replaceVariablesAndBody(sentence.variables, newBody);
    }

    public Clause visitClause(Clause clause, Data data) {
        List<Literal> positiveLits = null;
        List<Literal> negativeLits = null;

        if ( clause.getPosLiteralCount() > 0 ) {
            positiveLits = new ArrayList<>();
            for (Literal literal : clause.getPositiveLiterals()) {
                Literal newLit = (Literal) literal.accept(this, data);
                positiveLits.add(newLit);
            }
        }

        if ( clause.getNegLiteralCount() > 0 ) {
            negativeLits = new ArrayList<>();
            for (Literal literal : clause.getNegativeLiterals()) {
                Literal newLit = (Literal) literal.accept(this, data);
                negativeLits.add(newLit);
            }
        }

        return clause.getStringHandler().getClause(positiveLits, negativeLits);
    }

    public Literal visitLiteral(Literal literal, Data data) {
        
        Literal result = literal;

        if ( termVisitor != null ) {
            List<Term> newTerms = null;

            if ( literal.getArity() != 0 ) {
                newTerms = new ArrayList<>();
                for (Term term : literal.getArguments()) {
                    Term newTerm = term.accept(termVisitor, data);
                    newTerms.add(newTerm);
                }
            }
            
            result = literal.getStringHandler().getLiteral(literal, newTerms);
        }
        
        return result;
    }

}
