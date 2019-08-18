package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.SentenceVisitor;
import edu.wisc.cs.will.Utils.Utils;

/*
 * @author twalker
 */
public class SentenceUnifier {
    
    private static final SentenceUnifierVisitor SENTENCE_UNIFIER_VISITOR = new SentenceUnifierVisitor();

    public static BindingList unify(Sentence s1, Sentence s2, BindingList bl) {
        if ( bl == null ) bl = new BindingList();
        SentenceUnifierData data = new SentenceUnifierData(s2, bl);
        return s1.accept(SENTENCE_UNIFIER_VISITOR, data);
    }

    public static BindingList unify(Sentence s1, Sentence s2) {
        return unify(s1, s2, new BindingList());
    }

    private static class SentenceUnifierData {
        Sentence that;
        BindingList bl;

        SentenceUnifierData(Sentence that, BindingList bl) {
            this.that = that;
            this.bl = bl;
        }

        @Override
        public String toString() {
            return "";
        }
    }

    private static class SentenceUnifierVisitor implements  SentenceVisitor<BindingList, SentenceUnifierData> {

        public BindingList visitOtherSentence(Sentence otherSentence, SentenceUnifierData data) {
            Utils.warning("Unifying Quantified sentences not supported.");
            return null;
        }

        public BindingList visitConnectedSentence(ConnectedSentence sentence, SentenceUnifierData data) {
            if (!(data.that instanceof ConnectedSentence)) return null;

            ConnectedSentence that = (ConnectedSentence) data.that;

            if (!sentence.getConnective().equals(that.getConnective())) return null;

            if ( sentence.getSentenceA() == null && that.getSentenceA() != null ) return null;
            if ( sentence.getSentenceA() != null && that.getSentenceA() == null ) return null;
            if ( sentence.getSentenceB() == null && that.getSentenceB() != null ) return null;
            if ( sentence.getSentenceB() != null && that.getSentenceB() == null ) return null;

            Sentence s1;
            Sentence s2;
            SentenceUnifierData newData;

            s1 = sentence.getSentenceA();
            s2 = that.getSentenceA();

            newData = new SentenceUnifierData(s2, data.bl);
            if ( s1.accept(this, newData) == null ) return null;

            s1 = sentence.getSentenceB();
            s2 = that.getSentenceB();

            newData = new SentenceUnifierData(s2, data.bl);
            if ( s1.accept(this, newData) == null ) return null;

            return data.bl;
        }

        public BindingList visitQuantifiedSentence(QuantifiedSentence sentence, SentenceUnifierData data) {
            Utils.warning("Unifying Quantified sentences not supported.");
            return null;
        }

        public BindingList visitClause(Clause clause, SentenceUnifierData data) {
            if (!(data.that instanceof Clause)) return null;

            Clause that = (Clause)data.that;

            if ( clause.getPosLiteralCount() != that.getPosLiteralCount() || clause.getNegLiteralCount() != that.getNegLiteralCount() ) {
                return null;
            }

            for (int i = 0; i < clause.getPosLiteralCount(); i++) {
                Literal thisLiteral = clause.getPosLiteral(i);
                Literal thatLiteral = that.getPosLiteral(i);

                SentenceUnifierData newData = new SentenceUnifierData(thatLiteral, data.bl);
                BindingList bl = thisLiteral.accept(this, newData);
                if ( bl == null ) return null;
            }

            for (int i = 0; i < clause.getNegLiteralCount(); i++) {
                Literal thisLiteral = clause.getNegLiteral(i);
                Literal thatLiteral = that.getNegLiteral(i);

                SentenceUnifierData newData = new SentenceUnifierData(thatLiteral, data.bl);
                BindingList bl = thisLiteral.accept(this, newData);
                if ( bl == null ) return null;
            }

            return data.bl;
        }

        public BindingList visitLiteral(Literal literal, SentenceUnifierData data) {
            if (!(data.that instanceof Literal)) return null;

            return Unifier.UNIFIER.unify(literal, (Literal)data.that, data.bl);
        }



    }

    private SentenceUnifier() {
        // TODO(@hayesall): Unused method?
    }
}
