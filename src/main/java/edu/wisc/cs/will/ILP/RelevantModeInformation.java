package edu.wisc.cs.will.ILP;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.ConnectiveName;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;

/*
 * @author twalker
 */
public class RelevantModeInformation implements RelevantInformation, Cloneable {

    private Example example;

    private boolean relevanceFromPositiveExample;

    private Literal mode;

    private RelevanceStrength relevanceStrength;

    RelevantModeInformation(Example example, boolean relevanceFromPositiveExample, Literal mode, RelevanceStrength relevanceStrength) {
        this.example = example;
        this.relevanceFromPositiveExample = relevanceFromPositiveExample;
        this.mode = mode;
        this.relevanceStrength = relevanceStrength;
    }

    @Override
    public String toString(String prefix) {
        return prefix + example + " : " + mode + ", " + getRelevanceStrength();
    }

    @Override
    public String toString() {
        return toString("");
    }



    @Override
    public Example getExample() {
        return example;
    }

    public boolean isRelevanceFromPositiveExample() {
        return relevanceFromPositiveExample;
    }

    public void setRelevanceFromPositiveExample(boolean positive) {
        this.relevanceFromPositiveExample = positive;
    }

    @Override
    public boolean isEquivalentUptoVariableRenaming(RelevantInformation info) {

        boolean result = false;

        if (info instanceof RelevantModeInformation) {
            RelevantModeInformation that = (RelevantModeInformation) info;
            result = this.mode.equals(that.mode);
        }

        return result;
    }

    @Override
    public RelevantModeInformation getGeneralizeRelevantInformation() {
        return this;
    }

    /*
     * @return the relevanceStrength
     */
    public RelevanceStrength getRelevanceStrength() {
        return relevanceStrength;
    }

    @Override
    public boolean prove(HornClauseContext context) {
        return relevanceFromPositiveExample;
    }

    public PredicateNameAndArity getPredicateNameAndArity() {
        return mode.getPredicateNameAndArity();
    }

    List<Term> getSignature() {
        List<Term> signature = new ArrayList<>();
        for (int i = 0; i < mode.getArity(); i++) { // TREVOR: this is probably ok since we only have 'flat' Examples, but there is (possibly) more robust code.  See how I did it for the negation-by-failure stuff.
            signature.add(mode.getStringHandler().getStringConstant("constant"));
        }
        return signature;
    }

    List<TypeSpec> getTypeSpecs() {
        return mode.getTypeSpecs();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final RelevantModeInformation other = (RelevantModeInformation) obj;
        if (!Objects.equals(this.example, other.example)) {
            return false;
        }
        if (this.relevanceFromPositiveExample != other.relevanceFromPositiveExample) {
            return false;
        }
        if (!Objects.equals(this.mode, other.mode)) {
            return false;
        }
        return this.relevanceStrength == other.relevanceStrength;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 43 * hash + (this.example != null ? this.example.hashCode() : 0);
        hash = 43 * hash + (this.relevanceFromPositiveExample ? 1 : 0);
        hash = 43 * hash + (this.mode != null ? this.mode.hashCode() : 0);
        hash = 43 * hash + (this.relevanceStrength != null ? this.relevanceStrength.hashCode() : 0);
        return hash;
    }


    public RelevantModeInformation copy() {
        try {
            return clone();
        } catch (CloneNotSupportedException ex) {
            return null;
        }
    }

    protected RelevantModeInformation clone() throws CloneNotSupportedException {
        return (RelevantModeInformation) super.clone();
    }

    public boolean isValidAdvice(AdviceProcessor ap) {
        return true;
    }

    ConnectedSentence getSentence(HornClauseContext context) {
        List<DefiniteClause> clauses = context.getClausebase().getAssertions(getPredicateNameAndArity());

        ConnectedSentence result = null;

        if ( clauses != null && !clauses.isEmpty()) {
            if ( clauses.size() == 1) {
                Clause theClause = clauses.get(0).getDefiniteClauseAsClause();
                result = theClause.asConnectedSentence();
            }
            else {

                Sentence s = null;

                BindingList bl = new BindingList();

                Literal firstHead = null;

                for (DefiniteClause definiteClause : clauses) {
                    Clause aClause = definiteClause.getDefiniteClauseAsClause();
                    Literal head = aClause.getDefiniteClauseHead();

                    if ( firstHead == null) {
                        firstHead = head;
                        s = context.getStringHandler().getClause(null, aClause.getNegativeLiterals());
                    }
                    else {
                        // This probably won't work...but I have no examples of when it
                        // will fail, so whatever...
                        bl = Unifier.UNIFIER.unify(firstHead, head, bl);
                        aClause = aClause.applyTheta(bl);
                        s = context.getStringHandler().getConnectedSentence(s, ConnectiveName.OR, context.getStringHandler().getClause(null, aClause.getNegativeLiterals()));
                    }
                }

                result = context.getStringHandler().getConnectedSentence(s, ConnectiveName.IMPLIES, firstHead);
            }

        }

        return result;
    }

    public boolean subsumes(RelevantInformation that) {
        return false;
    }
}
