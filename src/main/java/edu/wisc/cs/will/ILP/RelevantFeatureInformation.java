package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;

import java.util.Objects;

/*
 * @author twalker
 */
public class RelevantFeatureInformation implements RelevantInformation, Cloneable {

    Example example;

    private boolean relevanceFromPositiveExample = true;

    private PredicateNameAndArity predicateNameAndArity;

    private RelevanceStrength relevanceStrength;

    public RelevantFeatureInformation(Example example, PredicateNameAndArity predicateNameAndArity, RelevanceStrength relevanceStrength) {
        this.example = example;
        this.predicateNameAndArity = predicateNameAndArity;
        this.relevanceStrength = relevanceStrength;
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

        if (info instanceof RelevantFeatureInformation) {
            RelevantFeatureInformation that = (RelevantFeatureInformation) info;
            result = this.getPredicateNameAndArity().equals(that.getPredicateNameAndArity());
        }

        return result;
    }

    @Override
    public RelevantFeatureInformation getGeneralizeRelevantInformation() {
        return this;
    }

    public RelevanceStrength getRelevanceStrength() {
        return relevanceStrength;
    }

    @Override
    public boolean prove(HornClauseContext context) {

        return relevanceFromPositiveExample;

    }

    public PredicateNameAndArity getPredicateNameAndArity() {
        return predicateNameAndArity;
    }

    public void setPredicateNameAndArity(PredicateNameAndArity predicateNameAndArity) {
        this.predicateNameAndArity = predicateNameAndArity;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final RelevantFeatureInformation other = (RelevantFeatureInformation) obj;
        if (!Objects.equals(this.example, other.example)) {
            return false;
        }
        if (this.relevanceFromPositiveExample != other.relevanceFromPositiveExample) {
            return false;
        }
        if (!Objects.equals(this.predicateNameAndArity, other.predicateNameAndArity)) {
            return false;
        }
        return this.relevanceStrength == other.relevanceStrength;
    }

    public boolean subsumes(RelevantInformation that) {
        return false;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 67 * hash + (this.example != null ? this.example.hashCode() : 0);
        hash = 67 * hash + (this.relevanceFromPositiveExample ? 1 : 0);
        hash = 67 * hash + (this.predicateNameAndArity != null ? this.predicateNameAndArity.hashCode() : 0);
        hash = 67 * hash + (this.relevanceStrength != null ? this.relevanceStrength.hashCode() : 0);
        return hash;
    }

    public String toString(String prefix) {
        return prefix + example + " : " + getPredicateNameAndArity() + ", " + getRelevanceStrength();
    }

    public RelevantFeatureInformation copy() {
        try {
            return clone();
        } catch (CloneNotSupportedException ex) {
            return null;
        }
    }

    protected RelevantFeatureInformation clone() throws CloneNotSupportedException {
        return (RelevantFeatureInformation) super.clone();
    }

    public boolean isValidAdvice(AdviceProcessor ap) {
        return true;
    }

}
