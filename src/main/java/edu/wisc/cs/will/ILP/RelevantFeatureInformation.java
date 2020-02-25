package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.RelevanceStrength;

/*
 * @author twalker
 */
public class RelevantFeatureInformation implements RelevantInformation, Cloneable {

    private boolean relevanceFromPositiveExample = true;

    public boolean isRelevanceFromPositiveExample() {
        return relevanceFromPositiveExample;
    }

    public void setRelevanceFromPositiveExample(boolean positive) {
        this.relevanceFromPositiveExample = positive;
    }

    @Override
    public RelevantFeatureInformation getGeneralizeRelevantInformation() {
        return this;
    }

    public RelevanceStrength getRelevanceStrength() {
        // TODO(@hayesall): Always returns null.
        return null;
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
        return this.relevanceFromPositiveExample == other.relevanceFromPositiveExample;
    }

    public boolean subsumes(RelevantInformation that) {
        return false;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 67 * hash + (this.relevanceFromPositiveExample ? 1 : 0);
        return hash;
    }

    @Override
    public String toString() {
        // TODO(@hayesall): This `toString()` method contains quite a few `null` after factoring out unused values.
        return null + " : " + null + ", " + null;
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
