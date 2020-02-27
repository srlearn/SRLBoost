package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.*;

import java.util.Objects;

/*
 * @author twalker
 */
public class RelevantModeInformation implements RelevantInformation, Cloneable {

    private final Example example;

    private boolean relevanceFromPositiveExample;

    private final Literal mode;

    private final RelevanceStrength relevanceStrength;

    RelevantModeInformation(Example example, Literal mode, RelevanceStrength relevanceStrength) {
        this.example = example;
        this.relevanceFromPositiveExample = true;
        this.mode = mode;
        this.relevanceStrength = relevanceStrength;
    }

    @Override
    public String toString() {
        return example + " : " + mode + ", " + getRelevanceStrength();
    }

    /*
     * @return the relevanceStrength
     */
    private RelevanceStrength getRelevanceStrength() {
        return relevanceStrength;
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


    protected RelevantModeInformation clone() throws CloneNotSupportedException {
        return (RelevantModeInformation) super.clone();
    }

}
