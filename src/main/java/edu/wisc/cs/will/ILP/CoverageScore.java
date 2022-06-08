package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;

/*
 * @author twalker
 */
public class CoverageScore implements Serializable {

    // TODO(hayesall): Utils for computing accuracy, etc. should probably be moved into here.

    private double truePositives  = 0;
    private double falsePositives = 0;
    private double trueNegatives  = 0;
    private double falseNegatives = 0;
    private final double falseNegativeMEstimate = 0;
    private final double truePositiveMEstimate  = 0;
    private final double falsePositiveMEstimate = 0;

    /* Creates a new instance of CoverageScore */
    public CoverageScore() {
    }

    public void setCounts(double tp, double fp, double tn, double fn) {
        this.setTruePositives( tp);
        this.setFalseNegatives(fn);
        this.setFalsePositives(fp);
        this.setTrueNegatives( tn);
    }

    public double getPrecision() {
        return Utils.getPrecision(truePositives + truePositiveMEstimate, falsePositives + falsePositiveMEstimate);
    }

    public double getRecall() {
        return Utils.getRecall(truePositives + truePositiveMEstimate, falseNegatives + falseNegativeMEstimate);
    }

    public double getF1() {
        return Utils.getF1(truePositives + truePositiveMEstimate, falsePositives + falsePositiveMEstimate, falseNegatives + falseNegativeMEstimate);
    }

    @Override
    public String toString() {
        return "CoverageScore(Object)";
    }

    public void addToTruePositive(double add) {
    	truePositives += add;
    }

    public void addToFalsePositive(double add) {
    	falsePositives += add;
    }

    public void addToTrueNegative(double add) {
    	trueNegatives += add;
    }

    public void addToFalseNegative(double add) {
    	falseNegatives += add;
    }

    public double getTruePositives() {
        return truePositives;
    }

    public void setTruePositives(double truePositives) {
        this.truePositives = truePositives;
    }

    public double getFalsePositives() {
        return falsePositives;
    }

    public void setFalsePositives(double falsePositives) {
        this.falsePositives = falsePositives;
    }

    public double getTrueNegatives() {
        return trueNegatives;
    }

    public void setTrueNegatives(double trueNegatives) {
        this.trueNegatives = trueNegatives;
    }

    public double getFalseNegatives() {
        return falseNegatives;
    }

    public void setFalseNegatives(double falseNegatives) {
        this.falseNegatives = falseNegatives;
    }

}
