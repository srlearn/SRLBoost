package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;

/*
 * @author twalker
 */
public class CoverageScore implements Serializable {

    private static final long serialVersionUID = -602218797572752941L;
    private double truePositives = 0;
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

    private double getAccuracy() {
        double trueNegativeMEstimate = 0;
        return Utils.getAccuracy(truePositives + truePositiveMEstimate, falsePositives + falsePositiveMEstimate, trueNegatives + trueNegativeMEstimate, falseNegatives + falseNegativeMEstimate);
    }

    public double getF1() {
        return Utils.getF1(truePositives + truePositiveMEstimate, falsePositives + falsePositiveMEstimate, falseNegatives + falseNegativeMEstimate);
    }

    private String toLongString() {
        StringBuilder sb = new StringBuilder();

        double maxValue = Utils.max(trueNegatives, truePositives, falseNegatives, falsePositives);


        int columnWidth = 6;

        boolean nonInteger = (trueNegatives != Math.floor(trueNegatives) || truePositives != Math.floor(truePositives) || falseNegatives != Math.floor(falseNegatives) || falsePositives != Math.floor(falsePositives));

        if (maxValue > 0 && !Double.isInfinite(maxValue) && !Double.isNaN(maxValue)) {
            columnWidth = Math.max((int) Math.ceil(Math.log10(maxValue)) + 2 + (nonInteger ? 3 : 0), columnWidth);
        }

        sb.append(String.format("%% %" + ((21 + 3 * columnWidth) / 2) + "s\n", "Actual"));
        sb.append(String.format("%% %9s%" + columnWidth + "s%" + columnWidth + "s%" + columnWidth + "s\n", "", "Pos", "Neg", "Total"));
        final String format = "%% %9s%" + columnWidth + (nonInteger ? ".2" : ".0") + "f%" + columnWidth + (nonInteger ? ".2" : ".0") +
                "f%" + columnWidth + (nonInteger ? ".2" : ".0") + "f\n";
        sb.append(String.format(format, "Model Pos", truePositives, falsePositives, truePositives + falsePositives));
        sb.append(String.format(format, "Neg", falseNegatives, trueNegatives, falseNegatives + trueNegatives));
        sb.append(String.format("%% %9s%" + columnWidth + (nonInteger ? ".2" : ".0") + "f%" + columnWidth + (nonInteger ? ".2" : ".0") +
                "f\n", "Total", truePositives + falseNegatives, falsePositives + trueNegatives));

        sb.append("\n");

        sb.append(String.format("%% Accuracy  = %.4f\n", getAccuracy()));
        sb.append(String.format("%% Precision = %.4f\n", getPrecision()));
        sb.append(String.format("%% Recall    = %.4f\n", getRecall()));
        sb.append(String.format("%% F(1)      = %.4f",   getF1()));

        return sb.toString();
    }

    @Override
    public String toString() {
        return toLongString();
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
