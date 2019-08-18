package edu.wisc.cs.will.ILP;

import java.io.Serializable;
import java.util.Comparator;

import edu.wisc.cs.will.Utils.Utils;

/*
 * @author twalker
 */
public class CoverageScore implements Serializable {

    final static Comparator<CoverageScore> ascendingAccuracyComparator = new AccuracyComparator(true);
    final static Comparator<CoverageScore> ascendingF1Comparator = new F1Comparator(true);

    private double truePositives  = 0;
    private double falsePositives = 0;
    private double trueNegatives  = 0;
    private double falseNegatives = 0;
    private double falseNegativeMEstimate = 0;
    private double truePositiveMEstimate  = 0;
    private double falsePositiveMEstimate = 0;
    private double trueNegativeMEstimate  = 0;

    /* Creates a new instance of CoverageScore */
    public CoverageScore() {
    }

    /* Creates a new instance of CoverageScore.
     *
     * @param tp True Positives (possibly weighted).
     * @param fp False Positives (possibly weighted).
     * @param tn True Negatives (possibly weighted).
     * @param fn False Negatives (possibly weighted).
     * @param falseNegativeMEstimate False negative mEstimate used when calculating precision/recall/F score.
     * @param falsePositiveMEstimate False positive mEstimate used when calculating precision/recall/F score.
     */
    CoverageScore(double tp, double fp, double tn, double fn, double falseNegativeMEstimate, double falsePositiveMEstimate) {
        setCounts(tp, fp, tn, fn);
        this.falseNegativeMEstimate = falseNegativeMEstimate;
        this.falsePositiveMEstimate = falsePositiveMEstimate;
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

    public double getAccuracy() {
        return Utils.getAccuracy(truePositives + truePositiveMEstimate, falsePositives + falsePositiveMEstimate, trueNegatives + trueNegativeMEstimate, falseNegatives + falseNegativeMEstimate);
    }

    public double getF1() {
        return Utils.getF1(truePositives + truePositiveMEstimate, falsePositives + falsePositiveMEstimate, falseNegatives + falseNegativeMEstimate);
    }

    double getFBeta(double beta) {
        return Utils.getFBeta(beta, truePositives + trueNegativeMEstimate, falsePositives + falsePositiveMEstimate, falseNegatives + falseNegativeMEstimate);
    }

    String toShortString() {
        boolean nonInteger = (trueNegatives != Math.floor(trueNegatives) || truePositives != Math.floor(truePositives) || falseNegatives != Math.floor(falseNegatives) || falsePositives != Math.floor(falsePositives));

        if (nonInteger) {
            return String.format("%% [TP=%.2f, FP=%.2f, TN=%.2f, FN=%.2f, A=%.2f, P=%.2f, R=%.2f, F1=%.2f]", truePositives, falsePositives, trueNegatives, falseNegatives, getAccuracy(), getPrecision(), getRecall(), getF1());
        } else {
            return String.format("%% [TP=%d, FP=%d, TN=%d, FN=%d, A=%.2f, P=%.2f, R=%.2f, F1=%.2f]", (int) truePositives, (int) falsePositives, (int) trueNegatives, (int) falseNegatives, getAccuracy(), getPrecision(), getRecall(), getF1());
        }
    }

    String toLongString() {
        StringBuilder sb = new StringBuilder();

        double maxValue = Utils.max(trueNegatives, truePositives, falseNegatives, falsePositives);


        int columnWidth = 6;

        boolean nonInteger = (trueNegatives != Math.floor(trueNegatives) || truePositives != Math.floor(truePositives) || falseNegatives != Math.floor(falseNegatives) || falsePositives != Math.floor(falsePositives));

        if (maxValue > 0 && !Double.isInfinite(maxValue) && !Double.isNaN(maxValue)) {
            columnWidth = Math.max((int) Math.ceil(Math.log10(maxValue)) + 2 + (nonInteger ? 3 : 0), columnWidth);
        }

        sb.append(String.format("%% %" + ((21 + 3 * columnWidth) / 2) + "s\n", "Actual"));
        sb.append(String.format("%% %9s%" + columnWidth + "s%" + columnWidth + "s%" + columnWidth + "s\n", "", "Pos", "Neg", "Total"));
        sb.append(String.format("%% %9s%" + columnWidth + (nonInteger ? ".2" : ".0") + "f%" + columnWidth + (nonInteger ? ".2" : ".0") +
                "f%" + columnWidth + (nonInteger ? ".2" : ".0") + "f\n", "Model Pos", truePositives, falsePositives, truePositives + falsePositives));
        sb.append(String.format("%% %9s%" + columnWidth + (nonInteger ? ".2" : ".0") + "f%" + columnWidth + (nonInteger ? ".2" : ".0") +
                "f%" + columnWidth + (nonInteger ? ".2" : ".0") + "f\n", "Neg", falseNegatives, trueNegatives, falseNegatives + trueNegatives));
        sb.append(String.format("%% %9s%" + columnWidth + (nonInteger ? ".2" : ".0") + "f%" + columnWidth + (nonInteger ? ".2" : ".0") +
                "f\n", "Total", truePositives + falseNegatives, falsePositives + trueNegatives));

        if (falseNegativeMEstimate != 0 || truePositiveMEstimate != 0 || falsePositiveMEstimate != 0 || trueNegativeMEstimate != 0) {
            sb.append("\n");
            if (truePositiveMEstimate != 0) {
                sb.append(String.format("%% True  Pos mEst  = %.4f\n", truePositiveMEstimate));
            }
            if (falsePositiveMEstimate != 0) {
                sb.append(String.format("%% False Pos mEst  = %.4f\n", falsePositiveMEstimate));
            }
            if (trueNegativeMEstimate != 0) {
                sb.append(String.format("%% True  Neg mEst  = %.4f\n", trueNegativeMEstimate));
            }
            if (falseNegativeMEstimate != 0) {
                sb.append(String.format("%% False Neg mEst  = %.4f\n", falseNegativeMEstimate));
            }
        }

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

    double getFalsePositiveMEstimate() {
        return falsePositiveMEstimate;
    }

    void setFalsePositiveMEstimate(double falsePositiveMEstimate) {
        this.falsePositiveMEstimate = falsePositiveMEstimate;
    }

    double getFalseNegativeMEstimate() {
        return falseNegativeMEstimate;
    }

    void setFalseNegativeMEstimate(double falseNegativeMEstimate) {
        this.falseNegativeMEstimate = falseNegativeMEstimate;
    }

    public static class AccuracyComparator implements Comparator<CoverageScore> {
        private int ascending = 1;

        AccuracyComparator(boolean ascending) {
            this.ascending = ascending ? 1 : -1;
        }

        public int compare(CoverageScore o1, CoverageScore o2) {
            double v1 = o1.getAccuracy();
            double v2 = o2.getAccuracy();

            if ( Double.isNaN(v1) && !Double.isNaN(v2)) {
                return -1 * ascending;
            }
            else if (!Double.isNaN(v1) && Double.isNaN(v2) ) {
                return ascending;
            }
            if ( Double.isNaN(v1) && Double.isNaN(v2) ) {
                return 0;
            }
            else {
                return (int)Math.signum(v1-v2) * ascending;
            }
        }
    }

    public static class FBetaComparator implements Comparator<CoverageScore> {
        private int ascending;
        private double beta;

        FBetaComparator(double beta, boolean ascending) {
            this.beta = beta;
            this.ascending = ascending ? 1 : -1;
        }

        public int compare(CoverageScore o1, CoverageScore o2) {
            double v1 = o1.getFBeta(beta);
            double v2 = o2.getFBeta(beta);

            if ( Double.isNaN(v1) && !Double.isNaN(v2)) {
                return -1 * ascending;
            }
            else if (!Double.isNaN(v1) && Double.isNaN(v2) ) {
                return ascending;
            }
            if ( Double.isNaN(v1) && Double.isNaN(v2) ) {
                return 0;
            }
            else {
                return (int)Math.signum(v1-v2) * ascending;
            }
        }
    }

    public static class F1Comparator extends FBetaComparator {

        F1Comparator(boolean ascending) {
            super(1, ascending);
        }
    }
}
