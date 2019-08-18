package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.Utils.Utils;
import java.util.Comparator;

/*
 * @author twalker
 */
public class CrossValidationResult {

    private CoverageScore averageTrainingCoverageScore;
    private CoverageScore averageEvaluationCoverageScore;

    private int numberOfFolds;

    private CrossValidationFoldResult[] foldResults;

    CrossValidationResult(int numberOfFolds) {
        this.numberOfFolds = numberOfFolds;
        foldResults = new CrossValidationFoldResult[numberOfFolds];
    }

    CrossValidationFoldResult getFoldResult(int fold) {
        return foldResults[fold];
    }

    void setFoldResult(int fold, CrossValidationFoldResult foldResult) {
        foldResults[fold] = foldResult;

        invalidateCoverageScores();
    }

    private void invalidateCoverageScores() {
        setAverageEvaluationCoverageScore();
        setAverageTrainingCoverageScore();
    }

    CoverageScore getAverageTrainingCoverageScore() {
        calculateAverageTrainingCoverageScore();

        return averageTrainingCoverageScore;
    }

    private void setAverageTrainingCoverageScore() {
        this.averageTrainingCoverageScore = null;
    }

    CoverageScore getAverageEvaluationCoverageScore() {
        calculateAverageEvaluationCoverageScore();

        return averageEvaluationCoverageScore;
    }

    private void setAverageEvaluationCoverageScore() {
        this.averageEvaluationCoverageScore = null;
    }

    private void calculateAverageTrainingCoverageScore() {
        if (averageTrainingCoverageScore == null) {
            double tp = 0;
            double tn = 0;
            double fp = 0;
            double fn = 0;

            double fnMEst = 0;
            double fpMEst = 0;

            int foldCount = 0;

            for (CrossValidationFoldResult foldResult : foldResults) {
                if (foldResult != null) {
                    foldCount++;

                    CoverageScore score = foldResult.getTrainingCoverageScore();

                    if (score != null) {
                        tp += score.getTruePositives();
                        tn += score.getTrueNegatives();
                        fp += score.getFalsePositives();
                        fn += score.getFalseNegatives();

                        fnMEst += score.getFalseNegativeMEstimate();
                        fpMEst += score.getFalsePositiveMEstimate();
                    }
                }
            }

            averageTrainingCoverageScore = new CoverageScore(tp/foldCount, fp/foldCount, tn/foldCount, fn/foldCount, fnMEst/foldCount, fpMEst/foldCount);
        }
    }

    private void calculateAverageEvaluationCoverageScore() {
        if (averageEvaluationCoverageScore == null) {
            double tp = 0;
            double tn = 0;
            double fp = 0;
            double fn = 0;

            double fnMEst = 0;
            double fpMEst = 0;

            int foldCount = 0;

            for (CrossValidationFoldResult foldResult : foldResults) {
                if (foldResult != null) {


                    CoverageScore score = foldResult.getEvaluationCoverageScore();

                    if (score != null) {
                        foldCount++;
                        tp += score.getTruePositives();
                        tn += score.getTrueNegatives();
                        fp += score.getFalsePositives();
                        fn += score.getFalseNegatives();

                        fnMEst += score.getFalseNegativeMEstimate();
                        fpMEst += score.getFalsePositiveMEstimate();
                    }
                }
            }

            if ( foldCount > 0 ) {
                averageEvaluationCoverageScore = new CoverageScore(tp/foldCount, fp/foldCount, tn/foldCount, fn/foldCount, fnMEst/foldCount, fpMEst/foldCount);
            }
        }
    }

    private double getAverageTrainingAccuracy() {
        CoverageScore score = getAverageTrainingCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
        else {
            return score.getAccuracy();
        }
    }

    double getAverageTestingAccuracy() {
        CoverageScore score = getAverageEvaluationCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
        else {
            return score.getAccuracy();
        }
    }

    double getAverageAccuracy() {
        double v = getAverageTestingAccuracy();

        if (Double.isNaN(v)) {
            v = getAverageTrainingAccuracy();
        }

        return v;
    }

    double getAverageTrainingPrecision() {
        CoverageScore score = getAverageTrainingCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
        else {
            return score.getPrecision();
        }
    }

    double getAverageTestingPrecision() {
        CoverageScore score = getAverageEvaluationCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
        else {
            return score.getPrecision();
        }
    }

    double getAverageTrainingRecall() {
        CoverageScore score = getAverageTrainingCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
        else {
            return score.getRecall();
        }
    }

    double getAverageTestingRecall() {
        CoverageScore score = getAverageEvaluationCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
        else {
            return score.getRecall();
        }
    }

    double getAverageTestingFBeta() {
    	return getAverageTestingFBeta(1.0); 
    }
    private double getAverageTestingFBeta(double beta) {
        CoverageScore score = getAverageEvaluationCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
		return score.getFBeta(beta);
    }

    double getAverageFBeta() {
    	return getAverageFBeta(1.0); 
    }
    private double getAverageFBeta(double beta) {
        CoverageScore score = getAverageEvaluationCoverageScore();

        if (score == null) {
            score = getAverageTrainingCoverageScore();
        }

        if ( score == null ) {
            return Double.NaN;
        }
		return score.getFBeta(beta);
    }

    private int getNumberOfFolds() {
        return numberOfFolds;
    }

    
    private String toShortString() {
        StringBuilder sb = new StringBuilder();

        CoverageScore cs;

        sb.append("% Folds = ").append(getNumberOfFolds());

        cs = getAverageTrainingCoverageScore();
        if ( cs != null ) {
            sb.append(", Train: ").append(cs.toShortString());
        }
        cs = getAverageEvaluationCoverageScore();
        if ( cs != null ) {
            sb.append(", Test: ").append(cs.toShortString());
        }
        return sb.toString();
    }

    @Override
    public String toString() {
        return toShortString();
    }

    /* Returns the FoldResults with the best Accuracy across all examples.
     *
     * The coverage score used to compare the fold results is based upon all
     * of the examples in the positive and negative sets.  If you would like
     * to get the best overall, you can pass a more specific comparator into
     * the getBestOrverallFold(Comparator&ltILPCVFoldResult&gt foldComparator)
     * method.
     *
     * @return FoldResults with the best Accuracy across all examples.
     */
    CrossValidationFoldResult getBestOverallFoldByAccuracy() {
        return getBestOverallFold(CoverageScore.ascendingAccuracyComparator);
    }

    CrossValidationFoldResult getBestOverallFoldByF1() {
        return getBestOverallFold(CoverageScore.ascendingF1Comparator);
    }
    
    /* Returns the best FoldResults across all examples as determined by the comparator.
     *
     * The comparator must be a CoverageScore comparator.  The CoverageScore
     * class many of the common comparison, such as accuracy, precision, etc.
     *
     * The coverage score used to compare the fold results is based upon all
     * of the examples in the positive and negative sets.  If you would like
     * to get the best overall, you can pass a more specific comparator into
     * the getBestOrverallFold(Comparator&ltILPCVFoldResult&gt foldComparator)
     * method.
     *
     * @param coverageScoreComparator CoverageScore comparator used to order the
     * fold results.  The coverage score compared is based upon all examples,
     * not just the evaluation test.
     * 
     * @return FoldResults with the best coverage score across all examples as determined by the comparator.
     */
    private CrossValidationFoldResult getBestOverallFold(final Comparator<CoverageScore> coverageScoreComparator) {

        Comparator<CrossValidationFoldResult> foldComparator = (o1, o2) -> coverageScoreComparator.compare(o1.getAllExamplesCoverageScore(), o2.getAllExamplesCoverageScore());

        return getBestOrverallFold(foldComparator);
    }

    /* Returns the best FoldResults as determined by the comparator.
     *
     * This method allows for maximum configurability with regards to how to
     * compare folds.  See getBestOverallFoldByAccuracy() and
     * getBestOverallFold(final Comparator<CoverageScore> coverageScoreComparator)
     * for simplier calling patterns.
     *
     * @param foldComparator Comparator used to order the fold results.
     * @return FoldResults with the best score as determined by the comparator.
     */
    private CrossValidationFoldResult getBestOrverallFold(Comparator<CrossValidationFoldResult> foldComparator) {

        return Utils.argmax(foldComparator, foldResults);
    }



}
