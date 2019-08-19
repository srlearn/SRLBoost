package edu.wisc.cs.will.ILP;

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


}
