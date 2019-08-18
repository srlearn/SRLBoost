package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import java.io.Serializable;

/* Provides a stopping condition for cross-validation based upon the maximum obtainable average coverage score on a partially completely cross-validation run.
 *
 * The maximum obtainable average coverage score is calculated by taking the average of
 * the scores of all the completed folds along with a maximum perfect score for
 * all uncompleted folds.
 *
 * From the coverage score, the maximum obtainable average precision and recall
 * can be calculated.  If either one of these values do not meet the stopping
 * conditions, cross-validation will be halted.
 *
 * Note, if either stopping condition cannot be met, the search will be stopped.
 *
 * @author twalker
 */
public class CVMaximumObtainableAverageCoverageStoppingCondition implements StoppingCondition<ILPCrossValidationLoop>, Serializable {

    private double stopIfPrecisionCannotMeetOrExceedThis;

    private double stopIfRecallCannotMeetOrExceedThis;

    private double stopIfAccuracyCannotMeetOrExceedThis;

    private double stopIfFScoreCannotMeetOrExceedThis;

    private double beta;


    CVMaximumObtainableAverageCoverageStoppingCondition(double stopIfPrecisionCannotMeetOrExceedThis, double stopIfRecallCannotMeetOrExceedThis) {
        this(stopIfPrecisionCannotMeetOrExceedThis,stopIfRecallCannotMeetOrExceedThis,0,0,1);
    }

    private CVMaximumObtainableAverageCoverageStoppingCondition(double stopIfPrecisionCannotMeetOrExceedThis, double stopIfRecallCannotMeetOrExceedThis, double stopIfAccuracyCannotMeetOrExceedThis, double stopIfFScoreCannotMeetOrExceedThis, double beta) {
        this.stopIfPrecisionCannotMeetOrExceedThis = stopIfPrecisionCannotMeetOrExceedThis;
        this.stopIfRecallCannotMeetOrExceedThis    = stopIfRecallCannotMeetOrExceedThis;
        this.stopIfAccuracyCannotMeetOrExceedThis  = stopIfAccuracyCannotMeetOrExceedThis;
        this.stopIfFScoreCannotMeetOrExceedThis    = stopIfFScoreCannotMeetOrExceedThis;
        this.beta = beta;
    }

    public boolean isStoppingConditionMet(ILPCrossValidationLoop search) {
        CrossValidationResult result = search.getCrossValidationResults();

        CrossValidationExampleSets exampleSets = search.getILPCrossValidationExampleSets();

        double tp = 0;
        double tn = 0;
        double fp = 0;
        double fn = 0;

        ILPouterLoop outerLoop = search.getOuterLoop();

        int n = exampleSets.getNumberOfFolds();

        boolean useEvalSet = (exampleSets.getPositiveEvaluationExamplesForFold(0) != null && !exampleSets.getPositiveEvaluationExamplesForFold(0).isEmpty());

        for(int i = 0; i < n; i++) {
            CrossValidationFoldResult foldResult = result.getFoldResult(i);

            if ( useEvalSet ) {
                CoverageScore cs;
                if ( foldResult != null && (cs = foldResult.getEvaluationCoverageScore()) != null) {
                    tp += cs.getTruePositives();
                    tn += cs.getTrueNegatives();
                    fp += cs.getFalsePositives();
                    fn += cs.getFalseNegatives();

                }
                else {
                    // We don't have any results for this fold, so just assume we got everything
                    // correct (sans the mEstimates which we will consider later).
                    tp += Example.getWeightOfExamples( exampleSets.getPositiveEvaluationExamplesForFold(i));
                    tn += Example.getWeightOfExamples( exampleSets.getNegativeEvaluationExamplesForFold(i));
                }
            }
            else {
                CoverageScore cs;
                if ( foldResult != null && (cs = foldResult.getTrainingCoverageScore()) != null) {
                    tp += cs.getTruePositives();
                    tn += cs.getTrueNegatives();
                    fp += cs.getFalsePositives();
                    fn += cs.getFalseNegatives();

                }
                else {
                    // We don't have any results for this fold, so just assume we got everything
                    // correct (sans the mEstimates which we will consider later).
                    tp += Example.getWeightOfExamples( exampleSets.getPositiveTrainingExamplesForFold(i));
                    tn += Example.getWeightOfExamples( exampleSets.getNegativeTrainingExamplesForFold(i));
                }
            }
        }

        CoverageScore maximumObtainableAverageCoverage = new CoverageScore(tp/n, fp/n, tn/n, fn/n, outerLoop.innerLoopTask.getMEstimatePos(), outerLoop.innerLoopTask.getMEstimateNeg());

        return ( maximumObtainableAverageCoverage.getPrecision() < getStopIfPrecisionCannotMeetOrExceedThis() || 
                 maximumObtainableAverageCoverage.getRecall()    < getStopIfRecallCannotMeetOrExceedThis()    ||
                 maximumObtainableAverageCoverage.getFBeta(beta) < getStopIfFScoreCannotMeetOrExceedThis()    ||
                 maximumObtainableAverageCoverage.getAccuracy()  < getStopIfAccuracyCannotMeetOrExceedThis() );
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final CVMaximumObtainableAverageCoverageStoppingCondition other = (CVMaximumObtainableAverageCoverageStoppingCondition) obj;
        if (this.stopIfPrecisionCannotMeetOrExceedThis != other.stopIfPrecisionCannotMeetOrExceedThis) {
            return false;
        }
        if (this.stopIfRecallCannotMeetOrExceedThis    != other.stopIfRecallCannotMeetOrExceedThis) {
            return false;
        }
        if (this.stopIfAccuracyCannotMeetOrExceedThis  != other.stopIfAccuracyCannotMeetOrExceedThis) {
            return false;
        }
        if (this.stopIfFScoreCannotMeetOrExceedThis    != other.stopIfFScoreCannotMeetOrExceedThis) {
            return false;
        }
        return this.beta == other.beta;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 59 * hash + (int) (Double.doubleToLongBits(this.stopIfPrecisionCannotMeetOrExceedThis) ^ (Double.doubleToLongBits(this.stopIfPrecisionCannotMeetOrExceedThis) >>> 32));
        hash = 59 * hash + (int) (Double.doubleToLongBits(this.stopIfRecallCannotMeetOrExceedThis)    ^ (Double.doubleToLongBits(this.stopIfRecallCannotMeetOrExceedThis)    >>> 32));
        hash = 59 * hash + (int) (Double.doubleToLongBits(this.stopIfAccuracyCannotMeetOrExceedThis)  ^ (Double.doubleToLongBits(this.stopIfAccuracyCannotMeetOrExceedThis)  >>> 32));
        hash = 59 * hash + (int) (Double.doubleToLongBits(this.stopIfFScoreCannotMeetOrExceedThis)    ^ (Double.doubleToLongBits(this.stopIfFScoreCannotMeetOrExceedThis)    >>> 32));
        hash = 59 * hash + (int) (Double.doubleToLongBits(this.beta) ^ (Double.doubleToLongBits(this.beta) >>> 32));
        return hash;
    }

    private double getStopIfPrecisionCannotMeetOrExceedThis() {
        return stopIfPrecisionCannotMeetOrExceedThis;
    }

    private double getStopIfRecallCannotMeetOrExceedThis() {
        return stopIfRecallCannotMeetOrExceedThis;
    }

    private double getStopIfFScoreCannotMeetOrExceedThis() {
        return stopIfFScoreCannotMeetOrExceedThis;
    }

    private double getStopIfAccuracyCannotMeetOrExceedThis() {
        return stopIfAccuracyCannotMeetOrExceedThis;
    }
}
