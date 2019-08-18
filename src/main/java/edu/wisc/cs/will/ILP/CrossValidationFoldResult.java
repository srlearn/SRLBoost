package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.Theory;
import java.io.Serializable;

/*
 * @author twalker
 */
public class CrossValidationFoldResult implements Serializable {
    private int     fold;
    private Theory  theory;
    private Gleaner gleaner;

    private CoverageScore trainingCoverageScore    = null;
    private CoverageScore evaluationCoverageScore  = null;
    private CoverageScore allExamplesCoverageScore = null;

    CrossValidationFoldResult(int fold, Theory theory, Gleaner gleaner) {
        this.fold = fold;
        this.theory = theory;
        this.gleaner = gleaner;
    }

    public Gleaner getGleaner() {
        return gleaner;
    }

    public void setGleaner(Gleaner gleaner) {
        this.gleaner = gleaner;
    }

    public Theory getTheory() {
        return theory;
    }

    public void setTheory(Theory theory) {
        if (this.theory != theory) {

            this.theory = theory;

            invalidateCoverageScores();
        }
    }

    private void invalidateCoverageScores() {
        trainingCoverageScore = null;
        evaluationCoverageScore = null;
    }

    public int getFold() {
        return fold;
    }

    public void setFold(int fold) {
        this.fold = fold;
    }

    CoverageScore getTrainingCoverageScore() {

        return trainingCoverageScore;
    }

    void setTrainingCoverageScore(CoverageScore trainingCoverageScore) {
        this.trainingCoverageScore = trainingCoverageScore;
    }

    CoverageScore getEvaluationCoverageScore() {
        return evaluationCoverageScore;
    }

    void setEvaluationCoverageScore(CoverageScore evaluationCoverageScore) {
        this.evaluationCoverageScore = evaluationCoverageScore;
    }

    CoverageScore getAllExamplesCoverageScore() {
        return allExamplesCoverageScore;
    }

    void setAllExamplesCoverageScore(CoverageScore allExamplesCoverageScore) {
        this.allExamplesCoverageScore = allExamplesCoverageScore;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        CoverageScore cs;

        sb.append("Cross-Validation Fold Result (Fold #").append(getFold()).append("):\n\n");

        sb.append(getTheory().toString()).append("\n");

        cs = getTrainingCoverageScore();
        if ( cs != null ) {
            sb.append("\n%%% TRAINING-SET Coverage Score:\n").append(cs.toLongString()).append("\n");
        }
        cs = getEvaluationCoverageScore();
        if ( cs != null ) {
            sb.append("\n%%% EVALUATION-SET Coverage Score:\n").append(cs.toLongString()).append("\n");
        }

        cs = getAllExamplesCoverageScore();
        if ( cs != null ) {
            sb.append("\n%%% All Examples Coverage Score:\n").append(cs.toLongString()).append("\n");
        }

        return sb.toString();
    }

}
