package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;
import java.util.List;
import java.util.Objects;

/*
 * @author twalker
 */
class CrossValidationLoopState implements Serializable {

    private ILPouterLoopState outerLoopState;

    private int numberOfFolds = -1; // Initialize to illegal value so we know it has been set.

    private CrossValidationExampleSets ilpCrossValidationExampleSets;

    private StoppingCondition<ILPCrossValidationLoop> earlyStoppingCondition = null;

    private long maximumCrossValidationTimeInMillisec = Long.MAX_VALUE;

    /* Stores the flipFlip examples values.
     *
     * This is also stored in the ilpCrossValidationExampleSets.  However, since that
     * may be null when this is set, we store a copy of the value here.
     *
     * If this value is null, then it passes through to the ilpCrossValidationExampleSets
     * to get the actual value.  The only time this shouldn't be null is when there isn't
     * an examples set set current.
     */
    private Boolean flipFlopValueHolder = null;

    /* Creates a CrossValidationLoopState with the given outerLoopState, numberOfFolds and example collection.
     *
     * If the example collection is non-null, it is assumed that the examples and fold data are already
     * setup.
     */
    CrossValidationLoopState(ILPouterLoopState outerLoopState, int numberOfFolds, CrossValidationExampleSets ilpCrossValidationExampleSets) {
        this.outerLoopState = outerLoopState.clone();
        setNumberOfFolds(numberOfFolds);
        setILPCrossValidationExampleSets(ilpCrossValidationExampleSets);
    }

    /* Checks to make sure that the two state objects belong to the same search.
     *
     * When loading checkpoint information, we need to make sure that the state
     * information saved to disk belongs to the same ILP run as the one currently
     * being performed.
     *
     * If this method throws an IncongruentSavedStateException, this state is probably
     * from a different search.
     *
     * This code resembled equals code and performs approximately the same function.
     * However, I renamed it to make it explicit what it is doing.
     */
    void checkStateCongruency(CrossValidationLoopState savedCVState) throws IncongruentSavedStateException {

        // Check that the number of folds was the same...
        if (numberOfFolds != savedCVState.numberOfFolds) {
            throw new IncongruentSavedStateException("Saved cross-validation state configured with incorrect number of folds. " +
                    "Expected = " + numberOfFolds + ".  Found = " + savedCVState.numberOfFolds + ".");
        }
        
        // For now just check that the other loop is consistent...
        getOuterLoopState().checkStateCongruency(savedCVState.outerLoopState);

        if ( getILPCrossValidationExampleSets() != null && savedCVState.getILPCrossValidationExampleSets() != null) {
            getILPCrossValidationExampleSets().checkStateCongruency(savedCVState.getILPCrossValidationExampleSets());
        }

        if (!Objects.equals(earlyStoppingCondition, savedCVState.earlyStoppingCondition)) {
            throw new IncongruentSavedStateException("Saved cross-validation early stopping criteria does not matter configured.  (Make sure your early stopping criteria class implements equals() correctly.");
        }
    }

    /* Creates an ILPouterLoop object which can be used to run a single fold.
     *
     * This object is just a copy of the CrossValidation outerloop with the
     * positiveitive and Negativeative examples set appropriately for this fold.
     */
    ILPouterLoopState getILPOuterLoopStateForFold(int fold) {
        ILPouterLoopState newState = outerLoopState.clone();
        newState.setCurrentFold(fold);

        return newState;
    }

    private ILPouterLoopState getOuterLoopState() {
        return outerLoopState;
    }

    int getNumberOfFolds() {
        return numberOfFolds;
    }

    private void setNumberOfFolds(int numberOfFolds) {

        if ( numberOfFolds <= 0 ) {
            throw new IllegalArgumentException("Number of folds must be >= 1.");
        }

        if (numberOfFolds != this.numberOfFolds) {
            if (this.numberOfFolds != -1) {
                throw new IllegalStateException("The number of folds has already been set.  Once set, it cannot be changed.");
            }

            this.numberOfFolds = numberOfFolds;
        }
    }

    CrossValidationExampleSets getILPCrossValidationExampleSets() {
        return ilpCrossValidationExampleSets;
    }

    final void setILPCrossValidationExampleSets(CrossValidationExampleSets ilpCrossValidationExamples) {
        if (this.ilpCrossValidationExampleSets != ilpCrossValidationExamples) {

            if ( ilpCrossValidationExamples != null && ilpCrossValidationExamples.getNumberOfFolds() != numberOfFolds ) {
                throw new IllegalArgumentException("The CV examples sets must have the same number of folds as the Cross Validation loop.  " +
                        "CVLoop folds = " + getNumberOfFolds() + ".  Collection folds = " + ilpCrossValidationExamples.getNumberOfFolds() + "." );
            }

            this.ilpCrossValidationExampleSets = ilpCrossValidationExamples;

            if ( this.ilpCrossValidationExampleSets != null &&  flipFlopValueHolder != null ) {
                this.ilpCrossValidationExampleSets.setFlipFlopPositiveitiveAndNegativeativeExamples(flipFlopValueHolder);

                flipFlopValueHolder = null;
            }
            
        }
    }

    List<Example> getPositiveTrainingExamplesForFolds(int fold) {

        if ( ilpCrossValidationExampleSets == null ) throw new IllegalStateException("The cross-validation example sets have not been set.");

        return ilpCrossValidationExampleSets.getPositiveTrainingExamplesForFold(fold);
    }


    List<Example> getPositiveEvaluationExamplesForFolds(int fold) {

        if ( ilpCrossValidationExampleSets == null ) throw new IllegalStateException("The cross-validation example sets have not been set.");

        return ilpCrossValidationExampleSets.getPositiveEvaluationExamplesForFold(fold);
    }

    List<Example> getNegativeTrainingExamplesForFolds(int fold) {

        if ( ilpCrossValidationExampleSets == null ) throw new IllegalStateException("The cross-validation example sets have not been set.");

        return ilpCrossValidationExampleSets.getNegativeTrainingExamplesForFold(fold);
    }

    List<Example> getNegativeEvaluationExamplesForFolds(int fold) {

        if ( ilpCrossValidationExampleSets == null ) throw new IllegalStateException("The cross-validation example sets have not been set.");

        return ilpCrossValidationExampleSets.getNegativeEvaluationExamplesForFold(fold);
    }

    List<Example> getAllPositiveExamples() {

        if ( ilpCrossValidationExampleSets == null ) throw new IllegalStateException("The cross-validation example sets have not been set.");

        return ilpCrossValidationExampleSets.getAllPositiveExamples();
    }

    List<Example> getAllNegativeExamples() {

        if ( ilpCrossValidationExampleSets == null ) throw new IllegalStateException("The cross-validation example sets have not been set.");

        return ilpCrossValidationExampleSets.getAllNegativeExamples();
    }

    StoppingCondition<ILPCrossValidationLoop> getEarlyStoppingCondition() {
        return earlyStoppingCondition;
    }

    void setEarlyStoppingCondition(StoppingCondition<ILPCrossValidationLoop> earlyStoppingCondition) {
        this.earlyStoppingCondition = earlyStoppingCondition;
    }

    boolean getFlipFlopPositiveitiveAndNegativeativeExamples() {
        if (flipFlopValueHolder == null) {
            if ( ilpCrossValidationExampleSets != null ) {
                return ilpCrossValidationExampleSets.getFlipFlopPositiveitiveAndNegativeativeExamples();
            }
            else {
                return false;
            }
        }
        else {
            return flipFlopValueHolder;
        }
    }

    void setFlipFlopPositiveitiveAndNegativeativeExamples(boolean flipFlopPositiveitiveAndNegativeativeExamples) {

        if ( this.flipFlopValueHolder == null || this.flipFlopValueHolder != flipFlopPositiveitiveAndNegativeativeExamples ) {
            if ( this.ilpCrossValidationExampleSets != null ) {
                this.ilpCrossValidationExampleSets.setFlipFlopPositiveitiveAndNegativeativeExamples(flipFlopPositiveitiveAndNegativeativeExamples);

            	this.flipFlopValueHolder = null;
            }
            else {
            	this.flipFlopValueHolder = flipFlopPositiveitiveAndNegativeativeExamples;
            }
            
        }
        outerLoopState.setFlipFlopPosAndNegExamples(flipFlopPositiveitiveAndNegativeativeExamples); // Add by JWS 12/8/09.
    }

    long getMaximumCrossValidationTimeInMillisec() {
        return maximumCrossValidationTimeInMillisec;
    }

    void setMaximumCrossValidationTimeInMillisec(long maximumCrossValidationTimeInMillisec) {
    	if (maximumCrossValidationTimeInMillisec < 0) { Utils.waitHere("Should not have a Negativeative value: setMaximumCrossValidationTimeInMillisec = " + maximumCrossValidationTimeInMillisec); }
        this.maximumCrossValidationTimeInMillisec = Math.max(0, maximumCrossValidationTimeInMillisec);
    }


}
