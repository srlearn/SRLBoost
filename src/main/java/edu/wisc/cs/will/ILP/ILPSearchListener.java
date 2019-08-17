package edu.wisc.cs.will.ILP;

import java.util.EventListener;

/**
 *
 * @author twalker
 */
public interface ILPSearchListener extends EventListener {

    ILPSearchAction onionLayerStarting(TuneParametersForILP onion, ILPparameterSettings onionLayer);
    void onionLayerFinished(TuneParametersForILP onion, ILPparameterSettings onionLayer);

    ILPSearchAction crossValidationFoldStarting(ILPCrossValidationLoop cvLoop, int fold);
    void crossValidationFoldFinished(ILPCrossValidationLoop cvLoop, int fold);

    ILPSearchAction outerLoopStarting(ILPouterLoop outerLoop);
    void outerLoopFinished(ILPouterLoop outerLoop);

    ILPSearchAction innerLoopStarting(LearnOneClause learnOneClause);
    void innerLoopFinished(LearnOneClause learnOneClause);
}
