package edu.wisc.cs.will.ILP;

import java.util.EventListener;

/*
 * @author twalker
 */
interface ILPSearchListener extends EventListener {

    ILPSearchAction outerLoopStarting(ILPouterLoop outerLoop);
    void outerLoopFinished(ILPouterLoop outerLoop);

    ILPSearchAction innerLoopStarting(LearnOneClause learnOneClause);
    void innerLoopFinished(LearnOneClause learnOneClause);
}
