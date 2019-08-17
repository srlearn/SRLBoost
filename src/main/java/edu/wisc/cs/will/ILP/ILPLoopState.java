package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import java.util.List;

/**
 *
 * @author twalker
 */
public interface ILPLoopState {

    List<Example> getPositiveExamples();

    ILPLoopState copy();
}
