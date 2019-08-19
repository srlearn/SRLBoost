package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.RelevanceStrength;

/*
 * @author twalker
 */
public interface RelevantInformation {
    Example getExample();
    RelevanceStrength getRelevanceStrength();
    boolean isRelevanceFromPositiveExample();
    void setRelevanceFromPositiveExample(boolean positive);

    boolean isEquivalentUptoVariableRenaming(RelevantInformation info);
    RelevantInformation getGeneralizeRelevantInformation();

    String toString(String prefix);

    RelevantInformation copy();

    boolean isValidAdvice(AdviceProcessor ap);

    boolean subsumes(RelevantInformation that);

}
