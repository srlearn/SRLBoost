package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.MapOfLists;

/**
 * @author twalker
 */
public interface RelevantInformation {
    Example getExample();
    RelevanceStrength getRelevanceStrength();
    boolean isRelevanceFromPositiveExample();
    void setRelevanceFromPositiveExample(boolean positive);

    boolean isEquivalentUptoVariableRenaming(RelevantInformation info);
    RelevantInformation getGeneralizeRelevantInformation();

    boolean prove(HornClauseContext context);

    String toString(String prefix);

    RelevantInformation copy();

    boolean isValidAdvice(AdviceProcessor ap);

    boolean subsumes(RelevantInformation that);

    /**
     * Returns a simplified version of the relevant information.
     */
    RelevantInformation getSimplified(HornClauseContext context, MapOfLists<PredicateNameAndArity, Clause> supportClauses);
}
