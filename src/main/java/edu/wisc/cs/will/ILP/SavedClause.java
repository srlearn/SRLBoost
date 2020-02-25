package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;
import java.util.Set;

/*
 * @author shavlik
 *
 *  An entry in a Gleaner.
 */
class SavedClause implements Serializable {
	double recall;
	double F1;
	double score;

	SavedClause(Gleaner caller, SingleClauseNode clause, boolean examplesFlipFlopped, String annotation) {
		// Holds a string that will be printed when the clause is dumped.
		// Annotation about what created this clause.

		try {
			double posCoverage = clause.getPosCoverage();
			double negCoverage = clause.negCoverage;
			double precision = clause.precision();
			recall      = clause.recall();
			F1          = clause.F(1);
			score       = clause.score;
			Set<Example> uncoveredPos = clause.getUptoKmissedPositiveExamples(caller.reportUptoThisManyFalseNegatives);
			Set<Example> uncoveredNeg = clause.getUptoKcoveredNegativeExamples(caller.reportUptoThisManyFalsePositives);
			String ruleAsString;
			if (((LearnOneClause) caller.getTaskBeingMonitored()).regressionTask && !((LearnOneClause) caller.getTaskBeingMonitored()).oneClassTask) {
				ruleAsString = "\n " + clause.reportRegressionRuleAsString(examplesFlipFlopped);
			} else {
				ruleAsString = (examplesFlipFlopped ? "not_" : "") + caller.handleInlinersIfPossible(clause.getClause()).toPrettyString("   ", Integer.MAX_VALUE) + ".";
			}
		} catch (Exception e) {
			Utils.reportStackTrace(e);
			Utils.error();
		}
	}
}
