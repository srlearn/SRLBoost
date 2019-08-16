package edu.wisc.cs.will.ILP;

import java.io.Serializable;
import java.util.Set;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 *  An entry in a Gleaner.
 */
@SuppressWarnings("serial")
public class SavedClause implements Serializable {
	long nodeCountWhenSaved;
	long acceptableNodeCountWhenSaved;
	boolean examplesFlipFlopped;
	String annotation; // Holds a string that will be printed when the clause is dumped.
	String clauseCreator; // Annotation about what created this clause.
	double posCoverage;
	double negCoverage;
	protected double precision;
	protected double recall;
	protected double F1;
	protected double score;
	Set<Example> uncoveredPos;
	Set<Example> uncoveredNeg;
	String ruleAsString;
	
	SavedClause(Gleaner caller, SingleClauseNode clause, long nodeCountWhenSaved, long acceptableNodeCountWhenSaved, boolean examplesFlipFlopped, String annotation, String clauseCreator) {
		this.nodeCountWhenSaved           = nodeCountWhenSaved;
		this.acceptableNodeCountWhenSaved = acceptableNodeCountWhenSaved;
		this.examplesFlipFlopped          = examplesFlipFlopped;
		this.annotation                   = annotation;
		this.clauseCreator                = clauseCreator;
		
		try {
			posCoverage = clause.getPosCoverage();
			negCoverage = clause.negCoverage;
			precision   = clause.precision();
			recall      = clause.recall();
			F1          = clause.F(1);
			score       = clause.score;
			uncoveredPos = clause.getUptoKmissedPositiveExamples( caller.reportUptoThisManyFalseNegatives);
			uncoveredNeg = clause.getUptoKcoveredNegativeExamples(caller.reportUptoThisManyFalsePositives);
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
