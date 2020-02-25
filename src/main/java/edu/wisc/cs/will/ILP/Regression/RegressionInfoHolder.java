package edu.wisc.cs.will.ILP.Regression;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.ILP.SingleClauseNode;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/*
 * @author tkhot
 *
 */
public abstract class RegressionInfoHolder {

	BranchStats trueStats;
	BranchStats falseStats;

	public abstract double weightedVarianceAtSuccess();
	public abstract double weightedVarianceAtFailure();
	
	public abstract double totalExampleWeightAtSuccess();
	public abstract double totalExampleWeightAtFailure();
	
	public abstract double meanAtSuccess();
	public abstract double meanAtFailure();

	public abstract RegressionInfoHolder addFailureStats(RegressionInfoHolder addThis);
	
	public double varianceAtSuccess() {
		return weightedVarianceAtSuccess() / totalExampleWeightAtSuccess();
	}
	
	public double varianceAtFailure() {
		return weightedVarianceAtFailure() / totalExampleWeightAtFailure();
	}
	public abstract void addFailureExample(Example eg, long numGrndg, double weight);

	public abstract void populateExamples(LearnOneClause task, SingleClauseNode singleClauseNode) throws SearchInterrupted;

	public BranchStats getTrueStats() {
		return trueStats;
	}

	public BranchStats getFalseStats() {
		return falseStats;
	}
}
