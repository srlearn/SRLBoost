package edu.wisc.cs.will.ILP.Regression;

import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.ILP.SingleClauseNode;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/*
 * @author tkhot
 */
public class RegressionInfoHolderForMLN extends RegressionInfoHolderForRDN {

	public RegressionInfoHolderForMLN() {
		super();
	}

	@Override
	public void populateExamples(LearnOneClause task, SingleClauseNode caller) throws SearchInterrupted {
		if (!task.regressionTask) { Utils.error("Should call this when NOT doing regression."); }
		if (caller.getPosCoverage() < 0.0) { caller.computeCoverage(); }
		for (Example posEx : task.getPosExamples()) {
			double weight = posEx.getWeightOnExample();
			double output = ((RegressionExample) posEx).getOutputValue();
			ProbDistribution prob   = ((RegressionRDNExample)posEx).getProbOfExample();
			if (prob.isHasDistribution()) {
				Utils.error("Expected single probability value but contains distribution");
			}
			if (!caller.posExampleAlreadyExcluded(posEx)) {
				long num = 1;
				if (caller != caller.getRootNode()) {
					num  = caller.getNumberOfGroundingsForRegressionEx(posEx);
				}
				if (num == 0) {
					Utils.waitHere("Number of groundings = 0 for " + posEx + " with " + caller.getClause());
					num = 1;
				}
				trueStats.addNumOutput(num, output, weight, prob.getProbOfBeingTrue());		
			}
		}
		RegressionInfoHolder totalFalseStats = caller.getTotalFalseBranchHolder() ;
		if (totalFalseStats != null) {
			falseStats = falseStats.add(totalFalseStats.falseStats);
		}
	}
}
