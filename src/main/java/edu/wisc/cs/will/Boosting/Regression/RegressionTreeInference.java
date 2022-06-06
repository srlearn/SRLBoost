package edu.wisc.cs.will.Boosting.Regression;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;

/*
 * @author tkhot
 *
 */
public class RegressionTreeInference extends SRLInference {

	private final ConditionalModelPerPredicate conditionalModel;

	RegressionTreeInference(ConditionalModelPerPredicate model, WILLSetup setup) {
		super(setup);
		this.conditionalModel=model;
	}

	@Override
	public ProbDistribution getExampleProbability(Example eg) {

		// Currently sets the probability value to regression values. 
		// Hence probabilities could be < 0 or > 1

		RegressionValueOrVector reg = conditionalModel.returnModelRegressionWithPrior(eg);
		if (reg.isHasVector()) {
			Utils.error("Pure regression tree learning doesn't learn vectors!!");
		}
		return new ProbDistribution(reg.getSingleRegressionValue(), true);
	}

	@Override
	public void setMaxTrees(int max) {
		conditionalModel.setNumTrees(max);
	}
}
