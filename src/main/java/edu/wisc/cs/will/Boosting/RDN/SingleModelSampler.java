package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.ProbDistribution;

import java.util.List;

public class SingleModelSampler extends SRLInference {

	private final ConditionalModelPerPredicate conditionalModel;

	SingleModelSampler(ConditionalModelPerPredicate model, WILLSetup setup, JointRDNModel jointModel) {
		super(setup);
		this.conditionalModel = model;
		this.jointModel = jointModel;
	}

	// TODO(?): Lot of common stuff with JointModelSampler, refactor

	public ProbDistribution getExampleProbability(Example eg) {
		return conditionalModel.returnModelProbability(eg);
	}

	// TODO If you have recursive rules, generate samples.
	@Override
	public void getProbabilities(List<RegressionRDNExample> allExs) {
		super.getProbabilities(allExs);

	}

	@Override
	public void setMaxTrees(int max) {
		conditionalModel.setNumTrees(max);
	}

}