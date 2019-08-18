package edu.wisc.cs.will.Boosting.RDN;

import java.util.ArrayList;
import java.util.List;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.RDN.Models.RelationalDependencyNetwork;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;

public class SingleModelSampler extends SRLInference {

	private ConditionalModelPerPredicate conditionalModel;

	private boolean hasRecursion;


	public SingleModelSampler(ConditionalModelPerPredicate model, WILLSetup setup, JointRDNModel jointModel, boolean isRecursive) {
		super(setup);
		this.conditionalModel = model;
		this.jointModel = jointModel;
		hasRecursion = isRecursive;
	}

	public void setSample(List<RegressionRDNExample> eg) {
		for (Example example : eg) {
			RegressionRDNExample rex = (RegressionRDNExample) example;
			ProbDistribution prob = conditionalModel.returnModelProbability(example);

			int prevValue = rex.getSampledValue();

			rex.setSampledValue(prob.randomlySelect());
			if (!rex.isHasRegressionVector()) {
				if (rex.getSampledValue() == 1) {
					setup.addFact(getRecursiveFact(rex));
				} else {
					setup.removeFact(getRecursiveFact(rex));
				}
			} else {
				if (prevValue != rex.getSampledValue()) {
					Example removeEg = setup.getMulticlassHandler().createExampleFromClass(rex, prevValue);
					Example addEg = setup.getMulticlassHandler().createExampleFromClass(rex, rex.getSampledValue());
					setup.removeFact(getRecursiveFact(removeEg));
					setup.addFact(getRecursiveFact(addEg));
				}
			}
		}
	}

	// TODO(?): Lot of common stuff with JointModelSampler, refactor

	private Literal getRecursiveFact(Example rex) {
		return setup.getHandler().getLiteral(
				setup.getHandler().getPredicateName(WILLSetup.recursivePredPrefix + rex.predicateName.name), rex.getArguments());
	}

	/*
	 * WILLSetup should have been called before
	 */
	void getProbabilitiesUsingSamples(List<RegressionRDNExample> ex) {
		Utils.println("Using recursion sampling");
		List<double[]> valueCounts = new ArrayList<>();
		String target = conditionalModel.getTargetPredicate();
		int size = setup.getMulticlassHandler().numConstantsForPredicate(target);


		int burnInSteps = 20;
		int numOfSamples = 200;
		for (int i = -burnInSteps; i < numOfSamples; i++) {
			System.currentTimeMillis();
			setSample(ex);
			System.currentTimeMillis();
			if (i >= 0) {
				System.currentTimeMillis();
				countSample(ex, valueCounts, size);
				System.currentTimeMillis();
			}
			if (i % 10 == 0) {
				Utils.println("Done with " + i + " samples");
			}
		}
		setProbability(valueCounts, ex);
	}

	private void setProbability(List<double[]> valueCounts, List<RegressionRDNExample> ex) {
		for (int i = 0; i < ex.size(); i++) {
			RegressionRDNExample eg = ex.get(i);
			double[] counts = valueCounts.get(i);

			ProbDistribution distr = new ProbDistribution(new RegressionValueOrVector(counts), false);
			eg.setProbOfExample(distr);
		}
	}

	private void countSample(List<RegressionRDNExample> ex, List<double[]> valueCounts, int totalVals) {
		for (int i = 0; i < ex.size(); i++) {
			if (valueCounts.size() <= i) {
				valueCounts.add(new double[totalVals]);
			}
			RegressionRDNExample eg = ex.get(i);
			int val = eg.getSampledValue();
			valueCounts.get(i)[val] += 1;
		}
	}

	public ProbDistribution getExampleProbability(Example eg) {
		return conditionalModel.returnModelProbability(eg);
	}

	// TODO If you have recursive rules, generate samples.
	@Override
	public void getProbabilities(List<RegressionRDNExample> allExs) {
		if (hasRecursion) {
			getProbabilitiesUsingSamples(allExs);
		} else {
			super.getProbabilities(allExs);
		}

	}

	@Override
	public void setMaxTrees(int max) {
		conditionalModel.setNumTrees(max);
	}

	/*
	 * @return the rdn
	 */
	public RelationalDependencyNetwork getRdn() {
		// Since the joint model is updated, create RDN on the fly
		return new RelationalDependencyNetwork(jointModel, setup);
	}
}