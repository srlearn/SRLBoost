package edu.wisc.cs.will.Utils;

import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;

import java.util.Arrays;

/*
 * @author tkhot
 */
public class ProbDistribution {

	/* Used if we don't have a distribution over multiple values but a single probability */
	private double probOfBeingTrue;
	
	private double[] probDistribution = null;
	
	private boolean hasDistribution;

	public ProbDistribution(double prob, boolean regression) {
		setProbOfBeingTrue(prob, regression);
	}

	public void setProbOfBeingTrue(double probOfBeingTrue, boolean regression) {
		if (regression) {
			setHasDistribution(false);
			this.probOfBeingTrue = probOfBeingTrue;
		}
	}

	/*
	 * Construct distribution using sigmoid
	 */
	public ProbDistribution(RegressionValueOrVector reg) {
		this(reg, true);
	}
	
	public ProbDistribution(RegressionValueOrVector reg, boolean useSigmoid) {
		if (useSigmoid) {
			initUsingSigmoid(reg);
		} else {
			initAfterNormalizing(reg); 
		}
	}
	
	private void initAfterNormalizing(RegressionValueOrVector reg) {
		if (reg.isHasVector()) {
			double deno = VectorStatistics.sum(reg.getRegressionVector());
			double[] probDist = VectorStatistics.scalarProduct(reg.getRegressionVector(), 1/deno);
			setProbDistribution(probDist);
		} else {
			setProbOfBeingTrue(reg.getSingleRegressionValue());
		}
	}

	private void initUsingSigmoid(RegressionValueOrVector reg) {
		if (reg.isHasVector()) {
			double[] exp = VectorStatistics.exponentiate(reg.getRegressionVector());
			double deno = VectorStatistics.sum(exp);
			double[] probDist = VectorStatistics.scalarProduct(exp, 1/deno);
			for (int i = 0; i < probDist.length; i++) {
				if (Double.isNaN(probDist[i])) {
					probDist[i] = 1;
				}
			}
			setProbDistribution(probDist);
		} else {
			setProbOfBeingTrue(BoostingUtils.sigmoid(reg.getSingleRegressionValue(), 0));
		}
	}

	@Override
	public String toString() {
		if (isHasDistribution()) {
			return Arrays.toString(probDistribution);
		} else{
			return probOfBeingTrue+"";
		}
	}

	public double getProbOfBeingTrue() {
		if (isHasDistribution()) {
			Utils.error("Expected single probability value but contains distribution");
		}
		return probOfBeingTrue;
	}

	private void setProbOfBeingTrue(double probOfBeingTrue) {
		if (probOfBeingTrue > 1) {
			Utils.error("Probability greater than 1!!: " +  probOfBeingTrue);
		}
		setHasDistribution(false);		
		this.probOfBeingTrue = probOfBeingTrue;
	}

	public double[] getProbDistribution() {
		if (!isHasDistribution()) {
			Utils.error("Expected distribution but contains single probability value");
		}
		return probDistribution;
	}

	private void setProbDistribution(double[] probDistribution) {
		setHasDistribution(true);
		this.probDistribution = probDistribution;
	}

	public boolean isHasDistribution() {
		return hasDistribution;
	}

	private void setHasDistribution(boolean hasDistribution) {
		this.hasDistribution = hasDistribution;
	}

}
