package edu.wisc.cs.will.Boosting.MLN;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

/*
 * Class used for inference in MLNs
 * @author tkhot
 */
public class MLNInference extends SRLInference {

	private final Map<String, Long> timePerModel = new HashMap<>();
	private Map<String, Long> cachedRegressionClauseWeights;
	public MLNInference(WILLSetup setup, JointRDNModel model) {
		super(setup);
		this.jointModel = model;
		cachedRegressionClauseWeights = new HashMap<>();
	}
	
	public void resetCache() {
		cachedRegressionClauseWeights = new HashMap<>();
	}

	@Override
	public ProbDistribution getExampleProbability(Example eg) {
		RegressionRDNExample rex = (RegressionRDNExample)eg;
		RegressionValueOrVector reg;
		if (rex.isHasRegressionVector()) {
			double[] probs = new double[rex.getOutputVector().length];
			Arrays.fill(probs, 0);
			reg = new RegressionValueOrVector(probs);
		} else {
			reg = new RegressionValueOrVector(0);
		}
		for (ConditionalModelPerPredicate mod : jointModel.values()) {
			String pred = mod.getTargetPredicate();
			long start = System.currentTimeMillis();
			mod.setCache(cachedRegressionClauseWeights);
			// TODO(TVK!) see if this works
			if (mod.getTargetPredicate().equals(eg.predicateName.name)) {
				reg.addValueOrVector(mod.returnModelRegressionWithPrior(eg));
			} else {
				reg.addValueOrVector(mod.returnModelRegression(eg));
			}
			long end = System.currentTimeMillis();
			addToTimePerModel(pred, end-start);	
		}

		return new ProbDistribution(reg, true);
		
	}
	private void addToTimePerModel(String pred, long l) {
		if (!timePerModel.containsKey(pred)) {
			timePerModel.put(pred, 0L);
		}
		timePerModel.put(pred, timePerModel.get(pred) + l);
	}

	@Override
	public void setMaxTrees(int max) {
		for (ConditionalModelPerPredicate mod : jointModel.values()) {
			mod.setNumTrees(max);
		}
	}

}
