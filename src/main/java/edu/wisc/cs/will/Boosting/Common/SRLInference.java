package edu.wisc.cs.will.Boosting.Common;

import edu.wisc.cs.will.Boosting.MLN.MLNInference;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.Models.RelationalDependencyNetwork;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.ProbDistribution;

import java.util.List;
import java.util.Map;

/**
 * Generic inference interfact for RFGB
 * @author tkhot
 */
public abstract class SRLInference {
	
	protected WILLSetup setup;
	protected RelationalDependencyNetwork rdn;
	protected JointRDNModel jointModel;
	
	protected SRLInference(WILLSetup setup) {
		this.setup = setup;
	}

	protected abstract ProbDistribution getExampleProbability(Example eg);

	public abstract void setMaxTrees(int max);

	/**
	 * 
	 * @param rex - Set the probability for this example
	 */
	private void setExampleProbability(RegressionRDNExample rex) {
		rex.setProbOfExample(getExampleProbability(rex));
	}
	
	public void getProbabilities(List<RegressionRDNExample> allExs) {
		System.currentTimeMillis();
		for (RegressionRDNExample ex : allExs) {
			if (this instanceof MLNInference) {
				((MLNInference)this).resetCache();
			}
			setExampleProbability(ex);
		}
	}

	public void getMarginalProbabilities(Map<String, List<RegressionRDNExample>> jointExamples) {
		for (List<RegressionRDNExample> examples : jointExamples.values()) {
			getProbabilities(examples);
		}
	}

}
