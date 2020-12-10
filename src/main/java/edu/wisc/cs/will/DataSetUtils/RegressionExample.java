package edu.wisc.cs.will.DataSetUtils;

import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.ILP.SingleClauseNode;
import edu.wisc.cs.will.Utils.Utils;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

public class RegressionExample extends Example {

	private static final long serialVersionUID = 1L;
	
	// The regression value that the trees should match
	private double outputValue = 0.0;

	// The expected regression value that we want to match (not used for RFGB but only if pos.txt contains regression examples)
	// This is the regression value mentioned in pos.txt
	public double originalRegressionOrProbValue = 0.0;
	
	// Does this example have a regression vector to fit instead of value ?
	// TODO(TVK): Should always be a vector ?
	private boolean hasRegressionVector = false;
	
	private double[] outputVector = null;
	
	public String leafId = "";

	public RegressionExample(HandleFOPCstrings stringHandler, Literal literal, double outputValue, String provenance, String extraLabel) {
		super(stringHandler, literal, provenance, extraLabel);
		this.setOutputValue(outputValue);
	}

	private Map<SingleClauseNode, Long> cachedNumberOfGroundings = null;
	
	public void cacheNumGroundings(SingleClauseNode key, long num) {
		if (cachedNumberOfGroundings == null) cachedNumberOfGroundings = new HashMap<>();
		cachedNumberOfGroundings.put(key, num);
	}
	
	public long lookupCachedGroundings(SingleClauseNode key) {
		if (cachedNumberOfGroundings == null ||
			!cachedNumberOfGroundings.containsKey(key)) { return -1; }
		return cachedNumberOfGroundings.get(key);
	}

	public void clearCache() {
		cachedNumberOfGroundings = null;
	}

	public double getOutputValue() {
		if (hasRegressionVector) {
			Utils.error("Retrieving scalar output value for " + this.toString() + "\n but has regression vector: " + Arrays.toString(getOutputVector()));
		}
		return outputValue;
	}

	public void setOutputValue(double outputValue) {
		this.outputValue = outputValue;
	}

	public double[] getOutputVector() {
		if (!hasRegressionVector) {
			Utils.error("Retrieving regression vector for " + this.toString() + "\n but has scalar output value: " + getOutputValue());
		}
		return outputVector;
	}

	public void setOutputVector(double[] outputVector) {
		setHasRegressionVector(true);
		this.outputVector = outputVector;
	}

	public boolean isHasRegressionVector() {
		return hasRegressionVector;
	}

	public void setHasRegressionVector(boolean hasRegressionVector) {
		this.hasRegressionVector = hasRegressionVector;
	}

}
