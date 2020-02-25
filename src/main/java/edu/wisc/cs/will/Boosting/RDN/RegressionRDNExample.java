package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.Boosting.EM.HiddenLiteralState;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;
import java.util.Arrays;

/**
 * Regression Example used for learning RDNs
 * @author Tushar Khot
 *
 */
public class RegressionRDNExample extends RegressionExample  implements Serializable  {
	// TODO(?): move to DataSetUtils, maybe?

	private static final long serialVersionUID = 5438994291636517166L;
	
	/**
	 *  This is used to indicate the original truth value of an example
	 *  Should not be changed once set
	 */
	@Deprecated
	private boolean originalTruthValue = false;
	
	/**
	 * Rather than using a boolean value, use integer for original value
	 * for single class problem, 0==false, 1==true
	 * for multi  class problem, the originalValue is an index to a constant value stored in MultiClassExampleHandler
	 */
	private int originalValue = 0;
	
	/**
	 *  This indicates whether this is a hidden literal. Original truth value wouldn't be useful if this is
	 *  set to true.
	 */
	private boolean hiddenLiteral = false;
	
	/**
	 * Only set if hiddenLiteral is set to true. 
	 */
	private int originalHiddenLiteralVal = 0;
	
	/**
	 *  This is to be only used while sampling.
	 */
	@Deprecated
	private boolean sampledTruthValue=(Utils.random() > 0.8);
	
	/**
	 * Rather than using a boolean value, use integer for sampled value
	 * for single class problem, 0==false, 1==true
	 * for multi class problem, the sampledValue is an index to a constant value stored in MultiClassExampleHandler
	 */
	private int sampledValue= (Utils.random() > 0.8) ? 1 : 0;
	
	
	/**
	 * Examples may have an associated state assignment to the hidden literals for the corresponding 
	 * output value.
	 */
	private final HiddenLiteralState stateAssociatedWithOutput = null;
	
	
	
	/**
	 * The probability of this example being true. Generally set by sampling procedure
	 * Hence  has Nan default value.
	 */
	private ProbDistribution probOfExample = null;
	
	public RegressionRDNExample(HandleFOPCstrings stringHandler, Literal literal, double outputValue, String provenance, String extraLabel) {
		super(stringHandler, literal, outputValue, provenance, extraLabel);
	}

	public RegressionRDNExample(HandleFOPCstrings stringHandler, Literal literal, double outputValue, String provenance, String extraLabel, boolean truthValue) {
		super(stringHandler, literal, outputValue, provenance, extraLabel);
		originalTruthValue = truthValue;
		originalValue = truthValue ? 1:0;
	}

	public RegressionRDNExample(Example ex, boolean truthValue) {
		super(ex.getStringHandler(), ex, (truthValue ? 1 : 0), ex.provenance, ex.extraLabel);
		originalTruthValue = truthValue;
		originalValue = truthValue ? 1:0;
	}

	public RegressionRDNExample(Literal lit, boolean truthValue, String provenance) {
		this(lit.getStringHandler(), lit, (truthValue ? 1 : 0), provenance, null);
	}

	public boolean isOriginalTruthValue() {
		if (isHiddenLiteral()) {
			Utils.waitHere("Can't trust original truth value here");
		}
		if (getOriginalValue() > 1) {
			Utils.error("Checking for truth value for multi-class example.");
		}
		return getOriginalValue() == 1;
	}

	void setOriginalTruthValue(boolean originalTruthValue) {
		setOriginalValue(originalTruthValue?1:0);
	}

	boolean isHiddenLiteral() {
		return hiddenLiteral;
	}

	void setHiddenLiteral() {
		this.hiddenLiteral = true;
	}

	int getOriginalHiddenLiteralVal() {
		if (!isHiddenLiteral()) {
			Utils.error("Not hidden literal!");
		}
		return originalHiddenLiteralVal;
	}

	void setOriginalHiddenLiteralVal(int originalHiddenLiteralVal) {
		if (!isHiddenLiteral()) {
			Utils.error("Not hidden literal!");
		}
		this.originalHiddenLiteralVal = originalHiddenLiteralVal;
	}

	public ProbDistribution getProbOfExample() {
		if (probOfExample == null) {
			Utils.error("Probability was not set");
			return null;
		}
		return probOfExample;
	}

	public void setProbOfExample(ProbDistribution probOfExample) {
		this.probOfExample = probOfExample;
	}
	
	public String toString() {
		return super.toString();
	}

	public String toPrettyString() {
		String result= super.toString();
		result += " Actual Bool=" + originalTruthValue +" Prob=" + probOfExample + " Output=";
		if (isHasRegressionVector()) {
			result += Arrays.toString(getOutputVector());
		} else {
			result += getOutputValue();
		}
		return result;
	}

	public int getOriginalValue() {
		if (isHiddenLiteral()) {
			Utils.waitHere("Can't trust original value here");
		}
		return originalValue;
	}

	void setOriginalValue(int originalValue) {
		this.originalValue = originalValue;
	}

	public int getSampledValue() {
		return sampledValue;
	}

	void setSampledValue(int sampledValue) {
		this.sampledValue = sampledValue;
	}

	public HiddenLiteralState getStateAssociatedWithOutput() {
		return stateAssociatedWithOutput;
	}

}
