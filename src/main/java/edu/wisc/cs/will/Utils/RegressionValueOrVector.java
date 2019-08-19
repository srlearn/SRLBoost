package edu.wisc.cs.will.Utils;

import java.util.Arrays;

/*
 * @author tkhot
 */
public class RegressionValueOrVector {

	/* Used if we don't have a distribution over multiple values but a single probability */
	private double singleRegressionValue;
	
	private double[] regressionVector;
	
	private boolean hasVector;
	
	public RegressionValueOrVector(double prob) {
		setSingleRegressionValue(prob);
	}

	public RegressionValueOrVector(double[] dist) {
		setRegressionVector(dist);
	}

	public void multiply(double scalar) {
		if (isHasVector()) {
			regressionVector = VectorStatistics.scalarProduct(regressionVector, scalar); 
		} else {
			singleRegressionValue *= scalar;
		}
	}
	
	public void addValueOrVector(RegressionValueOrVector add){
		// If null, then add 0
		if (add == null) {
			return;
		}
		
		if (isHasVector()) {
			regressionVector = VectorStatistics.addVectors(this.regressionVector, add.regressionVector);
		} else {
			singleRegressionValue += add.singleRegressionValue;
		}
	}
	
	public void addScalar(double scalar) {
		if (isHasVector()) {
			regressionVector = VectorStatistics.addScalar(regressionVector, scalar);
		} else {
			singleRegressionValue += scalar;
		}
	}
	
	@Override
	public String toString() {
		if (isHasVector()) {
			return Arrays.toString(regressionVector);
		} else{
			return singleRegressionValue+"";
		}
	}

	public double getSingleRegressionValue() {
		return singleRegressionValue;
	}

	private void setSingleRegressionValue(double singleRegressionValue) {
		this.singleRegressionValue = singleRegressionValue;
	}

	double[] getRegressionVector() {
		return regressionVector;
	}

	private void setRegressionVector(double[] regressionVector) {
		setHasVector();
		this.regressionVector = regressionVector;
	}

	public boolean isHasVector() {
		return hasVector;
	}

	private void setHasVector() {
		this.hasVector = true;
	}

}
