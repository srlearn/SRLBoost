package edu.wisc.cs.will.Boosting.OneClass;

/*
 * @author tkhot
 */
class KernelEstimator {

	private enum KernelFunction {
		EPAN,
		GAUSSIAN
	}

	KernelEstimator() {
		double bandwidth = 0.5;
		KernelFunction kernelType = KernelFunction.GAUSSIAN;
	}

}
