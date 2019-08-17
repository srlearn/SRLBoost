package edu.wisc.cs.will.Boosting.OneClass;

import java.util.ArrayList;
import java.util.List;

/**
 * @author tkhot
 */
class KernelEstimator {

	private double bandwidth;
	
	private enum KernelFunction {
		EPAN,
		GAUSSIAN
	}
	
	private KernelFunction kernelType;
	
	KernelEstimator() {
		bandwidth = 0.5;
		kernelType = KernelFunction.GAUSSIAN;
	}
	
	double getDistance(int commonEdges) {
		if (commonEdges == -1) {
			return 0; 
		}
		return Math.exp(-(double)commonEdges);
	}
	
	double getKernelValue(double distance) {
		switch (kernelType) {
		case EPAN:
			return (3.0/4.0) * (1 - Math.pow(distance/bandwidth, 2));
			
		case GAUSSIAN:
			return (1.0 / Math.sqrt(2.0 * Math.PI)) * Math.exp(- Math.pow(distance/bandwidth, 2.0) / 2);
			
		default:
			return distance;
		}
	}

	double getProbabilityFromDistance(List<Double> distances) {
		List<Double> kernelVals = new ArrayList<>();
		for (Double dist : distances) {
			kernelVals.add(getKernelValue(dist));
		}
		return getProbabilityFromKernel(kernelVals);
	}

	private double getProbabilityFromKernel(List<Double> kernelVals) {
		double sum = 0;
		for (Double kval : kernelVals) {
			sum += kval;
		}
		return (1/((double)kernelVals.size() * bandwidth)) * sum;
	}

	double getBandwidth() {
		return bandwidth;
	}

}
