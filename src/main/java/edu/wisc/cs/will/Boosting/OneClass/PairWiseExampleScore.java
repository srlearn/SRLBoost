package edu.wisc.cs.will.Boosting.OneClass;

import edu.wisc.cs.will.DataSetUtils.Example;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/*
 * @author tkhot
 */
public class PairWiseExampleScore {

	PairWiseExampleScore() {
		Map<String, Double> currentPairWiseDistance = new HashMap<>();
		Map<String, Integer> exampleCategory = new HashMap<>();
		KernelEstimator kernelEst = new KernelEstimator();
	}


	public double getVariance(List<Example> examples) {
		return 1 - (1.0/examples.size());
	}
	public static List<Example> removeFromCopy(List<Example> allEgs, List<Example> subtractEg) {
		List<Example> copy  = new ArrayList<>(allEgs);
		copy.removeAll(subtractEg);
		return copy;
	}

}
