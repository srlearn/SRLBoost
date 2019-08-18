package edu.wisc.cs.will.Boosting.OneClass;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.Utils;

/*
 * @author tkhot
 */
public class PairWiseExampleScore {

	private Map<String, Double> currentPairWiseDistance;
	
	private Map<String, Integer> exampleCategory;
	
	int currCount= 0;

	int numLabelled = 0;
	
	private KernelEstimator kernelEst;
	
	PairWiseExampleScore() {
		currentPairWiseDistance = new HashMap<>();
		exampleCategory         = new HashMap<>();
		kernelEst 				= new KernelEstimator();
	}
	
	private static String getExamplePairKey(Example eg1, Example eg2) {
		String eg1String = eg1.toPrettyString();
		String eg2String = eg2.toPrettyString();
		
		if (eg1String.equals(eg2String)) {
			Utils.error("Distance between the same examples: " + eg1String);
		}
		// To make sure that order of examples doesn't matter
		if (eg1String.compareTo(eg2String) > 0) {
			return eg1String + "::::" + eg2String; 
		}
		return eg2String + "::::" + eg1String;
	}

	public double calculateKernelScore(List<Example> trueBranch,
								 List<Example> falseBranch, int depth) {
	
		double score;
		
		double changeInKDE = 0;
		double changeInDist = 0;
		int distCounter = 0;
		int numLabelledHere=0;
		for (Example x_i : trueBranch) {
			int cat_i = getCategory(x_i);

			for (Example x_j : falseBranch) {
				int cat_j = getCategory(x_j);

				double dist = getDistance(x_i, x_j);
				double updateDist = kernelEst.getDistance(depth);
				double new_dist = (dist * currCount + updateDist) / (currCount + 1);
				double old_kVal = kernelEst.getKernelValue(dist);
				double new_kVal = kernelEst.getKernelValue(new_dist);

				// If different class
				if (cat_i != cat_j) {
					// The change in distance effects the entropy
					// TODO(TVK)

					double changeForXi = (1 / ((double) (numLabelled) * kernelEst.getBandwidth())) * (new_kVal - old_kVal);
					changeInKDE -= changeForXi * (1 - dist);

				}

				if ((cat_i == cat_j) && cat_i != -1) {
					double changeForXi = (1 / ((double) (numLabelled - 1) * kernelEst.getBandwidth())) * (new_kVal - old_kVal);
					changeInKDE += changeForXi + changeForXi;
				}

				changeInDist += dist - new_dist;
				distCounter += 1;
			}
		}
		
		
		for (int i = 0; i < trueBranch.size(); i++) {
			Example x_i = trueBranch.get(i);
			int cat_i = getCategory(x_i);
			if (cat_i != -1) { numLabelledHere ++;}
			for (int j = i+1; j < trueBranch.size(); j++) {
				Example x_j = trueBranch.get(j);
				int cat_j = getCategory(x_j);
				
				double dist = getDistance(x_i, x_j);
				double updateDist = 0; // Same branch, no change in distance
				double new_dist = (dist*currCount + updateDist)/(currCount + 1);
				double old_kVal = kernelEst.getKernelValue(dist); // getKernelVal(dist);
				double new_kVal = kernelEst.getKernelValue(new_dist);  //getKernelVal(new_dist);
				
				// If different class
				if (cat_i != cat_j) {
					double changeForXi = (1/((double)(numLabelled) * kernelEst.getBandwidth())) * (new_kVal - old_kVal);
					changeInKDE -= changeForXi * (1 - dist);

				}
				
				if ((cat_i == cat_j) && cat_i != -1) {
					double changeForXi = (1/((double)(numLabelled-1) * kernelEst.getBandwidth()))* (new_kVal - old_kVal);
					changeInKDE += changeForXi + changeForXi;
				}
				
				changeInDist += dist - new_dist;
				distCounter += 1;
			}
		}
		
		for (int i = 0; i < falseBranch.size(); i++) {
			Example x_i = falseBranch.get(i);
			int cat_i = getCategory(x_i);
			if (cat_i != -1) { numLabelledHere ++;}
			for (int j = i+1; j < falseBranch.size(); j++) {
				Example x_j = falseBranch.get(j);
				int cat_j = getCategory(x_j);
				
				double dist = getDistance(x_i, x_j);
				double updateDist = 0; // Same branch, no change in distance
				double new_dist = (dist*currCount + updateDist)/(currCount + 1);
				double old_kVal = kernelEst.getKernelValue(dist); // getKernelVal(dist);
				double new_kVal = kernelEst.getKernelValue(new_dist);  //getKernelVal(new_dist);
				
				// If different class
				if (cat_i != cat_j) {
					// The change in distance effects the entropy
					// TODO(TVK)
					
					double changeForXi = (1/((double)(numLabelled) * kernelEst.getBandwidth())) * (new_kVal - old_kVal);
					changeInKDE -= changeForXi * (1 - dist);

				}
				
				if ((cat_i == cat_j) && cat_i != -1) {
					double changeForXi =(1/((double)(numLabelled-1) * kernelEst.getBandwidth())) * (new_kVal - old_kVal);
					changeInKDE += changeForXi + changeForXi;
				}
				
				changeInDist += dist - new_dist;
				distCounter += 1;
			}
		}
		
		score = (numLabelledHere != 0 ? (changeInKDE/(double)numLabelledHere) : 0) + 1*(distCounter != 0 ? (changeInDist/ (double)distCounter): 0);
		Utils.println("Score=" + score);
		Utils.println("changeInKDE=" + changeInKDE + " counter = " + numLabelledHere);
		Utils.println("changeInDist= " + changeInDist + " counter = " + distCounter);
		return score;
	}

	private int getCategory(Example eg) {
		if (!exampleCategory.containsKey(eg.toPrettyString())) {
			Utils.error("No category info for " + eg);
		}
		return exampleCategory.get(eg.toPrettyString());
	}

	void addDistance(Example eg1,
					 Example eg2, double dist) {
		String key  = getExamplePairKey(eg1, eg2);
		currentPairWiseDistance.put(key, dist);
	}
	
	void addExample(Example eg, int category) {
		exampleCategory.put(eg.toPrettyString(), category);
	}


	private double getDistance(Example eg1, Example eg2) {
		String key =  getExamplePairKey(eg1, eg2);
		if (!currentPairWiseDistance.containsKey(key)) {
			Utils.error("No distance stored between " + eg1 + " and " + eg2);
		} 
		return currentPairWiseDistance.get(key);
	}

	public double getVariance(List<Example> examples) {
		return 1 - (1/examples.size());
	}
	public static List<Example> removeFromCopy(List<Example> allEgs, List<Example> subtractEg) {
		List<Example> copy  = new ArrayList<>(allEgs);
		copy.removeAll(subtractEg);
		return copy;
	}

}
