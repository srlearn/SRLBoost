package edu.wisc.cs.will.ILP.Regression;

import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.VectorStatistics;

/*
 * @author tkhot
 *
 */
public class BranchVectorStats extends BranchStats {

	private double[] sumOfOutputAndNumGroundingVec = null;

	BranchVectorStats() {
	}

	void addNumVectorOutput(long num, double[] output, double weight) {
		
		double deno;
		deno = 0.1;
		if (sumOfOutputAndNumGroundingVec == null) {
        	sumOfOutputAndNumGroundingVec = new double[output.length];
        	// the default value is zero, but don't want to miss it
        	// Faster than filling the array with 0's
        	if (Utils.diffDoubles(sumOfOutputAndNumGroundingVec[0], 0)) {
        		Utils.error("Java didn't init double array with 0 values");
        	}
        }
		sumOfNumGroundingSquared += num*num*weight;
 
		sumOfOutputAndNumGroundingVec = VectorStatistics.addVectors(sumOfOutputAndNumGroundingVec, 
				VectorStatistics.scalarProduct(output, num*weight));
       sumOfOutputSquared += weight* VectorStatistics.dotProduct(output, output);
       
       // Check the first class to decide pos/neg example
       if (output[0] > 0 ) {
       	numPositiveOutputs+=weight; 
       } else {
       	numNegativeOutputs+=weight;
       }
       numExamples+=weight;
       sumOfNumGroundingSquaredWithProb = num*num*weight*deno;
	}

}
