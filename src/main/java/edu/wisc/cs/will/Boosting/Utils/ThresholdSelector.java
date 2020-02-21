package edu.wisc.cs.will.Boosting.Utils;

import edu.wisc.cs.will.ILP.CoverageScore;

import java.util.ArrayList;

/*
 * @author Tushar Khot
 */
public class ThresholdSelector {

	static class ProbabilityResult {

		ProbabilityResult(double prob, boolean posEg) {
			super();
			this.prob = prob;
			this.posEg = posEg;
		}

		public String toString() {
			return prob +":" + posEg;
		}
		
		final double prob;
		final boolean posEg;
	}
	
	static class descendingProbs implements java.util.Comparator<ProbabilityResult> {

		 public int compare(ProbabilityResult ob1, ProbabilityResult ob2) {
			if (ob1.prob == ob2.prob) {
				if (ob1.posEg && ob2.posEg) {
					return 0;
				}
				if (ob1.posEg) {
					return -1;
				}
				if (ob2.posEg) {
					return 1;
				}
				return 0;
			} else {
				return (int) Math.ceil(ob2.prob - ob1.prob);
			}
		 }
	}
	
	private final ArrayList<ProbabilityResult> results;

	public double lastComputedF1 = Double.NaN;

	public ThresholdSelector() {
		results = new ArrayList<>();
	}

	public void addProbResult(double prob, boolean posEg) {
		results.add(new ProbabilityResult(prob, posEg));
	}
	
	public double selectBestThreshold() {
		results.sort(new descendingProbs());
		CoverageScore score = new CoverageScore();
		int numP=0;
		int numN=0;
		for (ProbabilityResult res : results) {
			if (res.posEg)
				numP++;
			else
				numN++;
		}
		score.setCounts(0, 0, numN, numP);
		
		double bestThreshold = 0;
		double bestF1 = 0;
		double lastProb = 1;
		for (ProbabilityResult res : results) {
			if (lastProb != res.prob) {
				double f1 = score.getF1();
				if (f1 > bestF1) {
					bestThreshold = (lastProb + res.prob)/2;
					bestF1 = f1;
				}
				lastProb = res.prob;
			}
			if (res.posEg) {
				score.setTruePositives(score.getTruePositives() + 1);
				score.setFalseNegatives(score.getFalseNegatives()-1);
			} else {
				score.setFalsePositives(score.getFalsePositives()+1);
				score.setTrueNegatives(score.getTrueNegatives()-1);
			}
		}
		System.out.println("Best F1 = " + bestF1);
		lastComputedF1 = bestF1;
		return bestThreshold;
	}
}
