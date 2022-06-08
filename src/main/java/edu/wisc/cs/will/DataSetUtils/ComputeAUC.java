package edu.wisc.cs.will.DataSetUtils;

import edu.wisc.cs.will.Utils.Utils;

import org.srlearn.auc.Confusion;

import java.util.ArrayList;
import java.util.List;

/*
 * This class computes the AUC(ROC/PR) using http://mark.goadrich.com/programs/AUC/
 * @author Tushar Khot
 * @author Alexander L. Hayes
 */
public class ComputeAUC {

	private final double ROC;
	private final double PR;
	private final double CLL;

	public ComputeAUC(List<Double> positiveExampleProbabilities,
			          List<Double> negativeExampleProbabilities) {
		CLL = getCLL(positiveExampleProbabilities, negativeExampleProbabilities);
		// The AUC code crashes if all the examples are of the same category.
		if (Utils.getSizeSafely(positiveExampleProbabilities) < 1) {
			Utils.println("\nNo positive examples in ComputeAUC.  Using AUC-ROC = 0.5 and AUC-PR = 0.0");
			ROC = 0.5;
			PR  = 0.0;
			return;
		}
		if (Utils.getSizeSafely(negativeExampleProbabilities) < 1) {
			Utils.println("\nNo negative examples in ComputeAUC.  Using AUC-ROC = 1.0 and AUC-PR = 1.0");
			ROC = 1.0;
			PR  = 1.0;
			return;
		}

		// TODO(hayesall): Move this logic into `InferBoostedRDN`, or move the `getCLL` into a `Metrics` package.

		List<Double> predictedValues = new ArrayList<>();
		predictedValues.addAll(positiveExampleProbabilities);
		predictedValues.addAll(negativeExampleProbabilities);

		List<Integer> actualValues = new ArrayList<>();

		for (int i=0; i<positiveExampleProbabilities.size(); i++) {
			actualValues.add(1);
		}
		for (int i=0; i<negativeExampleProbabilities.size(); i++) {
			actualValues.add(0);
		}

		Confusion confusion = Confusion.fromPredictions(
				predictedValues.stream().mapToDouble(d -> d).toArray(),
				actualValues.stream().mapToInt(d -> d).toArray()
		);

		ROC = confusion.calculateAUCROC();
		PR = confusion.calculateAUCPR(0.0);
	}
	
	private double getCLL(List<Double> posProb,
				List<Double> negProb) {
		Utils.println("%Pos=" + posProb.size());
		Utils.println("%Neg=" + negProb.size());
		double llSum = 0;
		for (Double prob : posProb) {
			if (prob == 0) {
				prob = 1e-6;
			}
			llSum += Math.log(prob);
		}
		Utils.println("%LL:" + llSum);
		for (Double prob : negProb) {
			if (prob == 1) {
				prob = 1 - 1e-6;
			}
			llSum += Math.log(1 - prob);
		}
		Utils.println("%LL:" + llSum);
		return llSum/(posProb.size() + negProb.size());
	}

	public double getROC() {
		return ROC;
	}

	public double getPR() {
		return PR;
	}
	
	public double getCLL() {
		return CLL;
	}
	
}
