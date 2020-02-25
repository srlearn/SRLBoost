package edu.wisc.cs.will.Boosting.EM;

import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.VectorStatistics;

import java.util.*;

/*
 * 
 * Class to store sampled world states for the hidden literals along with probability of each world state
 * @author tkhot
 *
 */
public class HiddenLiteralSamples {

	// TODO(@hayesall): `worldStates` and `probabilities` are queried but never updated.
	private final List<HiddenLiteralState> worldStates;
	private final List<Double>     probabilities;

	private HiddenLiteralSamples() {
		worldStates = new ArrayList<>();
		probabilities = new ArrayList<>();
		// Only used while adding samples. Used to compute the probability of each world after sampling.
	}


	public ProbDistribution sampledProbOfExample(Example eg) {
		double sumProb = 0;
		boolean isMultiClass = false;
		double[] sumVec = null;
		int size = 0;
		RegressionRDNExample rex = (RegressionRDNExample)eg;
		if (rex.isHasRegressionVector()) {
			isMultiClass = true;
			size = rex.getOutputVector().length;
			sumVec = new double[size];
			Arrays.fill(sumVec, 0.0);
		}
		//ProbDistribution probDistr = new Pro
		for (int j = 0; j < worldStates.size(); j++) {
			HiddenLiteralState state = worldStates.get(j);
			int index = state.getAssignment(eg);
			if (isMultiClass) {
				double[] probVec = VectorStatistics.scalarProduct(VectorStatistics.createIndicator(size, index),
						probabilities.get(j));
				sumVec = VectorStatistics.addVectors(sumVec, probVec);
			} else {
				if (index == 1) {
					sumProb += probabilities.get(j);
				}
			}
		}
		ProbDistribution probDistr;
		if (isMultiClass) {
			probDistr = new ProbDistribution(sumVec);
		} else {
			probDistr = new ProbDistribution(sumProb);
		}
		return probDistr;
	}

	@Override
	public String toString() {
		StringBuilder rep = new StringBuilder();
		for (int i = 0; i < worldStates.size(); i++) {
			rep.append("\n");
			rep.append(worldStates.get(i).getStringRep());
			rep.append(":").append(probabilities.get(i));
		}	
		return rep.toString();
	}

}
