package edu.wisc.cs.will.Boosting.EM;

import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.VectorStatistics;

import java.util.*;

/*
 * 
 * Class to store sampled world states for the hidden literals along with probability of each world state
 * @author tkhot
 *
 */
public class HiddenLiteralSamples {

	private List<HiddenLiteralState> worldStates;
	private List<Double>     probabilities;
	// Only used while adding samples. Used to compute the probability of each world after sampling.
	private final List<Long>       counts;
	
	private Map<HiddenLiteralState, Integer> worldStateToIndex;
	
	public HiddenLiteralSamples() {
		worldStates = new ArrayList<>();
		probabilities = new ArrayList<>();
		counts = new ArrayList<>();
		worldStateToIndex = new HashMap<>();
	}


	public void buildExampleToAssignMap() {
		for (HiddenLiteralState state : worldStates) {
			state.buildLiteralToAssignMap();
		}
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

	/*
	 * @return the worldStates
	 */
	public List<HiddenLiteralState> getWorldStates() {
		return worldStates;
	}

	/*
	 * If the number of probabilities == 0  or less than number of world state
	 * then the counters were not updated to probabilities using the number of 
	 * samples.
	 * @return the probabilities
	 */
	public List<Double> getProbabilities() {
		return probabilities;
	}

	public void updateSample(Map<String, List<RegressionRDNExample>> jointExamples) {
		HiddenLiteralState state = new HiddenLiteralState(jointExamples);
		Integer index = worldStateToIndex.get(state);
		if (index == null) {
			index = worldStates.size();
			worldStates.add(state);
			worldStateToIndex.put(state, index);
			counts.add(0L);
		}
		counts.set(index, counts.get(index) + 1);
	}
	
	public void setProbabilitiesFromCounters(long numSamples) {
		for (Long count : counts) {
			probabilities.add((double)count/(double)numSamples);
		}
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

	public HiddenLiteralSamples getMostLikelyState() {
		
		HiddenLiteralSamples marginalSample = new HiddenLiteralSamples();
		HiddenLiteralState mostLikelyState = null;
		double maxProb = -1;
		for (int i = 0; i < worldStates.size(); i++) {
			Double prob = probabilities.get(i);
			if (prob > maxProb) {
				maxProb = prob;
				mostLikelyState = worldStates.get(i);
			}
		}
		
		if (mostLikelyState == null) {
			Utils.error("No world state found");
		}
		int index = 0;
		marginalSample.worldStateToIndex.put(mostLikelyState, index);
		marginalSample.worldStates.add(mostLikelyState);
		marginalSample.probabilities.add(1.0);
		
		// To compute the difference between MAP and EM probs
		 this.buildExampleToAssignMap();
		return marginalSample;
	}

	public void setWorldStates(List<HiddenLiteralState> worldStates) {
		this.worldStates = worldStates;
	}

	public void setProbabilities(List<Double> probabilities) {
		this.probabilities = probabilities;
	}

	public Map<HiddenLiteralState, Integer> getWorldStateToIndex() {
		return worldStateToIndex;
	}

	public void setWorldStateToIndex(
			Map<HiddenLiteralState, Integer> worldStateToIndex) {
		this.worldStateToIndex = worldStateToIndex;
	}

	public void buildExampleToCondProbMap(WILLSetup setup, JointRDNModel jtModel) {
		for (HiddenLiteralState state : worldStates) {
			state.buildExampleToCondProbMap(setup, jtModel);
		}
	}
	
	/*
	 * Will pick the top k states with the highest state pseudo probabilities
	 */
	public void pickMostLikelyStates(int maxStates) {
		
		if (worldStates.size() < maxStates) {
			Utils.waitHere("Sampled less than max states: " + worldStates.size() + " < " + maxStates);
			return;
		}
		List<Integer> mostLikely = getMostLikelyStates(maxStates);
		
		for (int i = worldStates.size() - 1; i >=0 ; i--) {
			if (!mostLikely.contains(i)) {
				worldStates.remove(i);
				probabilities.remove(i);
			} 
		}
		
		// Rebuild map
		worldStateToIndex = new HashMap<>();
		for (int i = 0; i < worldStates.size(); i++) {
			worldStateToIndex.put(worldStates.get(i), i);
		}
		
	}

	private List<Integer> getMostLikelyStates(int maxStates) {
		List<Double> probabilities = new LinkedList<>();
		List<Integer> indexes = new LinkedList<>();
		for (int i = 0; i < worldStates.size(); i++) {
			double prob = worldStates.get(i).getStatePseudoProbability();
			int j;
			for (j = 0; j < probabilities.size(); j++) {
				if (probabilities.get(j) < prob) {
					break;
				}
			}
			probabilities.add(j, prob);
			indexes.add(j, i);
			while (probabilities.size() > maxStates) {
				probabilities.remove(probabilities.size()-1);
				indexes.remove(indexes.size()-1);
			}
		}
		return indexes;
	}
	
}
