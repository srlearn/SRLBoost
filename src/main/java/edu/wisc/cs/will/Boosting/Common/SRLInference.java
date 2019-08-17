package edu.wisc.cs.will.Boosting.Common;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.Boosting.EM.HiddenLiteralSamples;
import edu.wisc.cs.will.Boosting.EM.HiddenLiteralState;
import edu.wisc.cs.will.Boosting.MLN.MLNInference;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.RDN.Models.DependencyPredicateNode.PredicateType;
import edu.wisc.cs.will.Boosting.RDN.Models.RelationalDependencyNetwork;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;

/**
 * Generic inference interfact for RFGB
 * @author tkhot
 */
public abstract class SRLInference {
	
	protected WILLSetup setup;
	protected RelationalDependencyNetwork rdn;
	protected JointRDNModel jointModel;
	
	public SRLInference(WILLSetup setup) {
		this.setup = setup;
	}

	public abstract ProbDistribution getExampleProbability(Example eg);

	public abstract void setMaxTrees(int max);

	/**
	 * 
	 * @param rex - Set the probability for this example
	 */
	private void setExampleProbability(RegressionRDNExample rex) {
		rex.setProbOfExample(getExampleProbability(rex));
	}
	
	public void getProbabilities(List<RegressionRDNExample> allExs) {
		System.currentTimeMillis();
		for (RegressionRDNExample ex : allExs) {
			if (this instanceof MLNInference) {
				((MLNInference)this).resetCache();
			}
			setExampleProbability(ex);
		}
	}
	
	/**
	 * Compute the averaged probability over each sample
	 */
	public void getProbabilitiesUsingSampledStates(HiddenLiteralSamples samples, List<RegressionRDNExample> allExs) {
		List<ProbDistribution> exProb = new ArrayList<>(allExs.size());
		String currTarget = null;
		for (RegressionRDNExample allEx : allExs) {
			exProb.add(null);
			if (currTarget == null) {
				currTarget = allEx.predicateName.name;
			} else {
				if (!currTarget.equals(allEx.predicateName.name)) {
					Utils.waitHere("Expected all examples to be of same type:" + allEx.predicateName.name + " but also found: " + currTarget);
				}
			}
		}
		
		if (getRdn() == null) {
			Utils.waitHere("Expected RDN to be set!");
		}
		
		// Have to collect the predicate names because query parents returns predicatename and not strings
		
		// Remove multiclass prefix from predicate name
		if (currTarget.startsWith(WILLSetup.multiclassPredPrefix)) {
			currTarget = currTarget.substring(WILLSetup.multiclassPredPrefix.length());
		}
		if (! (this instanceof MLNInference)) {
			boolean marginalizeAll = true;
			for( PredicateName queryPars : getRdn().getQueryParents(currTarget)) {
				// Don't marginalize this predicate
				// There will be something left after marginalizing
				marginalizeAll = false;
			}


			// Save marginalizing time
			if (marginalizeAll && !getRdn().isRecursive(currTarget)) {
				Utils.println("Computing without sampling since no hidden/query parents.");
				getProbabilities(allExs);
				return;
			}
		}
		Utils.println("Computing using " + samples.getWorldStates().size() + " samples.");
		// If doesn't depend on the world state, just return the probabilities ie every predicate has been marginalized out.
		// Shouldn't be called anymore
		if (samples.getWorldStates().size() == 0) {
			Utils.waitHere("This code shouldn't be called anymore as we check for marginalizeAll before.");
			getProbabilities(allExs);
			return;
		}
		for (int i = 0; i < samples.getWorldStates().size(); i++) {
			getProbabilitiesUsingSample(samples.getWorldStates().get(i), allExs);
			double currWorldProb = samples.getProbabilities().get(i);
			for (int j = 0; j < allExs.size(); j++) {
				RegressionRDNExample ex = allExs.get(j);
				ProbDistribution newDistr = new ProbDistribution(ex.getProbOfExample());
				newDistr.scaleDistribution(currWorldProb);
				if (exProb.get(j) != null && newDistr.isHasDistribution() != exProb.get(j).isHasDistribution()) {
					Utils.waitHere("Mismatch between example distributions for " + ex.toString() + " distr:" + newDistr.isHasDistribution());
				}
				if (exProb.get(j) != null) {
					newDistr.addDistribution(exProb.get(j));
				}
				
				exProb.set(j, newDistr);
			}
			if (i % 100 == 99) {
				Utils.println("done with #" + (i + 1) + " samples.");
			}
		}
		for (int j = 0; j < allExs.size(); j++) {
			RegressionRDNExample ex = allExs.get(j);
			ex.setProbOfExample(exProb.get(j));
		}
	}

	/**
	 * set the probability of the examples using the worldState as facts
	 */
	private void getProbabilitiesUsingSample(HiddenLiteralState worldState,
		List<RegressionRDNExample> allExs) {
		updateFactsFromState(setup, worldState);
		getProbabilities(allExs);
	}

	public static void updateFactsFromState(WILLSetup setup, HiddenLiteralState worldState) {
		for (Literal posEx : worldState.getPosExamples()) {
			
			if (posEx.predicateName.name.startsWith(WILLSetup.multiclassPredPrefix)) {
				RegressionRDNExample mcRex = (RegressionRDNExample)posEx;
				int maxVec = mcRex.getOutputVector().length;
				int assign = worldState.getAssignment((Example)posEx);
				if (assign < 0 || assign >= maxVec) { Utils.waitHere("Assignment: " + assign + " not within bound: " + maxVec);}
				for (int i = 0; i < maxVec; i++) {
					Example eg =  setup.getMulticlassHandler().createExampleFromClass(mcRex, i);
					if (i == assign) {
						addAsPosFact(eg, setup);
					} else {
						addAsNegFact(eg, setup);
					}
				}
			} else {
				addAsPosFact(posEx, setup);
			}
		}
		for (Literal negEx : worldState.getNegExamples()) {
			addAsNegFact(negEx, setup);
		}
	}

	private static  void addAsNegFact(Literal negEx, WILLSetup setup) {
		if (setup.allowRecursion) {
			Literal lit = setup.getHandler().getLiteral(setup.getHandler().getPredicateName(
					WILLSetup.recursivePredPrefix + negEx.predicateName.name), negEx.getArguments());
			setup.removeFact(lit);
		}
		setup.removeFact(negEx);
	}

	private static void addAsPosFact(Literal posEx, WILLSetup setup) {
		if (setup.allowRecursion) {
			Literal lit = setup.getHandler().getLiteral(setup.getHandler().getPredicateName(
					WILLSetup.recursivePredPrefix + posEx.predicateName.name), posEx.getArguments());
			setup.addFact(lit);
		}
		setup.addFact(posEx);
	}

	public void getMarginalProbabilities(Map<String, List<RegressionRDNExample>> jointExamples) {
		for (List<RegressionRDNExample> examples : jointExamples.values()) {
			getProbabilities(examples);
		}
	}

	/**
	 * Returns true, if the predicate is using recursion.
	 */
	protected boolean isRecursive(String target) {
		return rdn.isRecursive(target);
	}

	/**
	 * 
	 * @param target predicate name to evaluate for
	 * @return true, if the target predicate has no query ancestors.
	 */
	protected boolean hasNoTargetParents(String target) {
		return (rdn.getAncestorsOfType(target, PredicateType.QUERY).size() == 0);
	}

	/**
	 * @return the rdn
	 */
	public RelationalDependencyNetwork getRdn() {
		return rdn;
	}
	
}
