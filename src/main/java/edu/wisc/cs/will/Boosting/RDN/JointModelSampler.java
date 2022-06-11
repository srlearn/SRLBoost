package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.RDN.Models.DependencyNetwork;
import edu.wisc.cs.will.Boosting.RDN.Models.RelationalDependencyNetwork;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.*;

/*
 * The class sets the probability of examples, given a joint RDN model (i.e. RDN model
 * for each predicate). 
 * 
 * @author Tushar Khot
 *
 */
public class JointModelSampler extends SRLInference {

	JointModelSampler(JointRDNModel model, WILLSetup setup) {
		super(setup);
		this.jointModel   = model;
		this.setup   = setup;
		// Use the model to obtain the RDN structure
		rdn = new RelationalDependencyNetwork(model, setup);
	}

	/*
	 * This method computes the marginal probabilities of {@link RegressionRDNExample} by setting the 
	 * probOfExample in each example. Make sure to pass all possible groundings of the target predicates
	 * as it would be using Gibbs Sampling over these examples. If there is no recursion or dependencies
	 * between the target predicates, Gibbs sampling wont be used and it is safe to pass only some examples. 
	 * @param jointExamples - The set of examples for which we want to compute the probabilities
	 */
	public void getMarginalProbabilities(Map<String, List<RegressionRDNExample>> jointExamples) {
		Utils.println("\n% Starting getMarginalProbabilities.");
		sampleWorldStates(jointExamples);
	}
	
	private void sampleWorldStates(Map<String, List<RegressionRDNExample>> originalJointExamples) {
		// TODO(@hayesall): This appears to be the only method which uses `printNetwork`

		// Get the order of the predicates for Gibbs sampling.
		// We want to order predicates by the number of query/target predicate parents.
		// For e.g., if "sameBib" has two query predicates as parents, while "sameTitle" has only one
		// query predicate as parent, we should sample in the order {sameTitle, sameBib}.

		if (originalJointExamples.keySet().size() > 1) {
			throw new RuntimeException("Multiple targets is deprecated.");
		}

		Collection<String> orderedPredicates = originalJointExamples.keySet();

		// Print after getting the order, as we print the order in the DOT file too.
		String rdnDotFile = setup.cmdArgs.getModelDirVal() + "bRDNs/dotFiles/rdn.dot";
		printNetwork(rdn, rdnDotFile);

		// Making a copy of the original map, since we will update the map to handle multi-class examples. 
		// Only the map is copied, the examples are still the same. So careful while modifying the actual examples in jointExamples
		Map<String, List<RegressionRDNExample>> jointExamples = new HashMap<>(originalJointExamples);

		// Break into components for MAP inference
		sampleExampleProbabilities(jointExamples, orderedPredicates);

		// Remove all examples.
		removeAllExamples(originalJointExamples);

		updateProbabilitiesForInput(originalJointExamples, jointExamples);

	}

	private void sampleExampleProbabilities(
			Map<String, List<RegressionRDNExample>> jointExamples,
			Collection<String> orderedPredicates) {

		// TODO(hayesall): Most of this method related to sampling when there were multiple targets.

		Map<String,List<Example>>  posEgs = new HashMap<>();
		Map<String,List<Example>>  negEgs = new HashMap<>();

		for (String target : jointExamples.keySet()) {
			List<RegressionRDNExample> examples = jointExamples.get(target);

			posEgs.put(target, new ArrayList<>());
			negEgs.put(target, new ArrayList<>());
			if (examples.isEmpty()) {
				continue;
			}
			// Based on the current sampled state(which would have been randomly assigned in the 
			// RegressionRDNExample constructor), find out the current positive and negative examples.
			updatePosNegWithSample(target, examples, posEgs, negEgs);
		}

		for (String target : orderedPredicates) {
			// No examples for this predicate
			if (!jointExamples.containsKey(target)) {
				continue;
			}
			ConditionalModelPerPredicate mod = jointModel.get(target);

			/*
			 * If this query predicate doesn't have any query predicates as parents,
			 * we can just compute the probabilities based on evidence and hence we 
			 * don't need sampling.
			 * Also if there is only one query predicate, we don't need joint inference.
			 *
			 * TODO(hayesall): Assert there is always a single query predicate.
			 */

			List<RegressionRDNExample> examples = jointExamples.get(target);

			if (examples.isEmpty()) {
				continue;
			}
			setup.prepareFactsAndExamples(posEgs, negEgs, target, false);
			SRLInference sampler;

			sampler = new SingleModelSampler(mod, setup, jointModel);

			/*
			 * If we are using recursion for this target, tell SingleModelSampler to use Gibbs sampling
			 * for probabilities.
			 */
			sampler.getProbabilities(examples);
		}
	}

	private void updatePosNegWithSample(String target, List<RegressionRDNExample> examples,
										Map<String,List<Example>> posEgs, 
										Map<String,List<Example>> negEgs) {

		// All examples are passed in, so reset the example list.
		assert examples != null;

		if (examples.isEmpty()) {
			Utils.error("Expected non-null and non-empty example list");
		}

		posEgs.get(target).clear();
		negEgs.get(target).clear();

		List<Example> posList = posEgs.get(target);
		List<Example> negList = negEgs.get(target);

		for (RegressionRDNExample rex : examples) {
			if (!rex.predicateName.name.equals(target)) {
				Utils.error("Found example: '" + rex + "'\nwhile sampling for " + target);
			}
			if (rex.getSampledValue() == 1) {
				posList.add(rex);
			} else {
				negList.add(rex);
			}
		}
	}

	/*
	 * Writes the RDN to a DOT file. Use GraphViz to convert it to an image.
	 */
	private void printNetwork(DependencyNetwork dn, String filename) {
		try {
			Utils.ensureDirExists(filename);
			// Create a new file.
			BufferedWriter writer = new BufferedWriter(new CondorFileWriter(filename, false));
			dn.printNetworkInDOT(writer);
			writer.close();
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in printRDN.");
		}
	}

	private void updateProbabilitiesForInput(Map<String, List<RegressionRDNExample>> originalJointExamples,
											 Map<String, List<RegressionRDNExample>> jointExamples) {
		for (String target : jointExamples.keySet()) {
			int i = 0;
			// Store the example probabilities for the multi-class predicates.
			// These probabilities are used to fill the probabilities in the originalJointExamples
			for (RegressionRDNExample rex : jointExamples.get(target)) {
				originalJointExamples.get(target).get(i).setProbOfExample(rex.getProbOfExample());
				i++;
			}
		}
		
	}

	private void removeAllExamples(Map<String, List<RegressionRDNExample>> jointExamples) {
		for (String target : jointExamples.keySet()) {
			for (RegressionRDNExample eg : jointExamples.get(target)) {
				setup.removeFact(eg);
			}
		}
	}

	public void setMaxTrees(int j) {
		for (ConditionalModelPerPredicate model : this.jointModel.values()) {
			model.setNumTrees(j);
		}
	}

	@Override
	public ProbDistribution getExampleProbability(Example eg) {
		Utils.error("JointModelSampler can't return single example probability as it does sampling");
		return null;
	}
	
}
