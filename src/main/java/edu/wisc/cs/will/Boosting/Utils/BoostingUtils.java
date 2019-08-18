package edu.wisc.cs.will.Boosting.Utils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.Boosting.Advice.AdviceReader;
import edu.wisc.cs.will.Boosting.EM.HiddenLiteralSamples;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.RunBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.Trees.RegressionMLNModel;
import edu.wisc.cs.will.Boosting.Trees.RegressionTree;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConsCell;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.ResThmProver.DefaultProof;
import edu.wisc.cs.will.ResThmProver.Proof;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;

/*
 * @author Tushar Khot
 *
 */
public class BoostingUtils {

	public static List<Example> convertToListOfExamples(List<RegressionRDNExample> examples) {
		if (examples == null) { return null; }
		List<Example> results = new ArrayList<>(examples.size());
		results.addAll(examples);
		return results;
	}

	public static List<RegressionRDNExample> castToListOfRegressionRDNExamples(List<Example> examples) {
		if (examples == null) { return null; }
		List<RegressionRDNExample> results = new ArrayList<>(examples.size());
		for (Example ex : examples) { results.add((RegressionRDNExample)ex); }
		return results;
	}
	
	public static RegressionValueOrVector getRegressionValueOrVectorFromTerm(Term leafTerm) {
		if (leafTerm instanceof NumericConstant) {
			return new RegressionValueOrVector(((NumericConstant) leafTerm).value.doubleValue());
		}
		if (leafTerm instanceof ConsCell) {
			ConsCell valarray = (ConsCell)leafTerm;
			double[] regVec = new double[valarray.length()];
			int index = 0;
			for (Term term : valarray) {
				double val  = ((NumericConstant) term).value.doubleValue();
				regVec[index++] = val;
			}
			return new RegressionValueOrVector(regVec);
		}
		Utils.error("Uknown type of constant in leaf: " + leafTerm.toPrettyString());
		return null;
	}

	public static String getLabelForModelNumber(int modelNumber) {
		return (modelNumber > 0 ? "Model" + modelNumber : ""); // Model 0 is only implicitly named, in case we only want one model.
	}

	public static String getLabelForCurrentModel() {
		return RunBoostedRDN.nameOfCurrentModel == null ? "" : "_" + RunBoostedRDN.nameOfCurrentModel;
	}

	public static String getLabelForResultsFileMarker() {
		return RunBoostedRDN.resultsFileMarker  == null ? "" : "_" + RunBoostedRDN.resultsFileMarker;
	}

	public static String getModelFile(CommandLineArguments cmdArgs, String target, boolean includeExtension) {
		String filename = cmdArgs.getModelDirVal() + "bRDNs/" + target;
		if (cmdArgs.getModelFileVal() != null) {
			 filename += "_" + cmdArgs.getModelFileVal();
		}
		filename += getLabelForCurrentModel() + (includeExtension ? ".model" : "");
		Utils.ensureDirExists(filename);
		return filename;
	}

	public static List<PredicateNameAndArity> convertBodyModesToPNameAndArity(Set<PredicateNameAndArity> pnames) {
		List<PredicateNameAndArity> pars = new ArrayList<>();
		for (PredicateNameAndArity predicate : pnames) {
			// For each spec for the predicate
			for (PredicateSpec spec : predicate.getPredicateName().getTypeList()) {
				if (spec.getTypeSpecList() != null) {
					int arity = spec.getTypeSpecList().size();
					PredicateNameAndArity par = new PredicateNameAndArity(predicate.getPredicateName(), arity);
					// TODO(TVK) use a set.
					if (!pars.contains(par)) {
						pars.add(par);
					}
				}
			}
		}
		return pars;
	}
	

	public static Set<Literal> getRelatedFacts(Term input, List<PredicateNameAndArity> allPredicates,
										LearnOneClause learnClause) {
		Set<Literal> relatedFacts = new HashSet<>();
		HandleFOPCstrings handler = learnClause.getStringHandler();

		// For each predicate
		for (PredicateNameAndArity predicateArity : allPredicates) {
			// not_predicate()  always would return true and should be ignored.
			// TODO Find a better way to handle this case
			if (predicateArity.getPredicateName().name.contains("not_")) {
				continue;
			}

			List<Term> args = new ArrayList<>();
			// For each argument 
			for (int i = 0; i < predicateArity.getArity(); i++) {
				args.add(handler.getGeneratedVariable(handler.convertToVarString("Arg" + i), true));
			}

			// Now try putting the term as an argument at every location.
			for (int i = 0; i < args.size(); i++) {
				Term bkup = args.get(i);
				Literal query = handler.getLiteral(predicateArity.getPredicateName(), args);

				BindingList bl = new BindingList();
				bl.addBinding((Variable)bkup, input);

				Literal boundQuery = query.applyTheta(bl);
				BindingList proofBindings;
				Proof proof = new DefaultProof(learnClause.getContext(), boundQuery );

				// Every call to prove() will return the next possible
				// SLD resolution's BindingList, or null if there 
				// are no more resolutions.

				while (  ( proofBindings = proof.prove() ) != null ) {
					// Here proofBindings will contains the bindings 
					// for all the free variables if the proof succeeded.
					// If you just need the binding of the variable, you have them.
					// If you want the full literal, just apply the bindings to the boundQuery.
					Literal boundResult = boundQuery.applyTheta(proofBindings);
					if (!boundResult.containsVariables()) {
						relatedFacts.add(boundResult);
					}
				}
			}
		}

		return relatedFacts;
	}

	public static double sigmoid(double numRegExp, double denoRegExp) {
		return 1/ (Math.exp(denoRegExp - numRegExp) + 1);
	}

	public static String getCheckPointFile(String saveModelName) {
		return saveModelName + ".ckpt";
	}

	public static String getCheckPointExamplesFile(String saveModelName) {
		return saveModelName + ".ckptEgs";
	}

	public static String getCheckPointFlattenedLitFile(String saveModelName) {
		return saveModelName + ".ckptLits";
	}

	public static double computeHiddenStateCLL(
			HiddenLiteralSamples sampledStates,
			Map<String, List<RegressionRDNExample>> hiddenExamples) {
		double cll=0;
		double counter = 0;
		double accuracyCounter = 0;
		double correct = 0;
		for (String predName : hiddenExamples.keySet()) {
			for (RegressionRDNExample eg : hiddenExamples.get(predName)) {
				ProbDistribution probDist = sampledStates.sampledProbOfExample(eg);
				double prob;
				if (probDist.isHasDistribution()) {
					double[] probs = probDist.getProbDistribution();
					
					int mostLikelyState = -1;
					double highestProb = 0.0; 
					for (int i = 0; i < probs.length; i++) {
						if (probs[i] > highestProb) {
							highestProb = probs[i];
							mostLikelyState = i;
						}
						if (eg.getOriginalHiddenLiteralVal() == i) {
							prob = probs[i];
						} else {
							prob = 1 - probs[i];
						}
						if (prob == 0) {
							prob = 1e-5;
						}
						cll += Math.log(prob);
						counter++;
					}
					if (mostLikelyState == eg.getOriginalHiddenLiteralVal()) {
						correct++;
					}
					accuracyCounter++;
				} else {
					prob = probDist.getProbOfBeingTrue();
					if (eg.getOriginalHiddenLiteralVal() == 0) {
						// False example with true prob < 0.5 ?
						if (prob < 0.5) {
							correct++;
						}
						prob = 1-prob;
					} else {
						// True example with true prob >= 0.5
						if (prob >= 0.5) {
							correct++;
						}
					}
					if (prob == 0) {
						prob = 1e-5;
					}
					cll += Math.log(prob);
					counter++;
					accuracyCounter++;
				}
				
			}
		}
		Utils.println("Hidden data accuracy: " + (correct / accuracyCounter) + " (" + correct + "/" + accuracyCounter + ").");
		return cll/counter;
		
	}
	
	
	
}
