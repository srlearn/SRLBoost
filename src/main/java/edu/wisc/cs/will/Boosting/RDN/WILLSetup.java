package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.Boosting.RDN.Models.RelationalDependencyNetwork;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.DataSetUtils.CreateSyntheticExamples;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings.VarIndicator;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ILP.*;
import edu.wisc.cs.will.ResThmProver.*;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.stdAIsearch.BestFirstSearch;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchStrategy;

import java.io.File;
import java.io.IOException;
import java.util.*;

/*
 *
 * @author shavlik
 * @author tushar
 */
public final class WILLSetup {

	// TODO(@hayesall): The `WILLSetup.outerLooper` ILPouterLoop is touched by quite
	// a few functions.
	private ILPouterLoop outerLooper;

	// These are meant for ease of access and should never be modified.
	// They can also be obtained by using outerLooper.
	private LearnOneClause innerLooper;
	private HandleFOPCstrings handler;
	private HornClauseContext context;
	private HornClauseProver prover;
	private MultiClassExampleHandler multiclassHandler;

	private Map<String, List<Example>> backupPosExamples;
	private Map<String, List<Example>> backupNegExamples;

	public boolean useMLNs = false;
	public boolean learnClauses = false;

	/**
	 * Cached list of predicate and arities for neighboring facts
	 */
	private List<PredicateNameAndArity> neighboringFactFilterList = null;
	
	public CommandLineArguments cmdArgs;
	public WILLSetup() { }

	private String getRunTypeMarker() {
		boolean learn = cmdArgs.isLearnVal();
		boolean infer = cmdArgs.isInferVal();
		
		if (learn && infer) { return "_learnPlusInfer"; } // Dribble files might overlap in this case.
		if (learn)          { return "_learn";          }
		if (infer)          { return "_infer";          }
		return                       "_runTypeIsUnknown";
	}

	public boolean setup(CommandLineArguments args, String directory, boolean forTraining) throws SearchInterrupted {

		this.cmdArgs = args;
		this.useMLNs = args.isLearnMLN();
		this.learnClauses = args.isLearningMLNClauses();

		Utils.Verbosity defaultVerbosity = Utils.Verbosity.Medium;

		// TODO(@hayesall): Providing a seed could be useful for replicating results.
		//	Utils.seedRandom((long) 12345); // Use this if we want to repeat runs exactly.

		Utils.seedRandom(System.currentTimeMillis() % 100000); // Only use the last few digits (though probably doesn't matter).  JWS
		Utils.setVerbosity(defaultVerbosity);

		File dir = new CondorFile(directory);

		if (!dir.isDirectory()) {
			throw new IllegalArgumentException("Unable to find task directory: " + directory + ".");
		}

		directory     = dir.getPath();
		String prefix = dir.getName();

		// Slice the '/' off the prefix if it was passed in with one ...
		if ( prefix.endsWith("/" ) ) {
			prefix = prefix.substring(0, prefix.length() - 1);
		}

		String[] file_paths = new String[4];

		file_paths[0] = directory + "/" + prefix + "_" + cmdArgs.getStringForTestsetPos()   + Utils.defaultFileExtensionWithPeriod;
		file_paths[1] = directory + "/" + prefix + "_" + cmdArgs.getStringForTestsetNeg()   + Utils.defaultFileExtensionWithPeriod;
		file_paths[3] = directory + "/" + prefix + "_" + cmdArgs.getStringForTestsetFacts() + Utils.defaultFileExtensionWithPeriod;
		file_paths[2] = directory + "/" + prefix + "_bk"                                    + Utils.defaultFileExtensionWithPeriod;

		String appendToPrefix="";
		if (forTraining && cmdArgs.getModelFileVal() != null) {
			appendToPrefix = cmdArgs.getModelFileVal();
		}
		if (!forTraining && cmdArgs.outFileSuffix != null) {
			appendToPrefix = cmdArgs.outFileSuffix;
		} else {
			if (!forTraining && cmdArgs.getModelFileVal() != null) {
				appendToPrefix = cmdArgs.getModelFileVal();
			}
		}

		// Try to place dribble files in the directory where RESULTS will go.
		String resultsDir = cmdArgs.getResultsDirVal();
		if (resultsDir == null) { resultsDir = directory + "/"; }

		Utils.createDribbleFile(resultsDir + prefix + getRunTypeMarker() + appendToPrefix  + "_dribble" + Utils.defaultFileExtensionWithPeriod);
		Utils.touchFile(        resultsDir + prefix + getRunTypeMarker() + appendToPrefix  + "_started" + Utils.defaultFileExtensionWithPeriod);
		createRegressionOuterLooper(file_paths, directory, prefix, cmdArgs.getSampleNegsToPosRatioVal(), cmdArgs.isLearnRegression() || cmdArgs.isLearnProbExamples());

		Utils.println("\n% Initializing the ILP inner looper.");
		getOuterLooper().initialize(false);

		Utils.println("% Old dir" + cmdArgs.getModelDirVal());
		if (cmdArgs.getModelDirVal() == null) {
			Utils.println("Setting model dir");	
			cmdArgs.setModelDirVal(getOuterLooper().getWorkingDirectory() + "/models/");
		}
		if (cmdArgs.getResultsDirVal() == null) { // Usually we want MODEL and RESULTS to be the same, but not if we're running on a fresh testset (i.e., one completely separate from the trainset).
			cmdArgs.setResultsDirVal(cmdArgs.getModelDirVal());
		}
		
		// Following code for non regression examples
		if (getInnerLooper().createdSomeNegExamples) {
			Example.writeObjectsToFile(file_paths[1], getInnerLooper().getNegExamples(), ".", "// Negative examples, including created ones.");
		}

		boolean bagOriginalNegExamples = false;

		// Should the examples be bagged upon reading them in?
		boolean bagOriginalPosExamples = false;
		if (cmdArgs.getBagOriginalExamples()) {
			bagOriginalPosExamples = true;
			bagOriginalNegExamples = true;
		}

		List<Literal> targets = getInnerLooper().targets;
		Set<Integer> arities = new HashSet<>(4);
		if (targets != null) for (Literal target : targets) { arities.add(target.getArity()); }

		// Use LIST since there can (legally) be duplicates.
		List<Example> posExamplesRaw = getOuterLooper().getPosExamples();
		List<Example> negExamplesRaw = getOuterLooper().getNegExamples() == null ? new ArrayList<>(): getOuterLooper().getNegExamples();
		List<Example> posExamples    = new ArrayList<>(posExamplesRaw.size());
		List<Example> negExamples    = new ArrayList<>(negExamplesRaw.size());
		
		if (targets != null) {
			for (Example pos : posExamplesRaw) {
				if (arities.contains(pos.getArity())) { 
					// If not in the list of targets, we would add to facts
					if (cmdArgs.getTargetPredVal().contains(pos.predicateName.name)) {
						posExamples.add(pos);
					} else {
						addFact(pos);
					}
				} else { 
					Utils.println(" Ignore this pos (arity not in " + arities + "): " + pos); 
				}
			}
			for (Example neg : negExamplesRaw) {
				if (arities.contains(neg.getArity())) {
					// If not in the list of targets, we would add to facts
					if (cmdArgs.getTargetPredVal().contains(neg.predicateName.name)) {
						negExamples.add(neg);
					}
				} else { 
					Utils.println(" Ignore this neg (arity not in " + arities + "): " + neg);
				}
			}

		} else {
			// If no targets (say because only testing and there are no positive examples), then simply accept all the examples.
			// If not in the list of targets, we would add to facts

			for (Example neg : negExamplesRaw) {
				// If not in the list of targets, we would add to facts
				if (cmdArgs.getTargetPredVal().contains(neg.predicateName.name)) {
					negExamples.add(neg);
				}
			}
		}

		Utils.println("\n% Have " + Utils.comma(posExamplesRaw) + " 'raw' positive examples and kept " + Utils.comma(posExamples) + ".");
		Utils.println(  "% Have " + Utils.comma(negExamplesRaw) + " 'raw' negative examples and kept " + Utils.comma(negExamples) + ".");

		// These shouldn't be RegressionRDNExamples. They are assumed to be "Example"s. 
		backupPosExamples = getExamplesByPredicateName(posExamples, forTraining && bagOriginalPosExamples); // Do bagging on the outermost loop.
		backupNegExamples = getExamplesByPredicateName(negExamples, forTraining && bagOriginalNegExamples);	// But only if TRAINING.
		// Needed to get examples from fact files.
		fillMissingExamples();

		// check if multi class trees are enabled.
		// We still create the multi class handler object
		multiclassHandler = new MultiClassExampleHandler();
		if (!cmdArgs.isDisableMultiClass()) {
			multiclassHandler.initArgumentLocation(this);
			for (String pred : backupPosExamples.keySet()) {
				multiclassHandler.addConstantsFromLiterals(backupPosExamples.get(pred));
				if (backupNegExamples.containsKey(pred)) {
					multiclassHandler.addConstantsFromLiterals(backupNegExamples.get(pred));
				}
			}
		}

		if (backupPosExamples != null) for (String target : backupPosExamples.keySet()) {
			Collection<Example> posegs = backupPosExamples.get(target);
			Collection<Example> negegs = backupNegExamples.get(target);

			// weigh the negative examples based on ratio of examples
			// If you have 10X negative examples, each negative example would be weighed 0.1
			// This is not the weight due to sampling. This is the weight to make large skews in 
			// data be equivalent to equal positive and negative examples. 
			// Weights are recalculated later if any sampling is done.

			double weightOnPosExamples = 1.0;
			if (Math.abs(weightOnPosExamples - 1.0) > 0.000001) for (Example pos : posegs) {
				pos.setWeightOnExample(weightOnPosExamples);
			}

			double weightOnNegExamples = 1.0;

			if (backupNegExamples != null && Math.abs(weightOnNegExamples - 1.0) > 0.000001) for (Example pos : negegs) {
				pos.setWeightOnExample(weightOnNegExamples);
			}
			Example.labelTheseExamples("#pos=", posegs);  // Used in comments only.
			Example.labelTheseExamples("#neg=", negegs);  // Used in comments only.
			Utils.println("\n% processing backup's for " + target +"\n%  POS EX = " + Utils.comma(posegs) +  "\n%  NEG EX = " + Utils.comma(negegs)	);
			
		}
		if (Utils.getSizeSafely(backupPosExamples) < 1) {
			if (Utils.getSizeSafely(backupNegExamples) < 1) { Utils.println("No pos nor neg examples!"); return false; }
		}
		
		if (cmdArgs.getDoInferenceIfModNequalsThis() >= 0) { // See if we have been requested to select a subset (e.g., because the test set is too large to run at once).
			int valueToKeep = cmdArgs.getDoInferenceIfModNequalsThis();
			int modN        = CommandLineArguments.modN;
			List<Example> new_posExamples = new ArrayList<>(posExamples.size() / Math.max(1, modN));
			List<Example> new_negExamples = new ArrayList<>(negExamples.size() / Math.max(1, modN));
			int counter = 0;
			
			for (Example ex : posExamples) { if (counter % modN == valueToKeep) { new_posExamples.add(ex); } counter++; }
			for (Example ex : negExamples) { if (counter % modN == valueToKeep) { new_negExamples.add(ex); } counter++; }
			
			Utils.println("% whenModEquals: valueToKeep = " + valueToKeep + ",  modN = " + modN + ",  counter = " + Utils.comma(counter) 
							+ "\n%  POS: new = " + Utils.comma(new_posExamples) +  " old = " + Utils.comma(posExamples)
							+ "\n%  NEG: new = " + Utils.comma(new_negExamples) +  " old = " + Utils.comma(negExamples)
							);
			
			posExamples = new_posExamples;
			negExamples = new_negExamples;
			getOuterLooper().setPosExamples(posExamples); // Set these in case elsewhere they are again gotten.
			getOuterLooper().setNegExamples(negExamples);
		}
		if (Utils.getSizeSafely(backupPosExamples) + Utils.getSizeSafely(backupNegExamples) < 1) {
			Utils.println("No pos nor neg examples after calling getDoInferenceIfModNequalsThis()!"); 
			return false; 
		}
		
		reportStats();

		// TODO(@hayesall): `recursion` seems to be false by default, but is also loaded in from the handler?
		String lookup = getHandler().getParameterSetting("recursion");
		if (lookup != null) {
			allowRecursion = Boolean.parseBoolean(lookup);
			Utils.println("Recursion set to:" + allowRecursion);
		}
		
		if (cmdArgs.getBagOriginalExamples()) { // DecisionForest Decision Forest DF DF df50
			Utils.waitHere("Is this still being used?");
			getOuterLooper().randomlySelectWithoutReplacementThisManyModes = 0.50; // TODO - allow this to be turned off (or the fraction set) when bagging.
		}
		return true;
	}

	/**
	 * This method moves facts to Examples if they are part of the joint inference task.
	 */
	private void fillMissingExamples() {
		Set<String> missingPositiveTargets = new HashSet<>();
		Set<String> missingNegativeTargets = new HashSet<>();
		for (String pred : cmdArgs.getTargetPredVal()) {
			// Make sure all targets have facts
			if (!backupPosExamples.containsKey(pred) ||
				 backupPosExamples.get(pred) == null ||
				 backupPosExamples.get(pred).isEmpty()) {
				Utils.println("% No pos ex for " + pred);
				missingPositiveTargets.add(pred);
			}
			// Make sure all targets have facts
			if (!backupNegExamples.containsKey(pred) ||
				backupNegExamples.get(pred) == null ||
				backupNegExamples.get(pred).isEmpty()) {
				Utils.println("% No neg ex for " + pred);
				missingNegativeTargets.add(pred);
			}
			// Initialize the hash map
			backupPosExamples.computeIfAbsent(pred, k -> new ArrayList<>());
			backupNegExamples.computeIfAbsent(pred, k -> new ArrayList<>());
		}

		if (missingPositiveTargets.isEmpty()) {
			return;
		}

		// These predicates are in facts.
		predicatesAsFacts.addAll(missingPositiveTargets);
		
		for (Literal lit : getContext().getClausebase().getFacts()) {

			String litPredicate = lit.predicateName.name;
			if (missingPositiveTargets.contains(litPredicate)) {

				// Telling WILL that this is an example.
				getInnerLooper().confirmExample(lit);
				
				RegressionRDNExample eg = new RegressionRDNExample(lit, true, "% Obtained from facts.");
				addExampleToMap(eg, backupPosExamples);
				if (!disableFactBase) {
					addedToFactBase.add(eg);
				}
			}
		}
		
		if (missingNegativeTargets.size() > 0) {
			// Update targetArgSpecs so that predicates are available for creating negatives.
			getInnerLooper().chooseTargetMode(true);
			
			for (int i = 0; i < getInnerLooper().getTargets().size(); i++) {
				String predName = getInnerLooper().getTargets().get(i).predicateName.name;
				//Utils.println("considering " + predName);
				if (missingNegativeTargets.contains(predName)) {
					// Only create negs for predicates completely missing from pos/neg or 
					// for any predicate missing negs iff createSyntheticexamples is enabled.
					if (missingPositiveTargets.contains(predName)) {
						Utils.println("Creating neg ex for: " + predName);
						List<Example> 
						negEgs = CreateSyntheticExamples.createAllPossibleExamples("% Negative example created from facts.",
									getHandler(), getProver(), getInnerLooper().getTargets().get(i),getInnerLooper().getTargetArgSpecs().get(i),
									getInnerLooper().getExamplePredicateSignatures().get(i), null,
								new ArrayList<>(backupPosExamples.get(predName)), null, null);
						assert negEgs != null;
						for (Example negEx : negEgs) {
							getInnerLooper().confirmExample(negEx);
						}
						backupNegExamples.put(predName, negEgs);
					}
				}
			}
		}
		// If no examples found, return
		for (String predName : cmdArgs.getTargetPredVal()) {
			if (missingPositiveTargets.contains(predName) && 
					(!backupPosExamples.containsKey(predName) || backupPosExamples.get(predName).isEmpty()) && 
				missingNegativeTargets.contains(predName) &&
					(!backupNegExamples.containsKey(predName) || backupNegExamples.get(predName).isEmpty())) {
				// Missing all examples of a particular type.

				String mesg = "No examples(positive & negative) found for predicate: " + predName;
				Utils.warning(mesg);
				return;
			}
		}
		// Update targetArgSpecs.
		getInnerLooper().chooseTargetMode(true);
	}

	private void addExampleToMap(Example eg, Map<String,List<Example>> exampleMap) {
		String litPredicate = eg.predicateName.name;
		if(!exampleMap.containsKey(litPredicate) ||	exampleMap.get(litPredicate) == null) {
			exampleMap.put(litPredicate, new ArrayList<>());
		}
		exampleMap.get(litPredicate).add(eg);
	}

	void reportStats() {
		Utils.println("\n% Memory usage by WILLSetup (just counts # targets?):");
		Utils.println("%  |backupPosExamples| = " + Utils.comma(backupPosExamples));
		Utils.println("%  |backupNegExamples| = " + Utils.comma(backupNegExamples));
		Utils.println("%  |predicatesAsFacts| = " + Utils.comma(predicatesAsFacts));
		Utils.println("%  |addedToFactBase|   = " + Utils.comma(addedToFactBase));
	}	
	
	public void prepareFactsAndExamples(String predicate) {
		prepareFactsAndExamples(backupPosExamples, backupNegExamples, predicate, true, null);
	}

	// TODO(@hayesall): It seems like a bug that `allowRecursion = false`.
	private boolean allowRecursion = false;
	public static final String recursivePredPrefix = "recursive_";
	static final String multiclassPredPrefix = "multiclass_";

	// Maintain a list of predicates that are already added, so that we can save on time.
	private final HashSet<String> predicatesAsFacts = new HashSet<>();
	private final HashSet<Literal> addedToFactBase  = new HashSet<>();
	private final boolean disableFactBase = true;
	
	private final Set<PredicateNameAndArity> backupTargetModes=new HashSet<>();

	void addAllTargetModes() {
		if (backupTargetModes.isEmpty()) {
			return;
		}
		
		for (PredicateNameAndArity mode : backupTargetModes) {
			getInnerLooper().addBodyMode(mode);
		}
		backupTargetModes.clear();
	}
	
	void prepareFactsAndExamples(Map<String, List<Example>> posEg,
								 Map<String, List<Example>> negEg,
								 String predicate, boolean forLearning,
								 String only_mod_pred) {

		if (allowRecursion || posEg.keySet().size() > 1 || negEg.keySet().size() > 1) {
			// JWS added the negEq check since we need to work with only NEG examples (ie, on an unlabeled testset).
			prepareFactsForJoint(posEg, negEg, predicate, only_mod_pred, forLearning);
		}
		prepareExamplesForTarget(posEg.get(predicate), negEg.get(predicate), predicate, forLearning);
		if (allowRecursion || posEg.keySet().size() > 1) {
			if (only_mod_pred != null) {
				recomputeFacts(predicate);
				recomputeFacts(recursivePredPrefix + predicate);
				recomputeFacts(only_mod_pred);
			} else {
				// Need to recompute all facts.
				for (String pred : cmdArgs.getTargetPredVal()) {
					recomputeFacts(recursivePredPrefix + predicate);
					recomputeFacts(pred);
				}
			}
		}
	}
	
	private RelationalDependencyNetwork rdnForPrecompute = null;
	private BoostingPrecomputeManager recomputer = null;
	// While doing joint inference, we may only precompute facts that influence some targets.
	private Set<String> onlyPrecomputeThese = null;
	
	void setOnlyPrecomputeThese(Set<String> precompute) {
		onlyPrecomputeThese = precompute;
	}

	private void recomputeFacts(String predicate) {
		if (onlyPrecomputeThese != null &&
			!onlyPrecomputeThese.contains(predicate)) {
			return;
		}
		if (rdnForPrecompute == null) {
			rdnForPrecompute = new RelationalDependencyNetwork(null, this);
			recomputer = new BoostingPrecomputeManager(this);
		}
		// Get the children for this predicate of type COMPUTED
		Collection<PredicateName> recomputeThese = rdnForPrecompute.getPredicatesComputedFrom(predicate);
		if(recomputeThese != null && recomputeThese.size() > 0) {
			ArrayList<PredicateName> orderedPrecomputes = getOrderOfPrecomputes(recomputeThese);
			for (PredicateName pName : orderedPrecomputes) {
				deleteAllFactsForPredicate(pName);
				recomputer.recomputeFactsFor(pName);
			}
		}
	}

	private ArrayList<PredicateName> getOrderOfPrecomputes(
			Collection<PredicateName> recomputeThese) {
		ArrayList<PredicateName> predicateNames=new ArrayList<>();
		// Creating a copy to make sure, we dont erase from original
		Set<PredicateName> inputPredicateNames = new HashSet<>(recomputeThese);
		FileParser parser = getInnerLooper().getParser();
		for (int i = 0; i < getInnerLooper().getParser().getNumberOfPrecomputeFiles(); i++) {
			List<Sentence> precomputeThese = parser.getSentencesToPrecompute(i);
			if (precomputeThese == null) {
				continue;
			}
			for (Sentence sentence : precomputeThese) {
				List<Clause> clauses = sentence.convertToClausalForm();
				if (clauses == null) {
					continue;
				}
				// Take each clause
				for (Clause clause : clauses) {
					if (!clause.isDefiniteClause()) { 
						Utils.error("Can only precompute Horn ('definite' actually) clauses.  You provided: '" + sentence + "'."); 
					}

					PredicateName headPredName = clause.posLiterals.get(0).predicateName;
					if(inputPredicateNames.contains(headPredName)) {
						predicateNames.add(headPredName);
						inputPredicateNames.remove(headPredName);
					}
				}
			}
		}
		return predicateNames;
	}

	private void deleteAllFactsForPredicate(PredicateName pName) {
		List<PredicateSpec> specs = pName.getTypeList();
		if (specs == null) {
			Utils.error("No specs for " + pName);
		}
		// Just take the first spec to get the number of arguments.
		int numArgs = specs.get(0).getArity();
		List<Term> args = new ArrayList<>();
		for (int i = 0; i < numArgs; i++) {
			String var = getHandler().convertToVarString("arg" + i);
			args.add(getHandler().getVariableOrConstant(var));
		}
		Literal pLit = getHandler().getLiteral(pName, args);
		Clause cl = getHandler().getClause(pLit, true);
		getContext().getClausebase().retractAllClausesWithUnifyingBody(cl);
		
	}

	public void prepareExamplesForTarget(String predicate) {
		prepareExamplesForTarget(backupPosExamples.get(predicate), backupNegExamples.get(predicate), predicate, true);
	}	
	
	private void prepareExamplesForTarget(List<Example> newPosEg,
										  List<Example> newNegEg,
										  String predicate,
										  boolean forLearning) {

		getOuterLooper().setPosExamples(new ArrayList<>(newPosEg));
		getOuterLooper().setNegExamples(new ArrayList<>(newNegEg));

		String prefix = null;

		if (forLearning) {

			if (multiclassHandler.isMultiClassPredicate(predicate)) {
				Utils.println("Morphing to regression vector");
				getOuterLooper().setLearnMultiValPredicates(true);
				morphToRegressionVectorExamples(newPosEg, cmdArgs.isLearnMLN() && cmdArgs.isLearningMLNClauses());
				prefix = WILLSetup.multiclassPredPrefix;
			} else {
				getOuterLooper().setLearnMultiValPredicates(false);
				// 	Move the examples into facts and get facts to predicates.
				getOuterLooper().morphToRDNRegressionOuterLoop(
						1,
						0,
						cmdArgs.getSampleNegsToPosRatioVal(),
						cmdArgs.getSamplePosProbVal(),
						cmdArgs.isLearnMLN() && cmdArgs.isLearningMLNClauses(),
						cmdArgs.reweighExamples,
						cmdArgs.isLearnRegression() || cmdArgs.isLearnProbExamples())
				;
			}

		}
		// Set target literal to be just one literal.
		getOuterLooper().innerLoopTask.setTargetAs(predicate, forLearning && cmdArgs.isJointModelDisabled(), prefix);
		handler.getPredicateName(predicate).setCanBeAbsent(-1);
	}
	/**
	 * No need for any sampling since only positive examples used.
	 */
	private void morphToRegressionVectorExamples(
			List<Example> newPosEg,
			boolean notLearnTrees) {

		// TODO(?): Subsample positives
		// TODO(?): allow weights for examples

		getOuterLooper().setFlagsForRegressionTask(notLearnTrees);
		List<Example> positiveExamples = new ArrayList<>(4);

		// Ignore the neg Eg since they are present as '0's in the regression vector

		for (Example example : newPosEg) {
			positiveExamples.add(multiclassHandler.morphExample(example));
		}
		
		getOuterLooper().setPosExamples(positiveExamples);
		getOuterLooper().setNegExamples(new ArrayList<>(0));
	}

	private Map<String,List<Example>> getExamplesByPredicateName(List<Example> examples, boolean createBootstrapSample) {
		// TODO(@TVK): remove the common stuff from `getJointExamples`

		Map<String,List<Example>> result = new HashMap<>();

		if (createBootstrapSample) {
			int numExamples = Utils.getSizeSafely(examples);
			for (int i = 0; i < numExamples; i++) {
				Example eg = examples.get(Utils.random0toNminus1(numExamples));
				String target = eg.predicateName.name; 
				if (!result.containsKey(target)) {
					result.put(target, new ArrayList<>());
				}
				result.get(target).add(eg);
			}
		} else {
			for (Example eg : examples) {
				String target = eg.predicateName.name; 
				if (!result.containsKey(target)) {
					result.put(target, new ArrayList<>());
				}
				result.get(target).add(eg);
			}
		}
		return result;
	}
	
	public HashMap<String,List<RegressionRDNExample>> getJointExamples(Set<String> targets) {
		// TODO(@hayesall): Large section of duplicated code, refactor.

		HashMap<String,List<RegressionRDNExample>> result = new HashMap<>();
		
		// TODO(?): Currently assuming they are marked as examples already.
		int counterPos = 0, counterNeg = 0;
		for (String pred : targets) {
			if (!result.containsKey(pred)) {
				result.put(pred, new ArrayList<>());
			}
			List<Example> lookupPos = backupPosExamples.get(pred);  Utils.println("\n% for " + pred + " |lookupPos| = " + Utils.comma(lookupPos));
			if (lookupPos != null) for (Example ex : lookupPos) {
				RegressionRDNExample rex = new RegressionRDNExample(getHandler(), ex.extractLiteral(), 1, ex.provenance, ex.extraLabel);
				if (cmdArgs.isLearnRegression()) {
					if (ex instanceof RegressionExample) {
						rex.originalRegressionOrProbValue = ((RegressionExample)ex).getOutputValue();
					} else {
						Utils.waitHere("Expected regression examples for learning regression trees");
					}
				}
				rex.setOriginalTruthValue(true);
				String target = ex.predicateName.name;
				if (targets.contains(target)) { 
					if (!result.containsKey(target)) {
						result.put(target, new ArrayList<>());
					}
					result.get(target).add(rex); counterPos++;

				} else {
					Utils.error("Didn't expect this example as target. Model absent: " + target);
				}
			}
			List<Example> lookupNeg = backupNegExamples.get(pred);  Utils.println("% for " + pred + " |lookupNeg| = " + Utils.comma(lookupNeg));
			if (lookupNeg != null) for (Example ex  : lookupNeg) {
				RegressionRDNExample rex = new RegressionRDNExample(getHandler(), ex.extractLiteral(), 0, ex.provenance, ex.extraLabel);
				rex.setOriginalTruthValue(false);
				if (cmdArgs.isLearnRegression()) {
					if (ex instanceof RegressionExample) {
						rex.originalRegressionOrProbValue = ((RegressionExample)ex).getOutputValue();
					} else {
						Utils.waitHere("Expected regression examples for learning regression trees");
					}
				}
				String target = ex.predicateName.name;
				if (targets.contains(target)) { 
					if (!result.containsKey(target)) {
						result.put(target, new ArrayList<>());
					}
					result.get(target).add(rex); counterNeg++;
				} else {
					Utils.error("Didn't expect this example as target. Model absent: " + target);
				}
			}	

		}

		Utils.println("% getJointExamples: |pos| = " + Utils.comma(counterPos) + ", |neg| = " + Utils.comma(counterNeg));
		return result;
	}

	private void prepareFactsForJoint(
			Map<String, List<Example>> posEg,
			Map<String, List<Example>> negEg,
			String predicate, String onlyModPred,
			boolean forLearning) {

		// to  be safe
		Set<String> newlyAddedPredicates = new HashSet<>();
		for (String target : posEg.keySet()) {
			if (target.equals(predicate)) {
				if (predicatesAsFacts.contains(target) && 
					disableFactBase && !allowRecursion) {
					System.currentTimeMillis();
					for (Example eg : posEg.get(target)) {
						removeFact(eg);
					}
					System.currentTimeMillis();
				} else {
					for (Example eg : posEg.get(target)) {
						// Remove this fact from clausebase.
						if (predicatesAsFacts.contains(target) && 
								disableFactBase) {
							removeFact(eg);
						}
						// add the recursive fact
						if (allowRecursion) {
							Literal lit = getHandler().getLiteral(handler.getPredicateName(recursivePredPrefix + eg.predicateName.name), eg.getArguments());
							if (disableFactBase) {
								addFact(lit);
							}
						}
					}
				}
			} else {
				for (Example eg : posEg.get(target)) {
					// Remove the recursion fact as this is not the target predicate
					if (allowRecursion) {
						Literal lit = getHandler().getLiteral(handler.getPredicateName(recursivePredPrefix + eg.predicateName.name), eg.getArguments());
						// if target predicate is set to null, we add the recursive fact as we want to add all examples as facts
						// for sampling hidden states
						if (predicate != null) {
							if (disableFactBase) {
								removeFact(lit);
							}
						} else {
							if (!disableFactBase) {
								addedToFactBase.add(lit);
							}
							addFact(lit);
						}
					} 

					if ((onlyModPred == null || eg.predicateName.name.equals(onlyModPred)) &&
						(!(predicatesAsFacts.contains(eg.predicateName.name) && forLearning)) && 
							disableFactBase) {
						addFact(eg);
					}
				}
				// update the set
				newlyAddedPredicates.add(target);
			}
		}
		for (String target : negEg.keySet()) {
			for (Example eg : negEg.get(target)) {
				if (!target.equals(predicate)) {
					// update the set
					newlyAddedPredicates.add(target);
				}
				// Either way remove this fact
				if (predicatesAsFacts.contains(eg.predicateName.name) &&
					(onlyModPred == null || eg.predicateName.name.equals(onlyModPred)) &&
						disableFactBase) {
					removeFact(eg);
				}
				if (allowRecursion) {
					Literal lit = getHandler().getLiteral(handler.getPredicateName(recursivePredPrefix + eg.predicateName.name), eg.getArguments());
					if (disableFactBase) {
						removeFact(lit);
					}
				}
			}
		}
		predicatesAsFacts.addAll(newlyAddedPredicates);
		// Remove the target as predicate
		if (predicate != null) {
			predicatesAsFacts.remove(predicate);
		}
	}

	public Clause convertFactToClause(String fact) {
		return getInnerLooper().getParser().parseDefiniteClause(fact);
	}

	Clause convertFactToClause(String fact, VarIndicator newVarIndicator) {
		VarIndicator oldVarIndicator = getHandler().getVariableIndicatorNoSideEffects();
		getHandler().setVariableIndicator(newVarIndicator);
		getHandler().keepQuoteMarks = false;
		Clause cl = getInnerLooper().getParser().parseDefiniteClause(fact);
		getHandler().setVariableIndicator(oldVarIndicator);
		return cl;
	}

	private void setOuterLooper(ILPouterLoop outerLooper) {
		this.outerLooper = outerLooper;
		this.innerLooper = outerLooper.innerLoopTask;
		this.handler     = outerLooper.innerLoopTask.getStringHandler();
		this.context     = outerLooper.innerLoopTask.getContext();
		this.prover      = outerLooper.innerLoopTask.getProver();
		neighboringFactFilterList = null;
	}

	public ILPouterLoop getOuterLooper() {
		return outerLooper;
	}

	public LearnOneClause getInnerLooper() {
		return innerLooper;
	}

	public HandleFOPCstrings getHandler() {
		return handler;
	}

	public HornClauseContext getContext() {
		return context;
	}

	void removeFact(Literal eg) {
		getContext().getClausebase().retractAllClausesWithUnifyingBody(eg);
	}

	void addFact(Literal eg) {
		getContext().getClausebase().assertFact(eg);
	}

	private HornClauseProver getProver() {
		return prover;
	}
	
	// Pulled out by JWS (7/8/10) so could be called elsewhere for a plain regression-tree learning.
	private void createRegressionOuterLooper(String[] newArgList, String directory, String prefix, double negToPosRatio, boolean isaRegressionTaskRightAway) {

		try {
			SearchStrategy         strategy = new BestFirstSearch();
			ScoreSingleClause        scorer = (cmdArgs.isLearnOCC() ? new ScoreOCCNode() :  new ScoreRegressionNode(cmdArgs.isLearnMLN()));

			// We're (sometimes) using A SMALL INDEX HERE, since the memory needs are already very large (i.e., trade off time for space).
			// We need to keep all the literals related to a specific proof (i.e., test of a hypothesis) around, but are willing to redo between proofs.
			// TODO(?): add 'runningLargeTask' to the passed-in arguments.

			// Need to set these BEFORE creating the LazyHornClausebase.
			LazyGroundNthArgumentClauseIndex.setMaximumIndexSize(100);
			LazyGroundClauseIndex.setMaximumIndexSize(           100);
					
			HandleFOPCstrings stringHandler = new HandleFOPCstrings(true); // Let the first file read set the default.  (Are libraries read first?)
			HornClausebase clausebase;
			clausebase = new LazyHornClausebase(stringHandler);

			HornClauseContext context = new DefaultHornClauseContext(clausebase);

			// TODO(?): `runningLargeTask`? Add to pass-in arguments?
			context.getStringHandler().variantFactHandling = VariantClauseAction.SILENTLY_KEEP_VARIANTS;
			context.getStringHandler().variantRuleHandling = VariantClauseAction.WARN_AND_REMOVE_VARIANTS;

			stringHandler.keepQuoteMarks                       = true;
			stringHandler.dontComplainIfMoreThanOneTargetModes = true;
			Utils.println("\n% Calling ILPouterLoop from createRegressionOuterLooper.");
			setOuterLooper(new ILPouterLoop(directory, prefix, newArgList, strategy, scorer, new Gleaner(), context, false, isaRegressionTaskRightAway));
			Utils.println("\n% The outer looper has been created.");
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Encountered a problem: " + e);
		}

        getInnerLooper().maxSearchDepth     =  10000;
		getInnerLooper().verbosity          =      0;

		getInnerLooper().maxNumberOfNewVars =      7;
		getInnerLooper().maxDepthOfNewVars  =      7;
		getInnerLooper().maxPredOccurrences =      5;
		getInnerLooper().restartsRRR        =     25;
		getOuterLooper().max_total_nodesExpanded = 10000000;
		getOuterLooper().max_total_nodesCreated  = 10 * getOuterLooper().max_total_nodesExpanded;
		getHandler().setStarMode(TypeSpec.minusMode);
		getInnerLooper().setMEstimatePos(0.1);
		getInnerLooper().setMEstimateNeg(0.1);
		getInnerLooper().setMaxNegCoverage(0.499);

		getInnerLooper().getProver().setMaxNodesToConsider(1000000);
		getInnerLooper().getProver().setMaxNodesToCreate( 10000000);

		// JWS: this is (sometimes) set high (multiple minutes), e.g. for a threshold calc for the breast-cancer dataset.
		getInnerLooper().getProver().setMaximumClockTimePerIterationInMillisec(300000);

		// Units are milliseconds.  So 3600000 = 1 hour.
		getInnerLooper().setMaximumClockTimePerIterationInMillisec(           7200000);

		// Sometimes we start out with a BOOLEAN task then later turn into a regression one.
		getInnerLooper().regressionTask = isaRegressionTaskRightAway;

		// This is a fraction of the current set of examples at the root.
		double minFractionOnBranches = Math.max(0.005, 0.05 / negToPosRatio);

		// If a set has less than this much VARIANCE per example, it will become a leaf.
		getOuterLooper().setMaxAcceptableNodeScoreToStop(0.0025);

		// If a recursive call involves fewer than this number of examples, make a leaf node (ALSO IMPACTS THE INITIAL CALL?)
		getOuterLooper().setOverallMinPosWeight(10);
		if (!cmdArgs.isLearnRegression() && !cmdArgs.isLearnProbExamples()) {
			getInnerLooper().setMinPosCoverageAsFraction(minFractionOnBranches);   // For a clause to be acceptable, it needs to cover at least this fraction of the examples (and not more than 1 minus this fraction).
		}

		// The next line overrides the one immediately above this comment.
		// Need to be careful here, since data might be quite skewed.  Should really be something like 10% of the majority category.
		getInnerLooper().setMinPosCoverage(3);

		if (!cmdArgs.isLearnRegression()) {
			// And cannot cover too many of the examples.
			getOuterLooper().setMaxRecallOfAcceptableClause(1 - minFractionOnBranches);
		}
		if (cmdArgs.isLearnMLN()) {
			getOuterLooper().setLearnMLNTheory(true);
		}

		// Since WILL focuses on seeds to filter out candidate clauses, we need a good number here because some seeds will go on the "false" branch.  Want to have enough so that on average can find the maximally acceptable skew for the true/false branches.  Or maybe OK to miss these to save time by having a smaller set of seeds?
		getOuterLooper().numberPosSeedsToUse = (int) Math.ceil(5 * negToPosRatio);
		// Only require ONE to be covered (other constraints will filter clauses).
		getInnerLooper().clausesMustCoverFractPosSeeds = 0.999999 / getOuterLooper().numberPosSeedsToUse;
		// Need to cover at least 1% of the examples, even if the root.
		getOuterLooper().setMinPrecisionOfAcceptableClause(0.001);
		getOuterLooper().setMaxNumberOfLiteralsAtAnInteriorNode(cmdArgs.getMaxLiteralsInAnInteriorNode());

		// Counting is from 0 (i.e., this is really "max number of ancestor nodes").  maxNumberOfClauses might 'dominate' this setting.
		getOuterLooper().setMaxTreeDepth(2);

		// This is the body of ONE node.  By allowing more bridgers that literals we can, say, create comparators between two extracted values.
		getOuterLooper().innerLoopTask.maxFreeBridgersInBody = 0;
		// Add 1 here since the root has literals but is at depth 0.
		// We don't want the individual trees to get too complicated, so limit to 4 literals (so if 2 lits per nodes and depth is 2, instead of a max of 6 literals, the limit of 4 will be used).
		// Recall there could be some bridgers at each interior node, so this is allowing some bridgers.
		getOuterLooper().setMaxTreeDepthInLiterals(Math.max(3, (getOuterLooper().getMaxTreeDepth() + 1) * (getOuterLooper().innerLoopTask.maxFreeBridgersInBody + getOuterLooper().getMaxNumberOfLiteralsAtAnInteriorNode())));

		// Reminder: "consider" means "expand" (i.e., remove from the OPEN list and generate its children);  "create" is a counter on children.
		int matLitsAtNode = cmdArgs.getMaxLiteralsInAnInteriorNode() + getOuterLooper().innerLoopTask.maxFreeBridgersInBody;
		// For reasons of time, don't want to expand too many nodes (does this setting matter if maxLits=1?).  Eg, expand the root, pick the best child, expand it, then pick the overall best unexpanded child, and repeat a few more times.
		getInnerLooper().setMaxNodesToConsider(matLitsAtNode > 1 ?     10 :     50);
		// This can be high since we want the # of expansions to be the limiting factor.
		getInnerLooper().setMaxNodesToCreate(  matLitsAtNode > 1 ?  10000 :  50000);
		// This is the maximum number of non-leaf nodes (tree building is via BEST-FIRST search).  MaxTreeDepth might 'dominate' this setting.
		getOuterLooper().maxNumberOfClauses =  matLitsAtNode > 1 ?     12 :     16 ;
		getOuterLooper().maxNumberOfCycles  =     2 * getOuterLooper().maxNumberOfClauses;

		if (cmdArgs.isLearnRegression()) {
			// This should be zero since we really don't have any negatives here (we instead are doing regression).
			getInnerLooper().minNumberOfNegExamples = 0;
		} else {
			// TVK : This SHOULDN'T be zero here, it is set later in morph. This is used to create negative examples.
			getInnerLooper().minNumberOfNegExamples = 10;
		}

		getInnerLooper().fractionOfImplicitNegExamplesToKeep = 1;
		// Other constraints say that at least half the examples must be covered, and sometimes we need to use the negation to do that.

		// TODO(?): is this time PER TREE?  I think so ...
		// TODO(?): determine if when time runs out, a reasonable model results. JWS: I think that sometimes timing out makes a NOT_* seem better than it should.
		double maxHoursToRunPerTree = getOuterLooper().getMaxTreeDepth() * 4.0;
		// TODO - should also have a maxTime for learning ALL N trees.  Maybe write the remaining trees as adding zero to the wgt'ed sum, since other code looks for maxTrees.
		getOuterLooper().setMaximumClockTimeInMillisec((long) (maxHoursToRunPerTree * 60 * 60 * 1000));
	}

	void getListOfPredicateAritiesForNeighboringFacts() {
		if (neighboringFactFilterList == null) {
			Set<PredicateNameAndArity> pars = new HashSet<>();
			String lookup;
			boolean addAllModes = true;
			if ((lookup =  getHandler().getParameterSetting("useAllBodyModesForNeighboringFacts")) != null) {
				addAllModes = Utils.parseBoolean(lookup);
			}
			if (addAllModes) {
				pars.addAll(BoostingUtils.convertBodyModesToPNameAndArity(getInnerLooper().getBodyModes()));
			}
			if ((lookup =  getHandler().getParameterSetting("includePredicatesForNeighboringFacts")) != null) {
				lookup = lookup.replaceAll("\"", "");
				List<String> preds = Utils.parseListOfStrings(lookup);
				for (String pred : preds) {
					pars.addAll(convertStringToPnameArity(pred));
				}
			}
			if ((lookup =  getHandler().getParameterSetting("excludePredicatesForNeighboringFacts")) != null) {
				lookup = lookup.replaceAll("\"", "");
				List<String> preds = Utils.parseListOfStrings(lookup);
				for (String pred : preds) {
					pars.removeAll(convertStringToPnameArity(pred));
				}
			}
			neighboringFactFilterList = new ArrayList<>(pars);
		}
	}
	
	private List<PredicateNameAndArity> convertStringToPnameArity(String pname) {
		String[] parts = pname.split("/");
		List<PredicateNameAndArity> pars = new ArrayList<>();
		// Arity given
		if (parts.length > 1) {
			String pred = parts[0];
			int arity = Integer.parseInt(parts[1]);
			pars.add(new PredicateNameAndArity(getHandler().getPredicateName(pred), arity));
		} else {

			PredicateName predicate = getHandler().getPredicateName(parts[0]);
			// For each spec for the predicate
			for (PredicateSpec spec : predicate.getTypeList()) {
				if (spec.getTypeSpecList() != null) {
					int arity = spec.getTypeSpecList().size();
					PredicateNameAndArity par = new PredicateNameAndArity(predicate, arity);
					if (!pars.contains(par)) {
						pars.add(par);
					}
				}
			}
		}
		return pars;
	}

	void getBitMaskForNeighboringFactArguments(String target) {
		// TODO(@hayesall): This is only used by `InferBoostedRDN`.
		String lookup;
		if ((lookup =  getHandler().getParameterSetting("bitMaskForNeighboringFactArgsFor" + target)) != null) {
			lookup = lookup.replaceAll("\"", "");
			Utils.parseListOfStrings(lookup);
		}
	}

	/**
	 * @return the multiclassHandler
	 */
	MultiClassExampleHandler getMulticlassHandler() {
		return multiclassHandler;
	}

}
