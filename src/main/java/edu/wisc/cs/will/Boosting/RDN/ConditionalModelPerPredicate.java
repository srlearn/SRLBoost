package edu.wisc.cs.will.Boosting.RDN;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.Boosting.RDN.MultiClassExampleHandler.ConstantLookupList;
import edu.wisc.cs.will.Boosting.Trees.ClauseBasedTree;
import edu.wisc.cs.will.Boosting.Trees.RegressionMLNModel;
import edu.wisc.cs.will.Boosting.Trees.RegressionTree;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings.VarIndicator;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;

// TODO(@hayesall): There are a large number of private variables and getters/setters scattered around this file.

public class ConditionalModelPerPredicate implements Serializable {

	// Used to control output from this class (0 = no output, 1=some, 2=much, 3=all).
	protected final static int debugLevel = 1;

	private static final long serialVersionUID = 9130108889576097786L;

	/**
	 *  Prior log probability i.e. \psi_0
	 */
	private double log_prior = -1.8;

	/**
	 *  List of boosted trees
	 */
	private List<RegressionTree[]> boostedTrees;

	/**
	 *  Number of trees. Generally numTrees would be the same as the boostedTrees size but one can reduce this.
	 */
	private int numTrees;

	/**
	 *  Step length for gradient.
	 *  All models in a array of RegressionTree[] have the same stepLength.
	 */
	private List<Double> stepLength;

	/**
	 * Predicate for which model is learnt.
	 */
	private String targetPredicate;

	/**
	 * Prefix for every tree used while storing the tree.
	 * Generally set to the targetPredicate 
	 */
	private String treePrefix;

	/**
	 * Set to true, if the model just has a set of rules that do the combination
	 */
	private boolean hasSingleTheory;

	/**
	 * Needed only with single theory as it stores the clauses 
	 */
	private WILLSetup setup;

	/**
	 * Save the constants for this predicate, if multiclass
	 */
	private ConstantLookupList constList = null;

	/**
	 * Sentences associated with theory. Needed only with hasSingleTheory.
	 */
	private List<Sentence> theory;

	private RegressionTree prior_advice;

	public ConditionalModelPerPredicate(WILLSetup willsetup) {	
		boostedTrees = new ArrayList<>(4);
		stepLength = new ArrayList<>(4);
		numTrees = 0;
		treePrefix = "";
		hasSingleTheory = false;
		setup = willsetup;
		theory = null;
		prior_advice = null;
	}

	/**
	 * Calculates the regression value for an example based on the model.
	 * Mostly one shouldn't have to use this but should directly use returnModelProbability.
	 * @param ex Example to evaluate
	 * @return the regression value for the example
	 */
	public RegressionValueOrVector returnModelRegression(Example ex) {
		if (hasSingleTheory) {
			return regressionValueFromTheory(ex); // TODO - need to handle multiple theories (will need to write out more).
		}
		RegressionValueOrVector total_sum_grad;
		RegressionRDNExample rex = (RegressionRDNExample)ex;
		if (rex.isHasRegressionVector()) {
			double[] regs = new double[rex.getOutputVector().length];
			Arrays.fill(regs, 0);
			total_sum_grad = new RegressionValueOrVector(regs);
		} else {
			total_sum_grad = new RegressionValueOrVector(0.0);
		}

		int counter = 0;
		
		// First add the prior advice regression values
		if (prior_advice != null) {
			total_sum_grad.addValueOrVector(prior_advice.getRegressionValue(ex));
		}
		for (RegressionTree[] tree : boostedTrees) {
			if (counter == numTrees) { break; }
			
			RegressionValueOrVector sum_grad = null;

			for (int i = 0; i < RunBoostedRDN.numbModelsToMake; i++) {
				if (setup == null) { Utils.error("WILLSetup object not initialized"); } 
				if (setup.cmdArgs.isPrintingTreeStats()) {
					tree[i].setAddLeafId(true);
				}

				RegressionValueOrVector thisValue = tree[i].getRegressionValue(ex);
				thisValue.multiply(stepLength.get(counter));
				
				if (sum_grad == null) {
					sum_grad = thisValue;
				} else {
					sum_grad.addValueOrVector(thisValue);
				}
			}
			sum_grad.multiply(1/RunBoostedRDN.numbModelsToMake);
			total_sum_grad.addValueOrVector(sum_grad);
			counter++;
		}
		return total_sum_grad;
	}

	private RegressionValueOrVector regressionValueFromTheory(Example ex) {
		HandleFOPCstrings handler = setup.getHandler();
		String totalStr    = handler.convertToVarString("Total");
		Term numTreeTerm = handler.getVariableOrConstant(Integer.toString(numTrees));
		Term totalVarTerm = handler.getVariableOrConstant(totalStr); 
		ex.addArgument(totalVarTerm);
		
		StringBuilder argsString  = new StringBuilder();
		// The error checking whether this matches the target predicate is done in addPrologCodeForUsingAllTrees
		List<Literal> targets = setup.getInnerLooper().getTargets();
		Literal       target  = null;
		if (Utils.getSizeSafely(targets) == 1) { target = targets.get(0); } else { Utils.error("Should only have one target.  Have: " + targets); }

		for (int i = target.numberArgs() - 1; i >= 0; i--) {
			argsString.insert(0, target.getArgument(i) + ", ");
		}
		String clauseStr = targetPredicate +"(" + argsString + totalVarTerm +") :- " + targetPredicate + "(" + argsString + numTreeTerm +", " + totalVarTerm + ").";
		 
		Clause clause = setup.convertFactToClause(clauseStr);

		BindingList list = setup.getInnerLooper().proveExampleAndReturnBindingList(clause, ex);
		Term y = list.lookup((Variable)totalVarTerm);
		
		ex.removeArgument(totalVarTerm);
		
		return BoostingUtils.getRegressionValueOrVectorFromTerm(y);
		
	}


	public RegressionValueOrVector returnModelRegressionWithPrior(Example ex) {
		RegressionValueOrVector modelRegression =  returnModelRegression(ex);
		modelRegression.addScalar(log_prior);
		return modelRegression;
	}

	/**
	 * Returns the probability of the example
	 * @param ex input example
	 * @return probability of the example being true
	 */
	ProbDistribution returnModelProbability(Example ex) {
		RegressionValueOrVector sum_grad = returnModelRegressionWithPrior(ex);
		return new ProbDistribution(sum_grad);
	}

	/**
	 * This function adds the predicates that are used in this model,
	 * i.e., the parents for the target predicate.
	 * @param preds - Adds the parent predicate to this collection
	 * Duplicate detection is responsibility of the caller
	 */
	public void getParentPredicates(Collection<PredicateName> preds) {
		if(prior_advice != null) {
			prior_advice.getParentPredicates(preds);
		}
		for (RegressionTree[] regTree : boostedTrees) {
			for (int i = 0; i < RunBoostedRDN.numbModelsToMake; i++) {
				regTree[i].getParentPredicates(preds);
			}
		}
	}

	/**
	 * Saves the model in the given file
	 * NOTE: the trees are stored in different files but their 
	 * filename prefix is stored in the model
	 * @param filename name to save model as
	 */
	public void saveModel(String filename) {
		if (hasSingleTheory) {
			Utils.println("% Model already saved so saveModel('" + filename + "') no needed.");
			return;
		}

		Utils.println("% Saving model in: " + filename);
		Utils.ensureDirExists(filename);
		try {
			BufferedWriter writer = new BufferedWriter(new CondorFileWriter(filename, false));
			writer.write(Integer.toString(numTrees));
			writer.newLine();
			writer.write(treePrefix);
			writer.newLine();
			writer.write(stepLength.toString());
			writer.newLine();
			writer.write(Double.toString(log_prior));
			writer.newLine();
			writer.write(targetPredicate);
			writer.newLine();
			// constants
			if (setup.getMulticlassHandler().isMultiClassPredicate(targetPredicate)) {
				String line = setup.getMulticlassHandler().constantsForPredicate.get(targetPredicate).toString();
				writer.write(line);
				writer.newLine();
				// Also store it for the inference task
				constList = setup.getMulticlassHandler().constantsForPredicate.get(targetPredicate);
			}
			
			// Now save the trees.
			for (int i = 0; i < numTrees; i++) {
				for (int modelNumber = 0; modelNumber < RunBoostedRDN.numbModelsToMake; modelNumber++) {
					boostedTrees.get(i)[modelNumber].saveToFile(getTreeFilename(filename, treePrefix, i, modelNumber)); 
				}
			}
			writer.close();	
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("saveMode: IO exception");
		}
	}

	/**
	 * Loads the model from a given file
	 */
	public void loadModel(String filename, WILLSetup setup, int loadMaxTrees) {
		if (hasSingleTheory) {
			numTrees=loadMaxTrees;
			List<Sentence> sentences = setup.getInnerLooper().getParser().readFOPCfile(filename);
			theory = null;
			addSentences(sentences);
			return;
		}
	
		try {
			BufferedReader reader = new BufferedReader(new CondorFileReader(filename));
			String line;

			// Number of trees
			line = reader.readLine();
			int numberOfTrees = Integer.parseInt(line);
			
			// Only limit trees if >= 0
			if (loadMaxTrees >= 0) {
				// Make sure the numberOfTrees >= loadMaxTrees
				if (numberOfTrees < loadMaxTrees) {
					Utils.error("Number of trees in the model (" + numberOfTrees + ") is less than the trees to be loaded (" + loadMaxTrees + ").\nFile: " + filename);
				} else {
					if (numberOfTrees > loadMaxTrees) {
						Utils.println("Model had " + numberOfTrees + " trees but loading only " + loadMaxTrees);
					}
				}
				numberOfTrees = loadMaxTrees;
			}
			
			// Prefix for boosted trees
			line = reader.readLine();
			treePrefix = line;
			// Step length
			line = reader.readLine();
			//first remove the []
			line = line.replace("[", "");
			line = line.replace("]", "");
			// Split into strings
			String[] lengths = line.split(",");
			for (String len : lengths) {
				stepLength.add(Double.parseDouble(len)); 
			}
			// Log prior
			line = reader.readLine();
			log_prior = Double.parseDouble(line);
			// target predicate
			line = reader.readLine();
			targetPredicate = line;
			
			// For multi-class predicate, read constant list
			if (setup.getMulticlassHandler().isMultiClassPredicate(targetPredicate)) {
				line =  reader.readLine();
				if (line == null || line.isEmpty()) {
					Utils.error("Expected constants being specified in the model file: " + filename);
				} else {
					ConstantLookupList newConstList = new MultiClassExampleHandler.ConstantLookupList();
					newConstList.load(setup, line);
					setup.getMulticlassHandler().updateConstantList(targetPredicate, newConstList);
				}
				
			}

			for (int i = 0; i < numberOfTrees; i++) {
				for (int modelNumber = 0; modelNumber < RunBoostedRDN.numbModelsToMake; modelNumber++) {
					RegressionTree tree;
					if (setup.useMLNs) {
						tree = new RegressionMLNModel(setup);
					} else {
						tree = new RegressionTree(setup);
					}
					String fileToLoad = getTreeFilename(filename, treePrefix, i, modelNumber);
					Utils.println("%   loadModel (#" + Utils.comma(i) + "): " + fileToLoad);
					tree.loadFromFile(fileToLoad);
					addTree(tree, stepLength.get(i), modelNumber);
				}
				updateSetOfTrees();
			}
			reader.close();
			Utils.println("%  Done loading " + Utils.comma(numberOfTrees) + " models.");
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem encountered reading model:\n " + filename);
		}
	}

	private String getTreeFilename(String modelFile, String prefix, int i, int modelNumber) {
		int lastPos = modelFile.lastIndexOf('/');
		String path = modelFile.substring(0, lastPos + 1); 
		path += "Trees/" + prefix + BoostingUtils.getLabelForCurrentModel() + "Tree" + i + BoostingUtils.getLabelForModelNumber(modelNumber) + ".tree";
		Utils.ensureDirExists(path);
		return path;
	}

	// TODO(@hayesall) This variable is only used by two methods.
	private RegressionTree[] nextSetOfTrees = null;

	void updateSetOfTrees() {
		boostedTrees.add(nextSetOfTrees);
		numTrees++;
		nextSetOfTrees = null;
	}

	void addTree(RegressionTree tree, double stepLength, int modelNumber) {
		if (hasSingleTheory) {
			// Convert array of clauses to sentences and add to theory.
			List<Sentence> sentences = new ArrayList<>(tree.getRegressionClauses());
			numTrees++;
			this.stepLength.add(stepLength);
			sentences.addAll(setup.getInnerLooper().getParser().parse(getStepLengthSentence(numTrees)));
			addSentences(sentences);
		} else {
			if (nextSetOfTrees == null) {
				// Is this the first one in this new forest?
				nextSetOfTrees = new RegressionTree[RunBoostedRDN.numbModelsToMake];
				// These are shared by all trees in one group.
				this.stepLength.add(stepLength);
			} else {
				if (stepLength != this.stepLength.get(numTrees)) { Utils.error("Expecting stepLength () for modelNumber=" + modelNumber + " to match that for modelNumber=0"); }
			}
			nextSetOfTrees[modelNumber] = tree;
		}
	}

	ClauseBasedTree getTree(int tree) {
		return boostedTrees.get(tree)[0];
	}
	
	String getStepLengthSentence(int i) {
		return LearnBoostedRDN.stepLengthPredicate(i) + "(" + stepLength.get(i - 1) + ").";
	}
	
	public void reparseModel(WILLSetup setup) {
		if (!hasSingleTheory) {
			for (ClauseBasedTree[] btree : boostedTrees) {
				for (int i = 0; i < RunBoostedRDN.numbModelsToMake; i++) {
					btree[i].setSetup(setup);
					btree[i].reparseRegressionTrees();
				}
			}
			if (prior_advice != null) {
				prior_advice.setSetup(setup);
				prior_advice.reparseRegressionTrees();
			}
			
			setSetup(setup);
		} else {
			setSetup(setup);
			List<Sentence> newSentences = new ArrayList<>();
			for (Sentence sent : theory) {
				Utils.println("Use string " + sent);
				Sentence sent2 = setup.convertFactToClause(sent + ".", VarIndicator.questionMarks);
				newSentences.add(sent2);
				Utils.println("Adding sentence: " + sent2);
			}
			
			// Reset
			theory=null;
			addSentences(newSentences);
		}
		// Also reload the constants
		if (constList != null) {
			ConstantLookupList newConstList = new MultiClassExampleHandler.ConstantLookupList();
			newConstList.load(setup, constList.toString());
			setup.getMulticlassHandler().updateConstantList(targetPredicate, newConstList);
		}
	}

	public Map<Clause, Double> convertToSingleMLN() {
		HashMap<Clause, Double> clauses = new HashMap<>();
		for (ClauseBasedTree[] trees : boostedTrees) {
			for (ClauseBasedTree tree : trees) {
				for (Clause regClause : tree.getRegressionClauses()) {
					addClause(clauses, regClause);
				}
			}
		}
		if(prior_advice != null) {
			for (Clause regClause : prior_advice.getRegressionClauses()) {
				addClause(clauses, regClause);
			}
		}
		return clauses;
	}
	
	
	private void addClause(HashMap<Clause, Double> clauses, Clause regClause) {
		Literal old_head = regClause.getDefiniteClauseHead();
		if (setup == null) {
			Utils.error("Null setup");
		}
		if (setup.getHandler() == null) {
			Utils.error("Null handler");
		}
		if (old_head == null) {
			Utils.error("Null old_head");
		}

		assert old_head != null;
		if (old_head.getArguments() == null) {
			Utils.error("Null arguments");
		}
		Literal head = setup.getHandler().getLiteral(
				old_head.predicateName,new ArrayList<>(old_head.getArguments()));
		
		int last = head.numberArgs();
		Term y = head.getArgument(head.numberArgs()-1);
		double value = ((NumericConstant) y).value.doubleValue();
		
		head.removeArgument(head.getArgument(last-1));
		List<Literal> posLits = new ArrayList<>();
		posLits.add(head);
		Clause cl = new Clause(setup.getHandler(), posLits, regClause.negLiterals, "");
		boolean added = false;
		for (Clause clause : clauses.keySet()) {
			if (clause.isVariant(cl)) {
				clauses.put(clause, clauses.get(clause) + value);
				added=true;
				break;
			}
		}
		if (!added) {
			clauses.put(cl, value);
		}
	}
	
	/**
	 * @return the targetPredicate
	 */
	public String getTargetPredicate() {
		return targetPredicate;
	}

	/**
	 * @param targetPredicate the targetPredicate to set
	 */
	public void setTargetPredicate(String targetPredicate) {
		this.targetPredicate = targetPredicate;
	}

	/**
	 * @param treePrefix the treePrefix to set
	 */
	void setTreePrefix(String treePrefix) {
		this.treePrefix = treePrefix;
	}

	/**
	 * @return the numTrees
	 */
	public int getNumTrees() {
		return numTrees;
	}

	/**
	 * @param numTrees the numTrees to set
	 */
	public void setNumTrees(int numTrees) {
		this.numTrees = numTrees;
	}

	/**
	 * @param logPrior the log_prior to set
	 */
	void setLog_prior(double logPrior) {
		// TODO(@hayesall): 0 is always passed to this method.
		log_prior = logPrior;
	}

	/**
	 * @param hasSingleTheory the hasSingleTheory to set
	 */
	public void setHasSingleTheory(boolean hasSingleTheory) {
		this.hasSingleTheory = hasSingleTheory;
	}

	void addSentences(List<Sentence> bkClauses) {
		if (!hasSingleTheory) {
			Utils.error("Attempting to add clauses to RDN that is not a single theory type");
		}
		if (setup == null) {
			Utils.error("WILLSetup not provided to RDNModelPerPredicate");
		}
		setup.getContext().assertSentences(bkClauses);
		if (theory == null) {
			theory = new ArrayList<>();
		}
		theory.addAll(bkClauses);	
	}

	public WILLSetup getSetup() {
		return setup;
	}

	public void setSetup(WILLSetup setup) {
		this.setup = setup;
	}

	String getLogPriorSentence() {
		return LearnBoostedRDN.LOG_PRIOR_PREDICATE + "(" + log_prior +").";
	}

	public void setCache(Map<String, Long> cachedRegressionClauseWeights) {
		for (ClauseBasedTree[] trees : boostedTrees) {
			for (ClauseBasedTree tree : trees) {
				if (tree instanceof RegressionMLNModel) {
					((RegressionMLNModel)tree).setCachedValues(cachedRegressionClauseWeights);
				}
			}
		}
	}

	public Set<Literal> getGroundParents(RegressionRDNExample example,
				Map<String, List<RegressionRDNExample>> jointExamples) {
		Set<Literal> parents = new HashSet<>();
		for (RegressionTree[] trees : boostedTrees) {
			for (RegressionTree tree : trees) {
				Set<Literal> pars = tree.getGroundParents(example, jointExamples);
				parents.addAll(pars);
			}
		}
		return parents;
	}
}
