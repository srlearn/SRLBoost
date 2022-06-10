package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.Boosting.Trees.ClauseBasedTree;
import edu.wisc.cs.will.Boosting.Trees.RegressionMLNModel;
import edu.wisc.cs.will.Boosting.Trees.RegressionTree;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Serializable;
import java.util.*;

// TODO(@hayesall): There are a large number of private variables and getters/setters scattered around this file.

public class ConditionalModelPerPredicate implements Serializable {

	private static final long serialVersionUID = 9130108889576097786L;

	/*
	 *  Prior log probability i.e. \psi_0
	 */
	private double log_prior = -1.8;

	/*
	 *  List of boosted trees
	 */
	private final List<RegressionTree[]> boostedTrees;

	/*
	 *  Number of trees. Generally numTrees would be the same as the boostedTrees size but one can reduce this.
	 */
	private int numTrees;

	/*
	 *  Step length for gradient.
	 *  All models in a array of RegressionTree[] have the same stepLength.
	 */
	private final List<Double> stepLength;

	/*
	 * Predicate for which model is learnt.
	 */
	private String targetPredicate;

	/*
	 * Prefix for every tree used while storing the tree.
	 * Generally set to the targetPredicate 
	 */
	private String treePrefix;

	/*
	 * Needed only with single theory as it stores the clauses 
	 */
	private WILLSetup setup;

	public ConditionalModelPerPredicate(WILLSetup willsetup) {
		boostedTrees = new ArrayList<>(4);
		stepLength = new ArrayList<>(4);
		numTrees = 0;
		treePrefix = "";
		setup = willsetup;
	}

	/*
	 * Calculates the regression value for an example based on the model.
	 * Mostly one shouldn't have to use this but should directly use returnModelProbability.
	 * @param ex Example to evaluate
	 * @return the regression value for the example
	 */
	public RegressionValueOrVector returnModelRegression(Example ex) {
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

		for (RegressionTree[] tree : boostedTrees) {
			if (counter == numTrees) { break; }
			
			RegressionValueOrVector sum_grad = null;

			for (int i = 0; i < RunBoostedRDN.numbModelsToMake; i++) {
				if (setup == null) { Utils.error("WILLSetup object not initialized"); }

				RegressionValueOrVector thisValue = tree[i].getRegressionValue(ex);
				thisValue.multiply(stepLength.get(counter));

				sum_grad = thisValue;
			}
			sum_grad.multiply(1/RunBoostedRDN.numbModelsToMake);
			total_sum_grad.addValueOrVector(sum_grad);
			counter++;
		}
		return total_sum_grad;
	}


	public RegressionValueOrVector returnModelRegressionWithPrior(Example ex) {
		RegressionValueOrVector modelRegression =  returnModelRegression(ex);
		modelRegression.addScalar(log_prior);
		return modelRegression;
	}

	/*
	 * Returns the probability of the example
	 * @param ex input example
	 * @return probability of the example being true
	 */
	ProbDistribution returnModelProbability(Example ex) {
		RegressionValueOrVector sum_grad = returnModelRegressionWithPrior(ex);
		return new ProbDistribution(sum_grad);
	}

	/*
	 * This function adds the predicates that are used in this model,
	 * i.e., the parents for the target predicate.
	 * @param preds - Adds the parent predicate to this collection
	 * Duplicate detection is responsibility of the caller
	 */
	public void getParentPredicates(Collection<PredicateName> preds) {
		for (RegressionTree[] regTree : boostedTrees) {
			for (int i = 0; i < RunBoostedRDN.numbModelsToMake; i++) {
				regTree[i].getParentPredicates(preds);
			}
		}
	}

	/*
	 * Saves the model in the given file
	 * NOTE: the trees are stored in different files but their 
	 * filename prefix is stored in the model
	 * @param filename name to save model as
	 */
	public void saveModel(String filename) {

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

	/*
	 * Loads the model from a given file
	 */
	public void loadModel(String filename, WILLSetup setup, int loadMaxTrees) {

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
		path += "Trees/" + prefix + "Tree" + i + BoostingUtils.getLabelForModelNumber(modelNumber) + ".tree";
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

	String getStepLengthSentence(int i) {
		return LearnBoostedRDN.stepLengthPredicate(i) + "(" + stepLength.get(i - 1) + ").";
	}
	
	public void reparseModel(WILLSetup setup) {
		for (ClauseBasedTree[] btree : boostedTrees) {
			for (int i = 0; i < RunBoostedRDN.numbModelsToMake; i++) {
				btree[i].setSetup(setup);
				btree[i].reparseRegressionTrees();
			}
		}

		setSetup(setup);
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
	
	/*
	 * @return the targetPredicate
	 */
	public String getTargetPredicate() {
		return targetPredicate;
	}

	/*
	 * @param targetPredicate the targetPredicate to set
	 */
	public void setTargetPredicate(String targetPredicate) {
		this.targetPredicate = targetPredicate;
	}

	/*
	 * @param treePrefix the treePrefix to set
	 */
	void setTreePrefix(String treePrefix) {
		this.treePrefix = treePrefix;
	}

	/*
	 * @return the numTrees
	 */
	public int getNumTrees() {
		return numTrees;
	}

	/*
	 * @param numTrees the numTrees to set
	 */
	public void setNumTrees(int numTrees) {
		this.numTrees = numTrees;
	}

	/*
	 * @param logPrior the log_prior to set
	 */
	void setLog_prior(double logPrior) {
		// TODO(@hayesall): 0 is always passed to this method.
		log_prior = logPrior;
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

}
