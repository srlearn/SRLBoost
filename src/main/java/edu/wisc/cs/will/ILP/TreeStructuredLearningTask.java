package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.FOPC.TreeStructuredTheoryInteriorNode;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.VectorStatistics;

import java.io.Serializable;
import java.util.List;

/*
 * @author shavlik
 *  Holds a task for learning an interior node for a tree-structured theory.
 */
class TreeStructuredLearningTask implements Serializable {

	private static final long serialVersionUID = 1L;
	
	private final List<Example>  posExamples;
	private final List<Example>  negExamples;
	
	private final TreeStructuredTheoryInteriorNode node;
	private SingleClauseNode          creatingNode;
	private double                    score;

	TreeStructuredLearningTask(List<Example> posExamples, List<Example> negExamples, TreeStructuredTheoryInteriorNode node) {
		this.posExamples = posExamples;
		this.negExamples = negExamples;
		this.node        = node;
	}
	
	public List<Example> getPosExamples() {
		return posExamples;
	}

	List<Example> getNegExamples() {
		return negExamples;
	}

	public TreeStructuredTheoryInteriorNode getNode() {
		return node;
	}

	SingleClauseNode getCreatingNode() {
		return creatingNode;
	}
	
	void setCreatingNode(SingleClauseNode creatingNode) {
		this.creatingNode = creatingNode;
	}

	public double getScore() {
		return score;
	}

	public void setScore(double score) {
		this.score = score;
	}
	
	// This should be called ONLY for root nodes as SingleClauseNode object is not 
	// available(null) in that case. It assumes that the examples are regression examples 
	double getVariance() {
		double sumOfOutputSquared = 0;
		double sumOfOutput = 0;
		double sumOfWeights = 0;
		for (Example eg : getPosExamples()) {
			RegressionExample regEx = (RegressionExample)eg;
			// If regression example, use vectorVariance
			if (regEx.isHasRegressionVector()) {
				return getVectorVariance();
			}
			sumOfOutputSquared += regEx.getOutputValue() * regEx.getOutputValue() * regEx.getWeightOnExample();
			sumOfOutput += regEx.getOutputValue() * regEx.getWeightOnExample();
			sumOfWeights += regEx.getWeightOnExample();
		}
		return sumOfOutputSquared/sumOfWeights - (Math.pow(sumOfOutput/sumOfWeights, 2));
	}
	
	
	private double getVectorVariance() {
		VectorStatistics vecStats = new VectorStatistics();
		if (getPosExamples().size() == 0) {
			Utils.error("No examples in the task!!");
		}
		for (Example eg : getPosExamples()) {
			RegressionExample regEx = (RegressionExample)eg;
			if (regEx.isHasRegressionVector()) {
				vecStats.addVector(regEx.getOutputVector());
			} else {
				Utils.error("No regression vector for example: " + regEx);
			}
		}
		return vecStats.getVariance();
	}
}

