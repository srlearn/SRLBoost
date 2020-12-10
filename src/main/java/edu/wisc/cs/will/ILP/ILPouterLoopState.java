package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.TreeStructuredTheory;
import edu.wisc.cs.will.FOPC.TreeStructuredTheoryInteriorNode;
import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;
import java.util.*;

/*
 *
 * @author twalker
 */
public class ILPouterLoopState implements Serializable, Cloneable {

    private static final long serialVersionUID = 2524809644370702110L;
    private int numberOfCycles;
    private int            numberOfLearnedClauses;     // Could easily count this, but keep it around for simplicity.
    private int            numberOfPosExamplesCovered; // Ditto.
    private int            numberOfNegExamplesCovered; // Ditto.
    private int            total_nodesExpanded;        // Sum over all outer-loop iterations.
    private int            total_nodesCreated;
    private int            total_nodesNotAddedToOPENsinceMaxScoreTooLow;
    private int            total_nodesRemovedFromOPENsinceMaxScoreNowTooLow;
    private int            total_countOfPruningDueToVariantChildren;

    private double         fractionOfPosCovered;
    private double         fractionOfNegCovered;

    private Theory         stdILPtheory;           // The standard ILP theory, i.e. the best clause from each seed.

    private Collection<Example> coveredPosExamples; // Collect positive examples covered by at least ONE 'best clause' produced by the ILP inner loop.
    private Collection<Example> coveredNegExamples; // Also see which negative examples are covered by some clause.

    private boolean          RRR;

    private Set<Example>     seedPosExamplesUsed;
    private Set<Example>     seedNegExamplesUsed;

    private   List<TreeStructuredLearningTask>  queueOfTreeStructuredLearningTasks; 
	private   TreeStructuredTheory              treeBasedTheory;  // Used when learning tree-structured theories.
    private   TreeStructuredLearningTask        currentTreeLearningTask;
    private   double                            overallMinPosWeight = -1; // When doing trees and we use smaller training sets upon recursion, this specifies the minimum (weighted) size of positive examples in a recursive call.
    double                            maxAcceptableNodeScoreToStop = Double.POSITIVE_INFINITY; // If score <= this, can create a leaf node in a tree-structured theory.

    private long             clockTimeUsedInMillisec;
    private long             maximumClockTimeInMillisec = Long.MAX_VALUE;
    
   /* Empty constructor for ILPouterLoopState.
    *
    * It is assumed that the ILPOuterLoop will setup all of these variables during
    * initialization or re-constitution of the checkpoint file.
    */
   ILPouterLoopState() {
    }

    public ILPouterLoopState clone() {
        try {
            return (ILPouterLoopState) super.clone();
        } catch(CloneNotSupportedException e) {
            return null;
        }
    }

    Collection<Example> getCoveredNegExamples() {
        return coveredNegExamples;
    }

    void setCoveredNegExamples(Collection<Example> coveredNegExamples) {
        this.coveredNegExamples = coveredNegExamples;
    }

    Collection<Example> getCoveredPosExamples() {
        return coveredPosExamples;
    }

    void setCoveredPosExamples(Collection<Example> coveredPosExamples) {
        this.coveredPosExamples = coveredPosExamples;
    }

    double getFractionOfNegCovered() {
        return fractionOfNegCovered;
    }

    void setFractionOfNegCovered(double fractionOfNegCovered) {
        this.fractionOfNegCovered = fractionOfNegCovered;
    }

    double getFractionOfPosCovered() {
        return fractionOfPosCovered;
    }

    void setFractionOfPosCovered(double fractionOfPosCovered) {
        this.fractionOfPosCovered = fractionOfPosCovered;
    }

    int getNumberOfCycles() {
        return numberOfCycles;
    }

    void setNumberOfCycles(int numberOfCycles) {
        this.numberOfCycles = numberOfCycles;
    }

    int getNumberOfLearnedClauses() {
        return numberOfLearnedClauses;
    }

    void setNumberOfLearnedClauses(int numberOfLearnedClauses) {
        this.numberOfLearnedClauses = numberOfLearnedClauses;
    }

    int getNumberOfNegExamplesCovered() {
        return numberOfNegExamplesCovered;
    }

    void setNumberOfNegExamplesCovered(int numberOfNegExamplesCovered) {
        this.numberOfNegExamplesCovered = numberOfNegExamplesCovered;
    }

    int getNumberOfPosExamplesCovered() {
        return numberOfPosExamplesCovered;
    }

    void setNumberOfPosExamplesCovered(int numberOfPosExamplesCovered) {
        this.numberOfPosExamplesCovered = numberOfPosExamplesCovered;
    }

    Theory getStdILPtheory() {
        return stdILPtheory;
    }

    void setStdILPtheory(Theory stdILPtheory) {
        this.stdILPtheory = stdILPtheory;
    }

    int getTotal_countOfPruningDueToVariantChildren() {
        return total_countOfPruningDueToVariantChildren;
    }

    void setTotal_countOfPruningDueToVariantChildren(int total_countOfPruningDueToVariantChildren) {
        this.total_countOfPruningDueToVariantChildren = total_countOfPruningDueToVariantChildren;
    }

    int getTotal_nodesExpanded() {
        return total_nodesExpanded;
    }

    void setTotal_nodesConsidered(int total_nodesConsidered) {
        this.total_nodesExpanded = total_nodesConsidered;
    }

    int getTotal_nodesCreated() {
        return total_nodesCreated;
    }

    void setTotal_nodesCreated(int total_nodesCreated) {
        this.total_nodesCreated = total_nodesCreated;
    }

    int getTotal_nodesNotAddedToOPENsinceMaxScoreTooLow() {
        return total_nodesNotAddedToOPENsinceMaxScoreTooLow;
    }

    void setTotal_nodesNotAddedToOPENsinceMaxScoreTooLow(int total_nodesNotAddedToOPENsinceMaxScoreTooLow) {
        this.total_nodesNotAddedToOPENsinceMaxScoreTooLow = total_nodesNotAddedToOPENsinceMaxScoreTooLow;
    }

    int getTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow() {
        return total_nodesRemovedFromOPENsinceMaxScoreNowTooLow;
    }

    void setTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow(int total_nodesRemovedFromOPENsinceMaxScoreNowTooLow) {
        this.total_nodesRemovedFromOPENsinceMaxScoreNowTooLow = total_nodesRemovedFromOPENsinceMaxScoreNowTooLow;
    }

    int getCurrentFold() {
        return -1;
    }

    boolean isRRR() {
        return RRR;
    }

    void setRRR(boolean useRRR) {
        this.RRR = useRRR;
    }

    Set<Example> getNegExamplesUsedAsSeeds() {
        return seedNegExamplesUsed;
    }

    Set<Example> getSeedPosExamplesUsed() {
        if ( seedPosExamplesUsed == null ) seedPosExamplesUsed = new HashSet<>();

        return seedPosExamplesUsed;
    }

    Set<Example> getSeedNegExamplesUsed() {
        if ( seedNegExamplesUsed == null ) seedNegExamplesUsed = new HashSet<>();

        return seedNegExamplesUsed;
    }
    
    void clearSeedPosExamplesUsed() {
    	if ( seedPosExamplesUsed == null ) { seedPosExamplesUsed = new HashSet<>(4); return; }
    	seedPosExamplesUsed.clear();
    }
    
    void clearSeedNegExamplesUsed() {
    	if ( seedNegExamplesUsed == null ) { seedNegExamplesUsed = new HashSet<>(4);return; }
    	seedNegExamplesUsed.clear();
    }

    long getClockTimeUsedInMillisec() {
        return clockTimeUsedInMillisec;
    }

    void setClockTimeUsedInMillisec(long clockTimeUsed) {
        this.clockTimeUsedInMillisec = clockTimeUsed;
    }

    long getMaximumClockTimeInMillisec() {
        return maximumClockTimeInMillisec;
    }

    void setMaximumClockTimeInMillisec(long maximumClockTime) {
        this.maximumClockTimeInMillisec = maximumClockTime;
    }
	
	TreeStructuredLearningTask popQueueOfTreeStructuredLearningTasks() {
		if (queueOfTreeStructuredLearningTasksIsEmpty()) { return null; }
		return queueOfTreeStructuredLearningTasks.remove(0);
	}	
	
	// This method assumes LOWER scores are better.
    void addToQueueOfTreeStructuredLearningTasks(TreeStructuredLearningTask task, TreeStructuredTheoryInteriorNode treeNode, SingleClauseNode creatingSearchNode, double score) {
        Utils.println("%      addToQueueOfTreeStructuredLearningTasks (level=" + Utils.comma(treeNode == null ? -1 : treeNode.getLevel())
                    + "; score=" + Utils.truncate(score, 6) + ")\n%         ILP node to extend: "	+  creatingSearchNode);
        task.setCreatingNode(creatingSearchNode);
		task.setScore(score);
		insertIntoQueueOfLearningTasks(task, (treeNode == null ? -1 : treeNode.getLevel()), score);
	}
	
	// This method assumes LOWER scores are better.
	private void insertIntoQueueOfLearningTasks(TreeStructuredLearningTask task, int level, double score) {
		if (queueOfTreeStructuredLearningTasks == null) { queueOfTreeStructuredLearningTasks = new LinkedList<>(); }
		int counter = 0;
		int size    = Utils.getSizeSafely(queueOfTreeStructuredLearningTasks);
		for (TreeStructuredLearningTask item : queueOfTreeStructuredLearningTasks) {
			if (score < item.getScore()) { // See if the new node's score belongs BEFORE this item.  (Ties go AFTER old entries.)
				queueOfTreeStructuredLearningTasks.add(counter, task);
                Utils.println("%      Insert tree-structured search node (@ level = " + Utils.comma(level) + " and with score = " + Utils.truncate(score, 6) + ") into position #" + Utils.comma(counter + 1) + " in the search queue (new size=" + Utils.comma(size + 1)+  ").");
                return;
			}
			counter++;
		}
        Utils.println("%      Insert tree-structured search node (@ level = " + Utils.comma(level) + " and with score = " + Utils.truncate(score, 6) + ") into the LAST position (#" + Utils.comma(counter + 1) + ") in the search queue.");
        queueOfTreeStructuredLearningTasks.add(task);
	}

	boolean queueOfTreeStructuredLearningTasksIsEmpty() {
		return (queueOfTreeStructuredLearningTasks == null || queueOfTreeStructuredLearningTasks.isEmpty()) ;
	}

    TreeStructuredTheory getTreeBasedTheory() {
		return treeBasedTheory;
	}

    void setTreeBasedTheory(TreeStructuredTheory treeBasedTheory) {
		this.treeBasedTheory = treeBasedTheory;
	}

	TreeStructuredLearningTask getCurrentTreeLearningTask() {
		return currentTreeLearningTask;
	}

    void setCurrentTreeLearningTask(TreeStructuredLearningTask currentTreeLearningTask) {
		this.currentTreeLearningTask = currentTreeLearningTask;
	}

	double getOverallMinPosWeight() {
		return overallMinPosWeight;
	}

	void setOverallMinPosWeight(double wgt) {
		this.overallMinPosWeight = wgt;
	}
    
    void clearAll() {
    	if (coveredPosExamples     != null) { coveredPosExamples.clear(); }
    	if (coveredNegExamples     != null) { coveredNegExamples.clear(); }
    	if (seedPosExamplesUsed    != null) { seedPosExamplesUsed.clear(); }
    	if (seedNegExamplesUsed    != null) { seedNegExamplesUsed.clear(); }
    	if (queueOfTreeStructuredLearningTasks != null) { queueOfTreeStructuredLearningTasks.clear(); }
    	stdILPtheory = null;
    }

}
