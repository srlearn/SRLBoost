package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.FOPCInputStream;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchMonitor;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

/*
 * Gleaner maintains the best clause (per 'marker') in each bin of recall ranges.
 * See M. Goadrich, L. Oliphant, & J. Shavlik (2006), 
 * Gleaner: Creating Ensembles of First-Order Clauses to Improve Recall-Precision Curves. 
 * Machine Learning, 64, pp. 231-262.
 * http://pages.cs.wisc.edu/~shavlik/abstracts/goadrich.mlj06.abstract.html
 * 
 * @author shavlik
 */
public class Gleaner extends SearchMonitor {

	private static final long serialVersionUID = 4948722327097394619L;

	private boolean useStructuredOutput = false; // This flag, if true, causes the output to be structured rather than
													// freeform human-readable text
    // Structured output is readable by RuleSetVisualizer (edu.wisc.cs.will.rulesetvisualizer pkg in MachineReading) - cth
    
	SingleClauseNode bestNode  = null;  // Also keep track of the best node.  (Maybe this should be a subclass of MonitorILPsearch?  For now, let these evolve separately.
	private double           bestScore = Double.NEGATIVE_INFINITY;
	SingleClauseNode bestNodeRegardless  = null;
	double           bestScoreRegardless = Double.NEGATIVE_INFINITY;

	private ILPouterLoop            ilpOuterLooper; // Trevor - I (JWS) didnt know if this should be transient.  TODO


	private final String defaultMarker = "allPossibleMarkers";
	private Map<String,Map<Integer,SavedClause>>        gleaners; // The first argument is the marker, the second is an integer marking the recall bin, and the inner Map contains the highest-scoring clause in that bin.
	private Map<Integer,SavedClause>              currentGleaner;
	private Map<Integer,SavedClause>              defaultGleaner;
	private final double[] recallBinUpperBounds = {0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.45, 0.50, 0.55, 0.60, 0.65, 0.70, 0.75, 0.80, 0.85, 0.90, 0.95, 1.01};  // Leave a little extra at the end (could be +inf, actually).
	private boolean  addedAnItem = false; // Indicates that something is in some Gleaner and hence cannot change recallBinUpperBounds.

	public Gleaner() {
      resetAllMarkers();
		this.setTaskBeingMonitored(null);
	}

	void clearBestNode() { // Might want to clear this, e.g., each ILP outer loop clears this so that the bestNode PER inner loop can be found.
		bestNode              = null;
		bestScore             = Double.NEGATIVE_INFINITY;
		bestScoreRegardless   = Double.NEGATIVE_INFINITY;
		bestNodeRegardless    = null;
	}
		
	// The general-purpose search code calls this when each node is scored.
	// Return FALSE if this node should NOT be added to OPEN, otherwise return true.
	public boolean recordNodeBeingScored(SearchNode nodeBeingCreated, double score) throws SearchInterrupted {
		SingleClauseNode clause = (SingleClauseNode) nodeBeingCreated;
		LearnOneClause     task = (LearnOneClause)   getTaskBeingMonitored();

		// Keep track of the best score, even if it isn't acceptable (e.g., we can then see the closest acceptable score ...).
		if (score > bestScoreRegardless) {
			bestScoreRegardless = score;
			bestNodeRegardless  = clause;
		}

		// Previously this was done when scoring a node timed out in computeCoverage(); we didn't want to report anything in such cases.
		if (clause.timedOut) { // Incompletely scored nodes should be ignored.
			return false;
		}
		
		if (clause.getPosCoverage() < 0 || clause.negCoverage < 0) { Utils.error("% Should not reach here with an unevaluated node: '" + nodeBeingCreated + "'."); }

		if (!clause.acceptableClauseExtraFilter(task)) {
			return false; // Unacceptable according to user-provided acceptability test.
		}
		if (task.getMinPosCoverage() > 0 && clause.getPosCoverage() < task.getMinPosCoverage()) {
			return false;  // Unacceptable recall.
		}
		if (task.getMaxNegCoverage() >= 0 && clause.negCoverage > task.getMaxNegCoverage()) {
			return false;  // Unacceptable coverage of negative examples (as a raw total).
		}
		if (task.getMinPrecision() > 0.0 && clause.precision() < task.getMinPrecision()) {
			return false;  // Unacceptable min precision.
		}
		if (task.maxRecall < 1.0 && clause.recall() > task.maxRecall) {
			return false;  // Unacceptable max precision.
		}
		if (task.regressionTask && clause == clause.getRootNode()) {
			Utils.println("% Unacceptable due to being the root node.");
			return false;  // Unacceptable max precision.
		}

		// Add to current Gleaner and default Gleaner (if different), even if unacceptable (to do: separate thresholds for Gleaner and for the best overall?  Or too many parameters?).
		SavedClause saver = new SavedClause(clause);
		addToGleaner(defaultGleaner, saver);
		if (currentGleaner != defaultGleaner) { 
			addToGleaner(currentGleaner, saver);
		}
		
		// Keep track of the best clause overall, assuming it meets the acceptability criteria.
		if (score > bestScore) {
			bestScore = score;
			bestNode  = clause;
			Utils.println("% Gleaner: New best node found (score = " + Utils.truncate(score, 6) + "): " + nodeBeingCreated);
		}

		return true;
	}

	void setCurrentMarker(String markerRaw) {
		String marker = markerRaw;

		// Set to false to reduce the number of gleaners.
		if (!markerRaw.equals(defaultMarker) && ilpOuterLooper != null) {
			if (!marker.trim().equals("")) { marker += ", "; }

			// TODO(@hayesall): After refactoring, the statement simplified to `marker += null`. This is likely wrong.
			marker += null;
		}
		currentGleaner = gleaners.computeIfAbsent(marker, k -> new HashMap<>(8));
	}
	
	private void resetAllMarkers() { // Be careful using this.  Might NOT want to clear between different "ILP outer loop" runs - instead, just use a new marker.
		currentGleaner = null;
		defaultGleaner = null;
		gleaners       = new HashMap<>(8);
		setCurrentMarker(defaultMarker); // Create the default Gleaner.
		defaultGleaner = currentGleaner; // Hold on to the default - we keep the best of all clauses per bin in here.
		addedAnItem    = false;
	}

	private void addToGleaner(Map<Integer, SavedClause> gleaner, SavedClause saver) {
		double  recall = saver.recall;
		double  F1     = saver.F1; // Use the F1 score for defining best within a bin.
		LearnOneClause  task = (LearnOneClause) getTaskBeingMonitored();
		if (task.regressionTask) { F1 = saver.score; } // Except when doing regression, then use the score.
		
		Integer index  = convertRecallToBinIndex(recall);
		SavedClause currentBestSaverInBin = gleaner.get(index);
		
		if (currentBestSaverInBin == null) { // Nothing there, so add.
			gleaner.put(index, saver);
		}
		else {  // Otherwise, see if a new best has been found for this bin.
			double F1current = (task.regressionTask ? currentBestSaverInBin.score : currentBestSaverInBin.F1);
			
			if (F1 > F1current) { // Update since better clause found.
				gleaner.remove(currentBestSaverInBin);
				gleaner.put(index, saver);
			}
		}
		if (!addedAnItem) { addedAnItem = true; }
	}

	private int convertRecallToBinIndex(double recall) {
		int counter = 0;
		for (double upper : recallBinUpperBounds) { 
			if (recall <= upper) { return counter; }
			counter++;
		}
		return counter; // If not found, return the last bin index plus 1.
	}

    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        if (!(in instanceof FOPCInputStream)) {
            throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject input stream must support FOPCObjectInputStream interface");
        }

        in.defaultReadObject();

	}

	void setILPouterLooper(ILPouterLoop ilpOuterLooper) {
		this.ilpOuterLooper = ilpOuterLooper;
	}


	void setUseStructuredOutput(boolean useStructuredOutput) {
		this.useStructuredOutput = useStructuredOutput;
	}
	boolean getUseStructuredOutput() {
		return useStructuredOutput;
	}

}
