package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.FOPCInputStream;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchMonitor;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

import java.io.IOException;
import java.io.Serializable;
import java.util.*;

/*
 * Gleaner maintains the best clause (per 'marker') in each bin of recall ranges.
 * See M. Goadrich, L. Oliphant, & J. Shavlik (2006), 
 * Gleaner: Creating Ensembles of First-Order Clauses to Improve Recall-Precision Curves. 
 * Machine Learning, 64, pp. 231-262.
 * http://pages.cs.wisc.edu/~shavlik/abstracts/goadrich.mlj06.abstract.html
 * 
 * @author shavlik
 */
public class Gleaner extends SearchMonitor implements Serializable {
	private             boolean useStructuredOutput = false; // This flag, if true, causes the output to be structured rather than freeform human-readable text
    // Structured output is readable by RuleSetVisualizer (edu.wisc.cs.will.rulesetvisualizer pkg in MachineReading) - cth
    
	SingleClauseNode bestNode  = null;  // Also keep track of the best node.  (Maybe this should be a subclass of MonitorILPsearch?  For now, let these evolve separately.
	private double           bestScore = Double.NEGATIVE_INFINITY;
	SingleClauseNode bestNodeRegardless  = null;
	double           bestScoreRegardless = Double.NEGATIVE_INFINITY;
	public  int       reportingPeriod;  // Report statistics every this many node expansions.

	private transient HandleFOPCstrings       stringHandler;
	          private ILPouterLoop            ilpOuterLooper; // Trevor - I (JWS) didnt know if this should be transient.  TODO
    transient private GleanerFileNameProvider fileNameProvider;
    
    final int    reportUptoThisManyFalseNegatives = 5; // Use 0 (or a negative number) to turn this off.
    final int    reportUptoThisManyFalsePositives = 5;
	private final double reportFalseNegativesIfRecallAtLeastThisHigh    = 0.8;
	private final double reportFalsePositivesIfPrecisionAtLeastThisHigh = 0.8;
    
	
	private final String defaultMarker = "allPossibleMarkers";
	private String       currentMarker; // The current marker 'name.'
	private List<String> markerList;    // A Gleaner is kept for each marker provided.  The user can use anything to label Gleaners.
	private Map<String,Map<Integer,SavedClause>>        gleaners; // The first argument is the marker, the second is an integer marking the recall bin, and the inner Map contains the highest-scoring clause in that bin.
	private Map<Integer,SavedClause>              currentGleaner;
	private Map<Integer,SavedClause>              defaultGleaner;
	private final double[] recallBinUpperBounds = {0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.45, 0.50, 0.55, 0.60, 0.65, 0.70, 0.75, 0.80, 0.85, 0.90, 0.95, 1.01};  // Leave a little extra at the end (could be +inf, actually).
	private boolean  addedAnItem = false; // Indicates that something is in some Gleaner and hence cannot change recallBinUpperBounds.
	private long     nodeCounterAll         =    0;
	private long     nodeCounterAcceptable  =    0;
	private long     changedAtThisNode      =   -1;
	private long     addsToGlobalGleaner    =    0;
	private long     addsToCurrentGleaner   =    0;
	private long     lastReported_addsToGlobalGleaner  = 0;
	private long     lastReported_addsToCurrentGleaner = 0;

	public Gleaner() {
		this(5000);
	}

	private Gleaner(int reportingPeriod) {
      resetAllMarkers();
      this.fileNameProvider   = null;
      this.setTaskBeingMonitored(null);
	  this.stringHandler      = null;
	  this.reportingPeriod    = reportingPeriod; // Override the default.
	  
	}
	
	public void setStringHandler(HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
	}


	void clearBestNode() { // Might want to clear this, e.g., each ILP outer loop clears this so that the bestNode PER inner loop can be found.
		bestNode              = null;
		bestScore             = Double.NEGATIVE_INFINITY;
		bestScoreRegardless   = Double.NEGATIVE_INFINITY;
		bestNodeRegardless    = null;
		nodeCounterAll        =  0;
		nodeCounterAcceptable =  0;
		changedAtThisNode     = -1;
		addsToGlobalGleaner   =  0;
		addsToCurrentGleaner  =  0;
		lastReported_addsToGlobalGleaner  = 0;
		lastReported_addsToCurrentGleaner = 0;
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

		nodeCounterAll++;

		// TODO(@hayesall): This is the only remaining call to `LearnOneClause.debugLevel`
		if (LearnOneClause.debugLevel > 0 && nodeCounterAll % reportingPeriod == 0) { reportSearchStats(); }
		
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
		SavedClause saver = new SavedClause(this, clause, nodeCounterAll, nodeCounterAcceptable, 
											(ilpOuterLooper != null && ilpOuterLooper.isFlipFlopPosAndNegExamples()),
											(ilpOuterLooper == null ? null  : ilpOuterLooper.getAnnotationForCurrentRun()),
											currentMarker);
		addToGleaner(defaultGleaner, saver, true);
		if (currentGleaner != defaultGleaner) { 
			addToGleaner(currentGleaner, saver, false);
		}
		
		// Keep track of the best clause overall, assuming it meets the acceptability criteria.
		nodeCounterAcceptable++;
		if (score > bestScore) {
			bestScore = score;
			bestNode  = clause;
			changedAtThisNode = nodeCounterAll;
			Utils.println("% Gleaner: New best node found (score = " + Utils.truncate(score, 6) + "): " + nodeBeingCreated);
		}

		return true;
	}
	
	private int countOfWarningsForInliners = 0; // Turn off reporting at the first 100.
	Clause handleInlinersIfPossible(Clause cRaw) {
		if (cRaw == null) { return null; }
		Clause c = (Clause) stringHandler.renameAllVariables(cRaw);
		if (ilpOuterLooper == null || ilpOuterLooper.innerLoopTask == null) { return c; }
		List<Clause> clauses = ilpOuterLooper.innerLoopTask.getInlineManager().handleInlinerAndSupportingClauses(c);
		
		if (clauses == null) { return c; }
		if (clauses.size() == 1) { return clauses.get(0); }
		if (++countOfWarningsForInliners < 3) { Utils.warning("#" + Utils.comma(countOfWarningsForInliners) + " Gleaner: when handling inliners in: \n   " + c + "\n got multiple clauses:\n   " + clauses); } // TODO figure out to do with these.
		return c;
	}

	// TODO(@hayesall): `reportSearchStats()` method can likely be removed.
	private void reportSearchStats() {
		Utils.print("% Gleaner has visited " + Utils.comma(nodeCounterAll) + " ILP clauses, of which " + Utils.comma(nodeCounterAcceptable) + " met the acceptability specs.");
		if (addsToGlobalGleaner  > lastReported_addsToGlobalGleaner)  { 
			Utils.print("\n%  Added " + addsToGlobalGleaner  + " clauses to the global gleaner." );
			addsToGlobalGleaner  = lastReported_addsToGlobalGleaner;
		}
		if (addsToCurrentGleaner > lastReported_addsToCurrentGleaner) {
			Utils.print("\n%  Added " + addsToCurrentGleaner + " clauses to the specific gleaner." );
			addsToCurrentGleaner  = lastReported_addsToCurrentGleaner;
		}
		if (changedAtThisNode > 0) {
			if (bestNode != null) { Utils.println("\n%  The best node, which scores " + Utils.truncate(bestScore, 3) + ", is:  [node #" + + changedAtThisNode + "]\n     " + bestNode); }
			changedAtThisNode = -1;
		}
		else { Utils.println("  No change in best clause since last report."); }
	}

	void setCurrentMarker(String markerRaw) {
		String marker = markerRaw;

		// Set to false to reduce the number of gleaners.
		if (!markerRaw.equals(defaultMarker) && ilpOuterLooper != null) {
			if (!marker.trim().equals("")) { marker += ", "; }
			marker += ilpOuterLooper.getAnnotationForCurrentRun();
		}
		currentGleaner = gleaners.get(marker);
		
		if (currentGleaner == null) { // See if we already have a gleaner of this type.  If not, create a new one.
			currentGleaner = new HashMap<>(8);
			gleaners.put(marker, currentGleaner);
			markerList.add(marker);
			addsToCurrentGleaner              = 0;
			lastReported_addsToCurrentGleaner = 0;
		}
		currentMarker = marker;
	}
	
	private void resetAllMarkers() { // Be careful using this.  Might NOT want to clear between different "ILP outer loop" runs - instead, just use a new marker.
		currentGleaner = null;
		defaultGleaner = null;
		markerList     = new ArrayList<>(8);
		gleaners       = new HashMap<>(8);
		setCurrentMarker(defaultMarker); // Create the default Gleaner.
		defaultGleaner = currentGleaner; // Hold on to the default - we keep the best of all clauses per bin in here.
		addedAnItem    = false;
		nodeCounterAll         =    0;
		nodeCounterAcceptable  =    0;
		changedAtThisNode      =   -1;
		addsToGlobalGleaner    =    0;
		addsToCurrentGleaner   =    0;
		lastReported_addsToGlobalGleaner  = 0;
		lastReported_addsToCurrentGleaner = 0;
	}

	private void addToGleaner(Map<Integer, SavedClause> gleaner, SavedClause saver, boolean theGlobalGleaner) {
		double  recall = saver.recall;
		double  F1     = saver.F1; // Use the F1 score for defining best within a bin.
		LearnOneClause  task = (LearnOneClause) getTaskBeingMonitored();
		if (task.regressionTask) { F1 = saver.score; } // Except when doing regression, then use the score.
		
		Integer index  = convertRecallToBinIndex(recall);
		SavedClause currentBestSaverInBin = gleaner.get(index);
		
		if (currentBestSaverInBin == null) { // Nothing there, so add.
			if (theGlobalGleaner) { addsToGlobalGleaner++; } else { addsToCurrentGleaner++; }
			gleaner.put(index, saver);
		}
		else {  // Otherwise, see if a new best has been found for this bin.
			double F1current = (task.regressionTask ? currentBestSaverInBin.score : currentBestSaverInBin.F1);
			
			if (F1 > F1current) { // Update since better clause found.
				gleaner.remove(currentBestSaverInBin);
				gleaner.put(index, saver);
				if (theGlobalGleaner) { addsToGlobalGleaner++; } else { addsToCurrentGleaner++; }
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

        FOPCInputStream fOPCInputStream = (FOPCInputStream) in;

        this.setStringHandler(fOPCInputStream.getStringHandler());
    }

	void setFileNameProvider(GleanerFileNameProvider fileNameProvider) {
        this.fileNameProvider = fileNameProvider;
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
