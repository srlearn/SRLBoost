package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.FOPCInputStream;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchMonitor;
import edu.wisc.cs.will.stdAIsearch.SearchNode;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintStream;
import java.io.Serializable;
import java.text.SimpleDateFormat;
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
	/*
     * File extension to add to files to be consumed by RuleSetVisualizer 
     * (See package edu.wisc.edu.rulesetvisualizer in MachineReading project.)
     */
    private static final String  ruleSetVisualizerFileExtension = "viz";
	private             boolean useStructuredOutput = false; // This flag, if true, causes the output to be structured rather than freeform human-readable text
    // Structured output is readable by RuleSetVisualizer (edu.wisc.cs.will.rulesetvisualizer pkg in MachineReading) - cth
    
	SingleClauseNode bestNode  = null;  // Also keep track of the best node.  (Maybe this should be a subclass of MonitorILPsearch?  For now, let these evolve separately.
	private double           bestScore = Double.NEGATIVE_INFINITY;
	SingleClauseNode bestNodeRegardless  = null;
	double           bestScoreRegardless = Double.NEGATIVE_INFINITY;
	public  int       reportingPeriod;  // Report statistics every this many node expansions.

	transient public  HandleFOPCstrings       stringHandler;
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
		this(null, null, null, 5000);
	}

	public Gleaner(GleanerFileNameProvider fileNameProvider, StateBasedSearchTask owner, HandleFOPCstrings stringHandler, int reportingPeriod) {
      resetAllMarkers();
      this.fileNameProvider   = fileNameProvider;
      this.setTaskBeingMonitored(owner);
	  this.stringHandler      = stringHandler;
	  this.reportingPeriod    = reportingPeriod; // Override the default.
	  
	}
	
	public void setStringHandler(HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
	}


	public void clearAnySavedInformation() {
		// Do NOT clear the Gleaner's when this is called, since we want them to persist across searches.
		// Users can always create a new marker if they want a fresh Gleaner.
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
		if (LearnOneClause.debugLevel > 0 && nodeCounterAll % reportingPeriod == 0) { reportSearchStats(); }
		
		// Previously this was done when scoring a node timed out in computeCoverage(); we didn't want to report anything in such cases.
		if (clause.timedOut) { // Incompletely scored nodes should be ignored.
			if (LearnOneClause.debugLevel > 0) { Utils.println("% Ignored because an incompletely scored node due to a timeout: " + clause); }
			return false;
		}
		
		if (clause.getPosCoverage() < 0 || clause.negCoverage < 0) { Utils.error("% Should not reach here with an unevaluated node: '" + nodeBeingCreated + "'."); }

		if (!clause.acceptableClauseExtraFilter(task)) {
			if (LearnOneClause.debugLevel > 1) { Utils.println("% Unacceptable due to extra-filter test: " + clause); }
			return false; // Unacceptable according to user-provided acceptability test.
		}
		if (task.getMinPosCoverage() > 0 && clause.getPosCoverage() < task.getMinPosCoverage()) {
			if (LearnOneClause.debugLevel > 1) { Utils.println("% Unacceptable due to min pos coverage: " + Utils.truncate(clause.getPosCoverage(), 4) + " vs " + Utils.truncate(task.getMinPosCoverage(), 4) + "   " + clause); }
			return false;  // Unacceptable recall.
		}
		if (task.getMaxNegCoverage() >= 0 && clause.negCoverage > task.getMaxNegCoverage()) {
			if (LearnOneClause.debugLevel > 1) { Utils.println("% Unacceptable due to max neg coverage: " + Utils.truncate(clause.negCoverage, 4) + " vs " +  Utils.truncate(task.getMaxNegCoverage(),4) + "   " + clause); }
			return false;  // Unacceptable coverage of negative examples (as a raw total).
		}
		if (task.getMinPrecision() > 0.0 && clause.precision() < task.getMinPrecision()) {
			if (LearnOneClause.debugLevel > 1) { Utils.println("% Unacceptable due to minPrecision: " + Utils.truncate(clause.precision(), 4) + " vs " +  Utils.truncate(task.minPrecision, 4) + "   " + clause); }
			return false;  // Unacceptable min precision.
		}
		if (task.maxRecall < 1.0 && clause.recall() > task.maxRecall) {
			if (LearnOneClause.debugLevel > 1) { Utils.println("% Unacceptable due to maxPrecision: " + clause.precision() + " vs " +  task.maxRecall + "   " + clause); }
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
		addToGleaner("default", defaultGleaner, saver, true);
		if (currentGleaner != defaultGleaner) { 
			addToGleaner("current", currentGleaner, saver, false);
		}
		
		// Keep track of the best clause overall, assuming it meets the acceptability criteria.
		if (LearnOneClause.debugLevel > 2) { Utils.println("% Acceptable (score = " + Utils.truncate(score, 4) + "): " + clause ); }
		nodeCounterAcceptable++;
		if (score > bestScore) {
			bestScore = score;
			bestNode  = clause;
			changedAtThisNode = nodeCounterAll;
			Utils.println("% Gleaner: New best node found (score = " + Utils.truncate(score, 6) + "): " + nodeBeingCreated);
		} else if (LearnOneClause.debugLevel > 1) {
			Utils.println("Acceptable but did not beat the score of: " + Utils.truncate(bestScore, 4));
		}

		return true;
	}
	
	private int countOfWarningsForInliners = 0; // Turn off reporting at the first 100.
	Clause handleInlinersIfPossible(Clause cRaw) {
		if (cRaw == null) { return cRaw; }
		Clause c = (Clause) stringHandler.renameAllVariables(cRaw);
		if (ilpOuterLooper == null || ilpOuterLooper.innerLoopTask == null) { return c; }
		List<Clause> clauses = ilpOuterLooper.innerLoopTask.getInlineManager().handleInlinerAndSupportingClauses(c);
		
		if (clauses == null) { return c; }
		if (clauses.size() == 1) { return clauses.get(0); }
		if (++countOfWarningsForInliners < 3) { Utils.warning("#" + Utils.comma(countOfWarningsForInliners) + " Gleaner: when handling inliners in: \n   " + c + "\n got multiple clauses:\n   " + clauses); } // TODO figure out to do with these.
		return c;
	}

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

	private void addToGleaner(String name, Map<Integer,SavedClause> gleaner, SavedClause saver, boolean theGlobalGleaner) {
		double  recall = saver.recall;
		double  F1     = saver.F1; // Use the F1 score for defining best within a bin.
		LearnOneClause  task = (LearnOneClause) getTaskBeingMonitored();
		if (task.regressionTask) { F1 = saver.score; } // Except when doing regression, then use the score.
		
		Integer index  = convertRecallToBinIndex(recall);
		SavedClause currentBestSaverInBin = gleaner.get(index);
		
		if (currentBestSaverInBin == null) { // Nothing there, so add.
			if (LearnOneClause.debugLevel > 1) { Utils.println("%  Adding '" + saver.ruleAsString + "' to the " + name + " Gleaner in bin #" + index + "."); }
			if (theGlobalGleaner) { addsToGlobalGleaner++; } else { addsToCurrentGleaner++; }
			gleaner.put(index, saver);
		}
		else {  // Otherwise, see if a new best has been found for this bin.
			double F1current = (task.regressionTask ? currentBestSaverInBin.score : currentBestSaverInBin.F1);
			
			if (F1 > F1current) { // Update since better clause found.
				if (LearnOneClause.debugLevel > 1) { Utils.println("%  Adding '" + saver.ruleAsString + "' to the " + name + " Gleaner in bin #" + index + ".  Removed '" + currentBestSaverInBin + "'."); }
				gleaner.remove(currentBestSaverInBin);
				gleaner.put(index, saver);
				if (theGlobalGleaner) { addsToGlobalGleaner++; } else { addsToCurrentGleaner++; }
			}
		}
		if (!addedAnItem) { addedAnItem = true; }
	}

   void dumpCurrentGleaner(LearnOneClause task) {
       // This is just my way of passing in the gleaner file name in a way that is
       // mutable when it changes on the outside...
       if ( fileNameProvider != null ) {
    	   String gleanerFileName  = fileNameProvider.getGleanerFileName();
    	   if (   gleanerFileName != null) { dumpCurrentGleaner(gleanerFileName, task); }
       }
       else {
           Utils.println("Gleaner.dumpCurrentGleaner() called with fileNameProvider == null.  Set the filenameProvider via Gleaner.setFileNameProvider().");
       }
   }
	
	void dumpCurrentGleaner(String fileName, LearnOneClause task) {
		if (useStructuredOutput) {
			// If structuredOutput is true, print a structured file format
			// (not necessarily human-readable), to be read by RuleSetVisualizer.
			dumpCurrentStructuredGleaner(fileName + "." + ruleSetVisualizerFileExtension, task);
		}
		else { // TODO - if we want to allow this to be turned off, we can add a boolean instance variable.
			try {
				String standardExtension = Utils.defaultFileExtension;
				CondorFileOutputStream outStream = new CondorFileOutputStream(fileName + "." + standardExtension);
				PrintStream            out       = new PrintStream(outStream); // No need for auto-flush.
				
				out.println("////// Learned from a dataset containing " 
							+ Utils.comma(task.getPosExamples()) + " positive (" + Utils.truncate(task.totalPosWeight) + " weighted sum) and "
							+ Utils.comma(task.getNegExamples()) + " negative (" + Utils.truncate(task.totalNegWeight) + " wgt'ed) examples.");
				if (task.getMaxNegCoverage() >= 0) {
					out.print(  "////// The minimal (wgt'ed) coverage = " + Utils.truncate(task.getMinPosCoverage(), 3) + ", the maximal (wgt'ed) NEG coverage = " + Utils.truncate(task.getMaxNegCoverage(), 3) + ", and the minimal (wgt'ed) precision = " + Utils.truncate(task.minPrecision, 3));
				}
				else {
					out.print(  "////// The minimal (wgt'ed) coverage = " + Utils.truncate(task.getMinPosCoverage(), 3) + " and the minimal (wgt'ed) precision = " + Utils.truncate(task.minPrecision, 3));
				}
				if (task.getMEstimatePos() != task.getMEstimateNeg()) { out.println(" (using (wgt'ed) m_pos = " + Utils.truncate(task.getMEstimatePos()) + " and m_neg = " + Utils.truncate(task.getMEstimatePos())); }
				else                                                  { out.println(" (using m = " + Utils.truncate(task.getMEstimatePos()) + ")"); }                                    
				
				// Make sure that if this file is read back in, it uses the same conventions as when it was written out.
				out.println("\n" + stringHandler.getStringToIndicateCurrentVariableNotation());
				
				for (Object marker : markerList) {
					String str = "\n////////////////////////////////////////////////////////////////////////////////";
					str       += "\n////";
					str       += "\n////     Gleaner for: " + marker;
					str       += "\n////";
					str       += "\n////////////////////////////////////////////////////////////////////////////////\n";
					out.println(str);
					if (LearnOneClause.debugLevel > 2) { Utils.println(str); }
					Map<Integer,SavedClause> thisGleaner = gleaners.get(marker);
					int  counter = 0;
					double lower = Double.NEGATIVE_INFINITY; 
					for (double upper : recallBinUpperBounds) {
						SavedClause saved = thisGleaner.get(counter);
						if (saved != null) { // Not all bins may have a clause.
							StringBuilder str2 = new StringBuilder("// Best in (weighted) recall bin #" + counter + ", (" + lower + ", " + upper + "], from '" + saved.clauseCreator + "' and covering "
									+ Utils.truncate(saved.posCoverage) + " wgt'ed positive and "
									+ Utils.truncate(saved.negCoverage) + " wgt'ed negative examples:\n"
									+ "//    Wgt'ed recall = " + Utils.truncate(saved.recall, 3) + ", precision = " + Utils.truncate(saved.precision, 3) + ", and F1 = " + Utils.truncate(saved.F1, 3)
									+ " - learned after " + Utils.comma(saved.nodeCountWhenSaved) + " total and " + Utils.comma(saved.acceptableNodeCountWhenSaved) + " acceptable nodes.  Node score = " + saved.score + "\n"
									+ saved.ruleAsString
									+ (saved.annotation != null ? " // " + saved.annotation : "") + "\n"); // TODO - should call handleInlinersIfPossible when the instance is made, but the wasted time shouldn't matter too much.
							if (reportUptoThisManyFalseNegatives > 0 &&  saved.recall >= reportFalseNegativesIfRecallAtLeastThisHigh) {
								Set<Example> uncovered = saved.uncoveredPos;
								if (uncovered != null) for (Example ex : uncovered) {
									Term   annotationTerm = ex.getAnnotationTerm();
									String annotationStr  = (annotationTerm == null ? ex.toPrettyString() : annotationTerm.toPrettyString());
									str2.append("      /* FALSE NEG: ").append(annotationStr.replace("::", "\n                     ")).append(" */\n");
								}
							}
							if (reportUptoThisManyFalsePositives > 0 && saved.precision >= reportFalsePositivesIfPrecisionAtLeastThisHigh) {
								Set<Example> covered =  saved.uncoveredNeg;
								if (covered != null) for (Example ex : covered) {
									Term   annotationTerm = ex.getAnnotationTerm();
									String annotationStr  = (annotationTerm == null ? ex.toPrettyString() : annotationTerm.toPrettyString());
									str2.append("      /* FALSE POS: ").append(annotationStr.replace("::", "\n                     ")).append(" */\n");
								}
							}
							out.println(str2);
							if (LearnOneClause.debugLevel > 2) { Utils.println(str2.toString()); }
						}
						counter ++;
						lower = upper;
					}
				}
	
			}
			catch (FileNotFoundException e) {
				Utils.reportStackTrace(e);
				Utils.error("Unable to successfully open this file for writing: " + fileName + ".  Error message: " + e.getMessage());
			}
		}
	}
	
	/*
	 * dumps the current gleaner with a structured output,
	 * not necessarily human readable, for use with RuleSetVisualizer
	 */
	private void dumpCurrentStructuredGleaner(String fileName, LearnOneClause task) {
		PrintStream      out ;
		CondorFileOutputStream outStream ;
		try {
			outStream = new CondorFileOutputStream(fileName);
			out       = new PrintStream(outStream); // No need for auto-flush.
			
			out.println("<?xml version=\"1.0\"?>");
			out.println("<dataset \nposExamples=\"" 
					+ Utils.comma(task.getPosExamples()) + "\" \nnegExamples=\"" 
					+ Utils.comma(task.getNegExamples()) + "\" \ntotalPosWeight=\"" 
					+ task.totalPosWeight + "\" \ntotalNegWeight=\"" 
					+ task.totalNegWeight + "\"");
			
			if (task.regressionTask) {out.println("regressionTask=\"true\"");} 
			else {out.println("regressionTask=\"false\"");	}
			
			if (task.getMaxNegCoverage() >= 0) {
				out.println("\nminPosCoverage=\"" 
						+ task.getMinPosCoverage() + "\" \nmaxNegCoverage=\"" 
						+ task.getMaxNegCoverage() + "\" \nminPrecision=\"" 
						+ task.minPrecision + "\"");
			}
			else {
				out.println("\nminPosCoverage=\"" 
						+ task.getMinPosCoverage() + "\" \nminPrecision=\"" 
						+ task.minPrecision + "\"");
			}
			if (task.getMEstimatePos() != task.getMEstimateNeg()) { out.println("mEstimatePos=\"" + task.getMEstimatePos() + "\" mEstimateNeg=\"" + task.getMEstimatePos() + "\" "); }
			else                                                  { out.println("mEstimatePos=\"" + task.getMEstimatePos() + "\" "); }                                    
			
			out.println(">"); // Close dataset tag
			String dateFormat = "yyyy-MM-dd HH:mm:ss";
			Calendar cal = Calendar.getInstance();
		    SimpleDateFormat sdf = new SimpleDateFormat(dateFormat);

			out.println("<fileCreated>" + sdf.format(cal.getTime()) + "</fileCreated>");
			out.println("<gleanerFileName>" + fileNameProvider.getGleanerFileName() + "</gleanerFileName>");
			// Make sure that if this file is read back in, it uses the same conventions as when it was written out.
			out.print("<fileConventions ");
			if (stringHandler.doVariablesStartWithQuestionMarks()) { out.print("\nuseLeadingQuestionMarkVariables=\"true\"\n");  } 
			else if (stringHandler.usingStdLogicNotation())        { out.print("\nuseStdLogicNotation=\"true\"\n");  }
			else                                                   { out.print("\nusePrologVariables=\"true\"\n");   }
			out.println(" />");
			
			StringBuilder buffer;
			for (Object marker : markerList) {
				String str = null;
				buffer = new StringBuilder();
				buffer.append("<gleaner><marker>").append(marker).append("</marker>");
				if (LearnOneClause.debugLevel > 2) { Utils.println(str); }
				Map<Integer,SavedClause> thisGleaner = gleaners.get(marker);
				int  counter = 0;
				double lower = Double.NEGATIVE_INFINITY; 
				for (double upper : recallBinUpperBounds) {
					SavedClause saved  = thisGleaner.get(counter);
					if (saved != null) { // Not all bins may have a clause.
						buffer.append("<recallBin binNum=\"").append(counter).append("\" lowerExclusive=\"").append(lower).append("\" upperInclusive=\"").append(upper).append("\">\n");
						buffer.append("<description>").append(saved.clauseCreator).append("</description>\n");
						buffer.append("<clause \nposCoverage=\"").append(saved.posCoverage).append("\"");
						buffer.append(" \nnegCoverage=\"").append(saved.negCoverage).append( "\"");
						buffer.append(" \nprecision=\"").append(saved.precision).append("\"");
						buffer.append(" \nrecall=\"").append(saved.recall).append("\"");
						buffer.append(" \nf1=\"").append(saved.F1).append("\"");
						buffer.append(" \nnodeCountWhenSaved=\"").append(saved.nodeCountWhenSaved).append("\"");
						buffer.append(" \nacceptableNodeCountWhenSaved=\"").append(saved.acceptableNodeCountWhenSaved).append("\"");
						buffer.append(" \nscore=\"").append(saved.score).append("\">");

						buffer.append("\n<clauseText>");
						if (task.regressionTask) {
							buffer.append("\" \reportRegressionRuleAsString=\"").append(saved.ruleAsString).append("\"");
							// TODO - handle inliners here as well
						}
						else {
							if (saved.examplesFlipFlopped) {
								buffer.append("not_");
							}
							buffer.append(saved.ruleAsString);	
						}
						buffer.append("</clauseText>\n");
						if (saved.annotation != null) {
						// TODO - should call handleInlinersIfPossible when the instance is made, but the wasted time shouldn't matter too much.
							buffer.append("<annotation>");
							buffer.append(saved.annotation);
							buffer.append("</annotation>");
						} 
						if (reportUptoThisManyFalseNegatives > 0 && saved.recall >= reportFalseNegativesIfRecallAtLeastThisHigh) {
							Set<Example> uncovered = saved.uncoveredPos;
							
							if (uncovered != null) {
								buffer.append("\n<falseNegatives>\n");
								for (Example ex : uncovered) {
							
									Term   annotationTerm = ex.getAnnotationTerm();
									String annotationStr  = (annotationTerm == null ? ex.toPrettyString() : annotationTerm.toPrettyString());
									
									buffer.append("<falseNegative>\n<annotation>").append(annotationStr.replace("::", "\n")).append("</annotation>\n");
									List<Term> arguments = ex.getArguments();
									StringBuilder fact = new StringBuilder(ex.predicateName.name + "(");
									if (arguments != null){
										for (Term t : arguments) {
											if (t != null) {
												buffer.append("<argument>").append(t.toString()).append("</argument>\n");
												fact.append(t.toString()).append(",");
											}
										}
									}
									buffer.append("<fact>").append(fact.substring(0, fact.length() - 1)).append(")." + "</fact>\n");
									buffer.append("</falseNegative>\n");
									
								}
								buffer.append("</falseNegatives>");
							}
						}
						if (reportUptoThisManyFalsePositives > 0 && saved.precision >= reportFalsePositivesIfPrecisionAtLeastThisHigh) {
							Set<Example> covered = saved.uncoveredNeg;
		
							if (covered != null) {
								buffer.append("\n<falsePositives>\n");
								for (Example ex : covered) {
							
								Term   annotationTerm = ex.getAnnotationTerm();
								String annotationStr  = (annotationTerm == null ? ex.toPrettyString() : annotationTerm.toPrettyString());
								    buffer.append("<falsePositive>\n<annotation>").append(annotationStr.replace("::", "\n")).append("</annotation>\n");
								    buffer.append("<predicateName>").append(ex.predicateName.name).append("</predicateName>\n");
								List<Term> arguments = ex.getArguments();
								StringBuilder fact = new StringBuilder(ex.predicateName.name + "(");
								if (arguments != null){
									for (Term t : arguments) {
										if (t != null) {
											buffer.append("<argument>").append(t.toString()).append("</argument>\n");
											fact.append(t.toString()).append(",");
										}
									}
									}
									buffer.append("<fact>").append(fact.toString(), 0, fact.length() - 1).append(")." + "</fact>\n");
									buffer.append("</falsePositive>\n");
								
								}
								
								buffer.append("</falsePositives>");
							}
						}
						buffer.append("\n</clause>");
						buffer.append("\n</recallBin>");

						if (LearnOneClause.debugLevel > 2) { Utils.println(buffer.toString()); }
					}
					
					counter ++;
					lower = upper;
				}
				buffer.append("\n</gleaner>");
				out.println(buffer.toString());
				out.flush();
			}
			out.println("\n</dataset>\n");
		}
		catch (FileNotFoundException e) {
			Utils.reportStackTrace(e);
			Utils.error("Unable to successfully open this file for writing: " + fileName + ".  Error message: " + e.getMessage());
		}

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
