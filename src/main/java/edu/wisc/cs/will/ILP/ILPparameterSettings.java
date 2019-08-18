package edu.wisc.cs.will.ILP;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.FOPC.RelevantLiteral;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.Utils.MessageType;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

public class ILPparameterSettings {
	protected final static int debugLevel = 1; // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).
	
	public TuneParametersForILP caller;
	ILPouterLoop    outerLooper;
	private boolean flipFlopPosAndNegExamples = false;
	private boolean reconsideredSetting       = false; // Mark if this setting has been corrupted from its initial version.
	private String  annotationForSetting;  // Used to provide a (presumably) short string that 'describes' this setting.
	
	// By using constants, the toString() is able to report only those settings that ARE DIFFERENT FROM THEIR DEFAULTS.
	private final static int default_maxNumberOfCycles      =   250; // Will only consider this many calls to the ILP inner loop.
	private final static int default_maxNumberOfClauses     =   100; // Similar to above, but only counts cases where an acceptable clause was produced.
	private final static int default_maxBodyLength          =    10;
	private final static int default_maxNodesToConsider     =  5000;
	private final static int default_maxNodesToCreate       = 25000;
	private final static int default_minNumberOfNegExamples =     1; // TODO - can use this to weed out some pseudo negatives.
	
	private final static double default_minPosCoverage      = 0.25; // This is a FRACTION of |examples| in (0,1).
	private final static double default_maxNegCoverage      = default_minPosCoverage; // This is an ABSOLUTE number if >= 1.
	private final static double default_minPrecision        = 0.50;
	private final static double default_mEstimatePos        = 0.1;
	private final static double default_mEstimateNeg        = 0.1;	
	private final static double default_minPrecisionToStop  = 0.99; // Depending on some flags, only one of these should matter.
	private final static double default_minRecallToStop     = 0.99;	
	private final static double default_minF1toStop         = 0.99;
	private final static double default_minAccuracyToStop   = 0.99;
	
	private final static int    default_starModeMap         = TypeSpec.plusMode;

	private  final static RelevanceStrength default_onlyConsiderIfRelevanceLevelAtLeastThisStrong = null;	
	
	private int maxNumberOfCycles      = default_maxNumberOfCycles;
	private int maxNumberOfClauses     = default_maxNumberOfClauses;
	private int maxBodyLength          = default_maxBodyLength;
	private int maxNodesToCreate       = default_maxNodesToCreate;
	private int maxNodesToConsider     = default_maxNodesToConsider;
	private int minNumberOfNegExamples = default_minNumberOfNegExamples;
	
	private double minPosCoverage      = default_minPosCoverage;
	private double maxNegCoverage      = default_maxNegCoverage;
	private double minPrecision        = default_minPrecision;
	private double mEstimatePos        = default_mEstimatePos;
	private double mEstimateNeg        = default_mEstimateNeg;		
	private double minPrecisionToStop  = default_minPrecisionToStop;		
	private double minRecallToStop     = default_minRecallToStop;	
	private double minF1ToStop         = default_minF1toStop;
	private double minAccuracyToStop   = default_minAccuracyToStop;
	
	private int    starModeMap         = default_starModeMap;

	private RelevanceStrength onlyConsiderIfRelevanceLevelAtLeastThisStrong = default_onlyConsiderIfRelevanceLevelAtLeastThisStrong;

	// Can override the TuneParametersForILP general loop on a per-setting basis.
	private boolean runAllAsTrainSet   = false;
	private boolean runCrossValidation = true;

	// These are used to restore to the settings before this instance's settings were assigned.
	private int    hold_maxNumberOfCycles;
	private int    hold_maxNumberOfClauses;
	private int    hold_maxBodyLength;
	private int    hold_maxNodesToCreate;
	private int    hold_maxNodesToConsider;
	private int    hold_minNumberOfNegExamples;
	private double hold_minPosCoverage;
	private double hold_maxNegCoverage;
	private double hold_minPrecision;
	private double hold_mEstimatePos;
	private double hold_mEstimateNeg;	
	private List<PredicateNameAndArity> save_knownModes = null; // Used if these parameter settings restricts the modes under consideration.
	private List<PredicateNameAndArity> used_knownModes = null;
	private boolean haveSetModesToUse = false;

    private int onionLayer;
	
	ILPparameterSettings(ILPouterLoop outerLooper, TuneParametersForILP caller, String annotationForSetting) {
		this.outerLooper = outerLooper;
		this.caller      = caller;
		this.annotationForSetting = annotationForSetting;
	}
	
	CrossValidationResult runAllAsTrainSet(double stopIfPrecisionCannotMeetOrExceedThis, double stopIfRecallCannotMeetOrExceedThis, double stopIfAccuracyCannotMeetOrExceedThis, double stopIfFScoreCannotMeetOrExceedThis, long maximumTimeInMilliseconds) throws SearchInterrupted {
		ILPCrossValidationLoop cv = new ILPCrossValidationLoop(outerLooper, 1);
		return helpRun(cv, stopIfPrecisionCannotMeetOrExceedThis, stopIfRecallCannotMeetOrExceedThis, stopIfAccuracyCannotMeetOrExceedThis, stopIfFScoreCannotMeetOrExceedThis, maximumTimeInMilliseconds);
	}

	CrossValidationResult runCrossValidation(double stopIfPrecisionCannotMeetOrExceedThis, double stopIfRecallCannotMeetOrExceedThis, double stopIfAccuracyCannotMeetOrExceedThis, double stopIfFScoreCannotMeetOrExceedThis, long maximumTimeInMilliseconds) throws SearchInterrupted {
		int folds = caller.getNumberOfFoldsToUse();
		ILPCrossValidationLoop cv = new ILPCrossValidationLoop(outerLooper, folds);
		return helpRun(cv, stopIfPrecisionCannotMeetOrExceedThis, stopIfRecallCannotMeetOrExceedThis, stopIfAccuracyCannotMeetOrExceedThis, stopIfFScoreCannotMeetOrExceedThis, maximumTimeInMilliseconds);
	}
	
	CrossValidationResult runWithSpecifiedTrainTuneSplit(double firstTrain, double lastTrain, double firstTune, double lastTune, double stopIfPrecisionCannotMeetOrExceedThis, double stopIfRecallCannotMeetOrExceedThis, double stopIfAccuracyCannotMeetOrExceedThis, double stopIfFScoreCannotMeetOrExceedThis, long maximumTimeInMilliseconds) throws SearchInterrupted {
		SingleFoldPartialSplitExampleSet exampleSets = new SingleFoldPartialSplitExampleSet(outerLooper.getPosExamples(), outerLooper.getNegExamples(), firstTrain, lastTrain, firstTune, lastTune);
        ILPCrossValidationLoop cv = new ILPCrossValidationLoop(outerLooper, 1, exampleSets);
    	return helpRun(cv, stopIfPrecisionCannotMeetOrExceedThis, stopIfRecallCannotMeetOrExceedThis, stopIfAccuracyCannotMeetOrExceedThis, stopIfFScoreCannotMeetOrExceedThis, maximumTimeInMilliseconds);
    }
	
	
	private CrossValidationResult helpRun(ILPCrossValidationLoop cv, double stopIfPrecisionCannotMeetOrExceedThis, double stopIfRecallCannotMeetOrExceedThis, double stopIfAccuracyCannotMeetOrExceedThis, double stopIfFScoreCannotMeetOrExceedThis, long maximumTimeInMilliseconds) throws SearchInterrupted  {

        CrossValidationResult result = null;

        setParameters();
		cv.setEarlyStoppingCondition( new CVMaximumObtainableAverageCoverageStoppingCondition(stopIfPrecisionCannotMeetOrExceedThis, stopIfRecallCannotMeetOrExceedThis));
		cv.setFlipFlopPositiveAndNegativeExamples(flipFlopPosAndNegExamples);
        cv.setMaximumCrossValidationTimeInMillisec(maximumTimeInMilliseconds);
        Utils.println("% ILPparameterSettings.helpRun: annotationForSetting = " + annotationForSetting);
		cv.getOuterLoop().setAnnotationForCurrentRun(annotationForSetting);
		cv.getOuterLoop().minimalAcceptablePrecision = stopIfPrecisionCannotMeetOrExceedThis; // When more than clause is being learned, can stop based on upper bounds of performance on the theory as a whole.
		cv.getOuterLoop().minimalAcceptableRecall    = stopIfRecallCannotMeetOrExceedThis;
		cv.getOuterLoop().minimalAcceptableAccuracy  = stopIfAccuracyCannotMeetOrExceedThis;
		cv.getOuterLoop().minimalAcceptableF1        = stopIfFScoreCannotMeetOrExceedThis;
		
		try {
			cv.executeCrossValidation();
            result = cv.getCrossValidationResults();
		} catch (EarlyStoppingConditionMet e) {
            Utils.println("Early stopping condition met during cross-validation.");
		}
        finally {
            resetParameters(); // This might lead to some warning because the run changed what some values are and the held parameters might now be infeasible (e.g., the max precision might be too high).  But that is OK.
        }

        return result;
	}
	
	void setModesToUse() {
		// Seems the following can be called once-and-for-all rather than when setting used.  If need be, call initially and again later.
		// This could be spend up by using some hashes.  Currently it is quadratic (i.e., two embedded FOR loops).
		HandleFOPCstrings stringHandler = outerLooper.innerLoopTask.stringHandler;
		save_knownModes = stringHandler.getKnownModes();
		used_knownModes = save_knownModes; // Set this here in case the IF below is skipped (i.e, all modes should be used).
		if (onlyConsiderIfRelevanceLevelAtLeastThisStrong != null && save_knownModes != null &&
			onlyConsiderIfRelevanceLevelAtLeastThisStrong.compareTo(RelevanceStrength.getWeakestRelevanceStrength()) > 0) { // If all acceptable, don't bother to filter.
			used_knownModes = new ArrayList<>(4);

			if (Utils.getSizeSafely(caller.relevantLiterals) < 1) { Utils.error("Should have some relevant features if this is being considered."); }
			// Keep a mode if (a) we want 'positive' relevance and this has ENOUGH positive relevance (so modes without any relevance will be discarded) 
			//             or (b) we want to limit the negative relevance, and this does not have too much 'irrelevance' (so modes without any relevance will be kept)
			boolean keepModesWithNoRelevanceMatch = onlyConsiderIfRelevanceLevelAtLeastThisStrong.compareTo(RelevanceStrength.NEUTRAL) <= 0;
			for (PredicateNameAndArity       pName    : save_knownModes) {
				boolean matchesRelevanceStmt = false;
				for (RelevantLiteral relevant : caller.relevantLiterals) {
					// TODO IF WE WANT TO SAY RELEVANT FOR THE SPECIFIC ARITY, WILL NEED TO REWRITE CODE AT A FINER GRAIN.  TODO
					if (relevant.getPredicateNameAndArity().equals(pName)) {
						matchesRelevanceStmt = true;
						if (relevant.atLeastThisRelevant(onlyConsiderIfRelevanceLevelAtLeastThisStrong)) {
							if (!used_knownModes.contains(pName)) { used_knownModes.add(pName); }
						}
					}
				}
				if (!matchesRelevanceStmt && keepModesWithNoRelevanceMatch && !used_knownModes.contains(pName)) {
					used_knownModes.add(pName);
				}
			}
		}
		haveSetModesToUse = true;
	}
	
	private void setParameters() {
		if (!haveSetModesToUse) { setModesToUse(); }
		hold_maxNumberOfCycles      = outerLooper.maxNumberOfCycles;
		hold_maxNumberOfClauses     = outerLooper.maxNumberOfClauses;
		hold_maxBodyLength          = outerLooper.innerLoopTask.maxBodyLength;
		hold_maxNodesToCreate       = outerLooper.innerLoopTask.getMaxNodesToCreate();
		hold_maxNodesToConsider     = outerLooper.innerLoopTask.getMaxNodesToConsider();
		hold_minNumberOfNegExamples = outerLooper.innerLoopTask.minNumberOfNegExamples;
		hold_minPosCoverage         = outerLooper.innerLoopTask.getMinPosCoverage();
		hold_maxNegCoverage         = outerLooper.innerLoopTask.getMaxNegCoverage();
		hold_minPrecision           = outerLooper.innerLoopTask.getMinPrecision();
		hold_mEstimatePos           = outerLooper.innerLoopTask.getMEstimatePos();
		hold_mEstimateNeg           = outerLooper.innerLoopTask.getMEstimateNeg();
		
		outerLooper.maxNumberOfCycles                = maxNumberOfCycles;
		outerLooper.maxNumberOfClauses               = maxNumberOfClauses;
		outerLooper.innerLoopTask.maxBodyLength      = maxBodyLength;
		outerLooper.innerLoopTask.setMaxNodesToCreate(maxNodesToCreate);
		outerLooper.innerLoopTask.setMaxNodesToConsider(maxNodesToConsider);
		outerLooper.innerLoopTask.minNumberOfNegExamples = minNumberOfNegExamples;
		outerLooper.innerLoopTask.setMinPosCoverage(minPosCoverage);
		outerLooper.innerLoopTask.setMaxNegCoverage(maxNegCoverage);
		outerLooper.innerLoopTask.setMinPrecision(  minPrecision);
		outerLooper.innerLoopTask.setMEstimatePos(  mEstimatePos);
		outerLooper.innerLoopTask.setMEstimateNeg(  mEstimateNeg);
		outerLooper.innerLoopTask.stringHandler.setStarMode(starModeMap);
		outerLooper.innerLoopTask.resetModes(used_knownModes);
        outerLooper.innerLoopTask.setCurrentRelevanceStrength(onlyConsiderIfRelevanceLevelAtLeastThisStrong);
	}
	
	// TODO - use some hashing to make this faster (ditto for code above).
	// Keep this near setParameters since these two share the double for loop.
	static boolean modeExistsNotInTheseRelevances(Set<RelevantLiteral> relevantLiterals, List<PredicateNameAndArity> modes) {
		for (PredicateNameAndArity       pnaa    : modes) {
            PredicateName pName = pnaa.getPredicateName();
			boolean matchesRelevanceStmt = false;
			for (RelevantLiteral relevant : relevantLiterals) { // TODO since RelevantLiteral is now a SET, should be able to define EQUALS and use contains.
				if (relevant.getPName() == pName) { matchesRelevanceStmt = true; break; }
			}
			if (!matchesRelevanceStmt) { return true; } // Found SOME mode that matches no relevance statement.
		}
		return false;
	}

	private void resetParameters() {
		outerLooper.maxNumberOfCycles                = hold_maxNumberOfCycles;
		outerLooper.maxNumberOfClauses               = hold_maxNumberOfClauses;
		outerLooper.innerLoopTask.maxBodyLength      = hold_maxBodyLength;
		outerLooper.innerLoopTask.setMaxNodesToCreate(hold_maxNodesToCreate);
		outerLooper.innerLoopTask.setMaxNodesToConsider(hold_maxNodesToConsider);
		outerLooper.innerLoopTask.minNumberOfNegExamples = hold_minNumberOfNegExamples;
		outerLooper.innerLoopTask.setMinPosCoverage(hold_minPosCoverage);
		outerLooper.innerLoopTask.setMaxNegCoverage(hold_maxNegCoverage);
		outerLooper.innerLoopTask.setMinPrecision(  hold_minPrecision);
		outerLooper.innerLoopTask.setMEstimatePos(  hold_mEstimatePos);
		outerLooper.innerLoopTask.setMEstimateNeg(  hold_mEstimateNeg);
		if (save_knownModes != null) { outerLooper.innerLoopTask.stringHandler.setKnownModes(save_knownModes); } // Restore the known modes if they were temporarily altered.
	}
	
	void onlyConsiderFeaturesAtLeastThisRelevant(RelevanceStrength minRelStrength) {
		onlyConsiderIfRelevanceLevelAtLeastThisStrong = minRelStrength;		
	}

	void setMaxNumberOfCycles(int maxNumberOfCycles) {
		this.maxNumberOfCycles = maxNumberOfCycles;
	}

	int getMaxBodyLength() {
		return maxBodyLength;
	}

	void setMaxBodyLength(int maxBodyLength) {
		this.maxBodyLength = maxBodyLength;
	}

	void setMaxNodesToCreate(int maxNodesToCreate) {
		this.maxNodesToCreate = maxNodesToCreate;
	}

	public void setMaxNodesToConsider(int maxNodesToConsider) {
		this.maxNodesToConsider = maxNodesToConsider;
	}

	void setMinPosCoverage(double minPosCoverage) {
		this.minPosCoverage = minPosCoverage;
	}

	void setMaxNegCoverage(double maxNegCoverage) {
		this.maxNegCoverage = maxNegCoverage;
	}

	boolean isRunAllAsTrainSet() {
		return runAllAsTrainSet;
	}

	void setRunAllAsTrainSet(boolean runAllAsTrainSet) {
		this.runAllAsTrainSet = runAllAsTrainSet;
	}

	boolean isRunCrossValidation() {
		return runCrossValidation;
	}

	void setRunCrossValidation(boolean runCrossValidation) {
		this.runCrossValidation = runCrossValidation;
	}

	void setFlipFlopPosAndNegExamples(boolean flipFlopPosAndNegExamples) {
		this.flipFlopPosAndNegExamples = flipFlopPosAndNegExamples;
	}

	int getMaxNumberOfClauses() {
		return maxNumberOfClauses;
	}

	void setMaxNumberOfClauses(int maxNumberOfClauses) {
		this.maxNumberOfClauses = maxNumberOfClauses;
	}

	void setMinPrecision(double minPrecision) {
		this.minPrecision = minPrecision;
	}

	void setMEstimatePos(double estimatePos) {
		mEstimatePos = estimatePos;
	}

	void setMEstimateNeg(double estimateNeg) {
		mEstimateNeg = estimateNeg;
	}

	void setStarModeMap(int starModeMap) {
		this.starModeMap = starModeMap;
	}

	void markAsReconsidered() {
		reconsideredSetting = true;
	}


	double getMinPrecisionToStop() {
		return minPrecisionToStop;
	}
	void setMinPrecisionToStop(double minPrecisionToStop) {
		if (this.minPrecisionToStop != minPrecisionToStop) { Utils.println(MessageType.ONION_VERBOSE_LAYER_CREATION,"% setMinPrecisionToStop = " + minPrecisionToStop); }
		this.minPrecisionToStop = minPrecisionToStop;
	}

	double getMinRecallToStop() {
		return minRecallToStop;
	}
	void setMinRecallToStop(double minRecallToStop) {
		if (this.minRecallToStop != minRecallToStop) { Utils.println(MessageType.ONION_VERBOSE_LAYER_CREATION,"% setMinRecallToStop = " + minRecallToStop); }
		this.minRecallToStop = minRecallToStop;
	}

	double getMinF1toStop() {
		return minF1ToStop;
	}
	void setMinF1toStop(double minF1ToStop) {
		if (this.minF1ToStop != minF1ToStop) { Utils.println(MessageType.ONION_VERBOSE_LAYER_CREATION,"% setMinF1toStop = " + minF1ToStop); }
		this.minF1ToStop = minF1ToStop;
	}

	double getMinAccuracyToStop() {
		return minAccuracyToStop;
	}
	void setMinAccuracyToStop(double minAccuracyToStop) {
		if (this.minAccuracyToStop != minAccuracyToStop) { Utils.println(MessageType.ONION_VERBOSE_LAYER_CREATION, "%   setMinAccuracyToStop = " + minAccuracyToStop); }
		this.minAccuracyToStop = minAccuracyToStop;
	}

	int getOnionLayer() {
        return onionLayer;
    }

    void setOnionLayer(int onionLayer) {
        this.onionLayer = onionLayer;
    }

    

	String toStringShort() {
		String result = ("MinRelevance(" + onlyConsiderIfRelevanceLevelAtLeastThisStrong + (flipFlopPosAndNegExamples ? ")/Flipped(true)" : ")") +
							"/MaxLen("    + maxBodyLength       + ")" +
							"/MaxClauses(" + maxNumberOfClauses + ")" +
							"/MinPrec("    + Utils.truncate(minPrecision, 4)   + ")" +
							"/MaxExpands(" + maxNodesToConsider + ")" +
							"/MaxCreates(" + maxNodesToCreate   + ")" +
							"/MinPos("     + Utils.truncate(minPosCoverage, 2) + ")" +
							"/MaxNegs("    + Utils.truncate(maxNegCoverage, 2) + ")");

		if (reconsideredSetting) { result += "  This setting was reconsidered (and relaxed) after it didn't suffice initially."; }
		return result;
	}

    @Override
	public String toString() {
		return toString(false);
	}
	public String toString(boolean reportAllValues) {
		String result = (reportAllValues ? "" : "%  The differences from the default settings are:");

		if (flipFlopPosAndNegExamples) { result += "\n%   positive and negative examples are flip-flopped"; }
		if (reconsideredSetting)       { result += "\n%   this setting was reconsidered (and relaxed) after it didn't suffice initially"; }

		if (reportAllValues || maxNumberOfCycles      != default_maxNumberOfCycles)      result += "\n%   maxNumberOfCycles  = "     + Utils.comma(maxNumberOfCycles);
		if (reportAllValues || maxNumberOfClauses     != default_maxNumberOfClauses)     result += "\n%   maxNumberOfClauses = "     + Utils.comma(maxNumberOfClauses);
		if (reportAllValues || maxBodyLength          != default_maxBodyLength)          result += "\n%   maxBodyLength      = "     + Utils.comma(maxBodyLength);
		if (reportAllValues || maxNodesToCreate       != default_maxNodesToCreate)       result += "\n%   maxNodesToCreate   = "     + Utils.comma(maxNodesToCreate);
		if (reportAllValues || maxNodesToConsider     != default_maxNodesToConsider)     result += "\n%   maxNodesToConsider = "     + Utils.comma(maxNodesToConsider);
		if (reportAllValues || minNumberOfNegExamples != default_minNumberOfNegExamples) result += "\n%   minNumberOfNegExamples = " + Utils.comma(minNumberOfNegExamples);

		if (reportAllValues || minPosCoverage         != default_minPosCoverage)         result += "\n%   minPosCoverage     = "     + Utils.truncate(minPosCoverage, 4);
		if (reportAllValues || maxNegCoverage         != default_maxNegCoverage)         result += "\n%   maxNegCoverage     = "     + Utils.truncate(maxNegCoverage, 4);
		if (reportAllValues || minPrecision           != default_minPrecision)           result += "\n%   minPrecision       = "     + Utils.truncate(minPrecision,   4);
		if (reportAllValues || mEstimatePos           != default_mEstimatePos)           result += "\n%   mEstimatePos       = "     + Utils.truncate(mEstimatePos,   4);
		if (reportAllValues || mEstimateNeg           != default_mEstimateNeg)           result += "\n%   mEstimateNeg       = "     + Utils.truncate(mEstimateNeg,   4);

		if (reportAllValues || onlyConsiderIfRelevanceLevelAtLeastThisStrong != default_onlyConsiderIfRelevanceLevelAtLeastThisStrong)  result += "\n%   minimum strength   = " + onlyConsiderIfRelevanceLevelAtLeastThisStrong;
		if (reportAllValues || starModeMap != default_starModeMap)  result += "\n%   map mode '*' to '" + TypeSpec.getModeString(starModeMap) + "'";

		result += "\n%   modes in use: " + Utils.limitLengthOfPrintedList(used_knownModes, 100);
		result += "\n%   all modes:    " + Utils.limitLengthOfPrintedList(save_knownModes, 100);
		return result;
	}

}
