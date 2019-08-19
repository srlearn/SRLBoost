package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.Utils.Utils;

import java.util.List;

public class ILPparameterSettings {

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

	private int    starModeMap         = default_starModeMap;

	private RelevanceStrength onlyConsiderIfRelevanceLevelAtLeastThisStrong = default_onlyConsiderIfRelevanceLevelAtLeastThisStrong;

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

	ILPparameterSettings(ILPouterLoop outerLooper, TuneParametersForILP caller, String annotationForSetting) {
		this.outerLooper = outerLooper;
		this.caller      = caller;
		this.annotationForSetting = annotationForSetting;
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
