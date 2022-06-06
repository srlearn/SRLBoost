package edu.wisc.cs.will.Boosting.Utils;

import edu.wisc.cs.will.Utils.Utils;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

// TODO(@hayesall): Replace this with an actual commandline parser.

public class CommandLineArguments {

	public CommandLineArguments() {
		super();
	}

	/*
	 * Steps to add new arguments
	 * 1. Define a "static final" string for the flag
	 * 2. Define a variable that is set by the flag
	 * 3. Create a getter and setter for the variable.
	 * 4. Set the value of the variable from the flags in parseArgs
	 * 5. Define a usage string in getUsageString
	 */

	public static final String srlboost_version = "0.2.0";

	private static final String argPrefix = "-";
	private static final String learn = "l";

	// Divide inference examples into this many bins.  THIS IS NEEDED WHEN THE SIZE OF A TESTSET IS TOO LARGE.
	public static int modN = 10;

	private static final String indicatorOfModN = "useMod";

	// Need to turn this off when using Condor.
	public boolean useLockFiles = true;
	
	private boolean learnVal = false;

	private static final String useMLN = "mln";
	private boolean learnMLN=false;

	private static final String useSoftM = "softm";
	private boolean SoftM=false;
	
	private static final String alphaFlag="alpha";
	private double alpha=0;
	
	private static final String betaFlag="beta";
	private double beta=0;

	private static final String learnMLNClauses = "mlnClause";
	private boolean learningMLNClauses=false;
	
	private static final String numMLNClauses = "numMLNClause";
	private int numberOfMLNClauses=5;
	
	private static final String maxMLNLength = "mlnClauseLen";
	private int maxMLNClauseLength=2;

	private static final String rdnIterFlag = "iter";
	private int rdnIterationStep = -1;

	private static final String learnCurve = "lc";
	private boolean printLearningCurve = false;

	private static final String outName = "outSuffix";
	public String outFileSuffix = null;

	private static final String infer = "i";
	private boolean inferVal=false;

	private static final String noBoosting = "noBoost";
	private boolean disabledBoosting=false;

	private static final String trainDir = "train";
	private String trainDirVal;

	private static final String testDir = "test";
	private String testDirVal;

	private static final String modelDir = "model";
	private String modelDirVal = null;
	
	private static final String resultsDir = "results";
	private String resultsDirVal = null;

	private static final String targetPred = "target";
	private Set<String> targetPredVal = null;

	private static final String loadModelPredFlag = "loadPredModel";
	private Set<String> loadPredModelVal = null;

	private static final String maxTrees = "trees";
	private int maxTreesVal=10;

	private static final String disableJointModel = "noJointModel";
	private boolean jointModelDisabled =false;

	private static final String disableChkPtFlag = "disableChkPts";
	private boolean noCheckPointing=false;

	private static final String regressionFlag = "reg";
	private boolean learnRegression = false;

	private static final String probFlag = "probEx";
	private boolean learnProbExamples = false;

	private static final String disableMultiClassFlag = "noMulti";
	private boolean disableMultiClass = false;

	private static final String maxInteriorNodeLits = "maxNodeLits";
	private int maxLiteralsInAnInteriorNodeVal = 1;

	private static final String bagOriginalExamplesKey   = "bag";
	private static final String noBagOriginalExamplesKey = "noBag";
	private boolean bagOriginalExamples = false;

	private static final String stepLen = "step";
	private double stepLenVal =1;

	private static final String sampleNegsToPosRatio = "negPosRatio";
	private double sampleNegsToPosRatioVal = 2;

	private static final String testNegsToPosRatio = "testNegPosRatio";
	private double testNegsToPosRatioVal = -1;

	private static final String aucPath = "aucJarPath";
	private String aucPathVal = null;

	private static final String modelName = "modelSuffix";
	private String modelFileVal = null;


	private static final String samplePosProb = "samplePositive";
	private double samplePosProbVal = -1.0;

	private static final String reweighEx = "reweigh";
	public boolean reweighExamples = false;

	public boolean parseArgs(String[] args) {

		for (int i = 0; i < args.length; i++) {

			if (args[i].trim().isEmpty())
				continue;

			if (argMatches(args[i], "v") || argMatches(args[i], "version")) {
				System.out.println(srlboost_version);
				System.exit(0);
			}

			if (argMatches(args[i], "h") || argMatches(args[i], "help")) {
				System.out.println(getUsageString());
				System.exit(0);
			}

			if (argMatches(args[i], "noLockFiles")) {
				useLockFiles = false;
				continue;
			}

			if (argMatches(args[i], indicatorOfModN)) {
				modN = Integer.parseInt(args[++i]);
				continue;
			}
			if (argMatches(args[i], useMLN)) {
				learnMLN = true;
				continue;
			}
			if (argMatches(args[i], useSoftM)) {
				SoftM = true;
				continue;
			}
			
			if (argMatches(args[i], alphaFlag)) {
				alpha=Double.parseDouble(args[++i]);
				continue;
			}
	
			if (argMatches(args[i], betaFlag)) {
				beta=Double.parseDouble(args[++i]);
				continue;
			}

			if (argMatches(args[i], learnCurve)) {
				printLearningCurve = true;
				if (isArgumentNotAFlag(args, i+1)) {
					printLearningCurve = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], disableChkPtFlag)) {
				noCheckPointing = true;
				if (isArgumentNotAFlag(args, i+1)) {
					noCheckPointing = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], rdnIterFlag)) {
				rdnIterationStep = Integer.parseInt(args[++i]);
				continue;
			}
			
			if (argMatches(args[i], learnMLNClauses)) {
				learningMLNClauses = true;
				if (isArgumentNotAFlag(args, i+1)) {
					learningMLNClauses = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], numMLNClauses)) {
				numberOfMLNClauses=Integer.parseInt(args[++i]);
				continue;
			}
			if (argMatches(args[i], maxMLNLength)) {
				maxMLNClauseLength=Integer.parseInt(args[++i]);
				continue;
			}
			if (argMatches(args[i], reweighEx)) {
				reweighExamples=true;
				continue;
			}
			if (argMatches(args[i], outName)) {
				outFileSuffix = args[++i];
				continue; 
			}
			if (argMatches(args[i], learn)) {
				learnVal = true;
				if (isArgumentNotAFlag(args, i+1)) {
					learnVal = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], infer)) {
				inferVal = true;
				if (isArgumentNotAFlag(args, i+1)) {
					inferVal = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], disableJointModel)) {
				jointModelDisabled = true;
				if (isArgumentNotAFlag(args, i+1)) {
					jointModelDisabled = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], disableMultiClassFlag)) {
				disableMultiClass = true;
				if (isArgumentNotAFlag(args, i+1)) {
					disableMultiClass = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], bagOriginalExamplesKey)) {
				bagOriginalExamples = true;
				if (isArgumentNotAFlag(args, i+1)) {
					bagOriginalExamples = Utils.parseBoolean(args[++i]);
				}
				continue;
			}		
			if (argMatches(args[i], noBagOriginalExamplesKey)) {
				bagOriginalExamples = false;
				continue;
			}
			if (argMatches(args[i], noBoosting)) {
				disabledBoosting = true;
				if (isArgumentNotAFlag(args, i+1)) {
					disabledBoosting = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], trainDir)) {
				setTrainDirVal(args[++i]);
				continue;
			}
			if (argMatches(args[i], testDir)) {
				setTestDirVal(args[++i]);
				continue;
			}
			if (argMatches(args[i], modelDir)) {
				setModelDirVal(args[++i]);
				continue; 
			}
			if (argMatches(args[i], resultsDir)) {
				setResultsDirVal(args[++i]);
				continue; 
			}
			if (argMatches(args[i], targetPred)) {
				String targetStr = args[++i];
				targetPredVal = new HashSet<>();
				targetPredVal.addAll(Arrays.asList(targetStr.split(",")));
				continue;
			}
			if (argMatches(args[i], loadModelPredFlag)) {
				String targetStr = args[++i];
				loadPredModelVal = new HashSet<>();
				loadPredModelVal.addAll(Arrays.asList(targetStr.split(",")));
				continue;
			}
			if (argMatches(args[i], regressionFlag)) {
				learnRegression=true;
				if (isArgumentNotAFlag(args, i+1)) {
					learnRegression = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], probFlag)) {
				learnProbExamples=true;
				if (isArgumentNotAFlag(args, i+1)) {
					learnProbExamples = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], maxInteriorNodeLits)) {
				maxLiteralsInAnInteriorNodeVal=Integer.parseInt(args[++i]);
				continue;
			}
			if (argMatches(args[i], maxTrees)) {
				maxTreesVal=Integer.parseInt(args[++i]);
				continue;
			}
			if (argMatches(args[i], stepLen)) {
				stepLenVal=Double.parseDouble(args[++i]);
				continue;
			}
			if (argMatches(args[i], sampleNegsToPosRatio)) {
				sampleNegsToPosRatioVal=Double.parseDouble(args[++i]);
				continue;
			}
			if (argMatches(args[i], testNegsToPosRatio)) {
				testNegsToPosRatioVal=Double.parseDouble(args[++i]);
				continue;
			}
			if (argMatches(args[i], samplePosProb)) {
				samplePosProbVal=Double.parseDouble(args[++i]);
				continue;
			}
				
			if (argMatches(args[i], aucPath)) {
				aucPathVal = args[++i];
				continue;
			}			
			if (argMatches(args[i], modelName)) {
				modelFileVal = args[++i];
				continue;
			}

			Utils.println("Unknown argument: " + args[i]);
			return false;
		}
		
		return true;
	}

	/*
	 * Returns true if there is an argument at "index" and it is not a flag. It uses startsWith("-") to determine
	 * if the next argument is a flag. So make sure to use it only for checking if boolean flags have 
	 * an argument that follows it as that would not begin with "-"
	 * @param args Arguments 
	 * @param index Position to look at
	 */
	private static boolean isArgumentNotAFlag(String[] args, int index) {
		if (args.length > index) {
			return !args[index].startsWith("-");
		}
		return false;
	}
	
	public static String getUsageString() {
		String result = "Usage:\n";
		
		result += argPrefix + learn + " : Use this flag, if you want to enable learning.\n";
		
		result += argPrefix + infer + " : Use this flag, if you want to enable inference.\n";

		result += argPrefix + noBoosting + " : Use this flag, if you dont want to use boosting.\n";
		
		result += argPrefix + trainDir + " <Training directory> : Path to the training directory in WILL format.\n";
		
		result += argPrefix + testDir + " <Testing directory> : Path to the testing directory in WILL format.\n";
		
		result += argPrefix + modelDir + " <Model directory> : Path to the directory with the stored models[or where they will be stored].\n";

		result += argPrefix + targetPred + " <target predicates> : Comma separated list of predicates that need to be learned/inferred.\n";

		result += argPrefix + maxTrees + " <Number of trees>: Number of boosting trees.\n";
		
		result += argPrefix + maxInteriorNodeLits +  " <Max number of literals at an interior node>: Max number of literals in an interior node.\n";
		
		result += argPrefix + stepLen + " <Step Length>: Default step length for functional gradient.\n";
		
		result += argPrefix + testNegsToPosRatio + " <Negative/Positive ratio>: Ratio of negatives to positive for testing.\n";
		
		return result;
	}
	
	private boolean argMatches(String arg, String constant) {
		return arg.compareToIgnoreCase(argPrefix + constant) == 0;
	}

	public boolean isLearnVal() {
		return learnVal;
	}

	public boolean isInferVal() {
		return inferVal;
	}

	private boolean checked_trainDirVal = false;

	public boolean isDisabledBoosting() {
		return disabledBoosting;
	}

	public String getTrainDirVal() {
		if (!checked_trainDirVal && trainDirVal != null) {
			checked_trainDirVal = true;
		}
		return trainDirVal;
	}

	private void setTrainDirVal(String trainDirVal) {
		checked_trainDirVal = true;
		if (!(trainDirVal.endsWith("/") || trainDirVal.endsWith("\\"))) {  trainDirVal += "/"; }
		this.trainDirVal = trainDirVal;
	}

	private boolean checked_testDirVal = false;

	public String getTestDirVal() {
		if (!checked_testDirVal && testDirVal != null) {
			checked_testDirVal = true;
		}
		return testDirVal;
	}

	private void setTestDirVal(String testDirVal) {
		checked_testDirVal = true;
		if (!(testDirVal.endsWith("/") || testDirVal.endsWith("\\"))) {  testDirVal += "/"; }
		this.testDirVal = testDirVal;
	}
	
	public boolean isLearningMLNClauses() {
		return learningMLNClauses;
	}

	public int getNumberOfMLNClauses() {
		return numberOfMLNClauses;
	}

	public int getMaxMLNClauseLength() {
		return maxMLNClauseLength;
	}

	public boolean isPrintLearningCurve() {
		return printLearningCurve;
	}

	public boolean getBagOriginalExamples() {
		return bagOriginalExamples;
	}

	public boolean useCheckPointing() {
		return !noCheckPointing;
	}

	private boolean checked_modelDirVal = false;

	public String getModelDirVal() {
		if (!checked_modelDirVal && modelDirVal != null) {
			checked_modelDirVal = true;
		}
		return modelDirVal;
	}

	public void setModelDirVal(String modelDirVal) {
		checked_modelDirVal = true;
		if (!(modelDirVal.endsWith("/") || modelDirVal.endsWith("\\"))) {  modelDirVal += "/"; }
		this.modelDirVal = modelDirVal;
	}

	private boolean checked_resultsDirVal = false;

	public String getResultsDirVal() {
		if (!checked_resultsDirVal && resultsDirVal != null) {
			checked_resultsDirVal = true;
		}
		return resultsDirVal;
	}

	public void setResultsDirVal(String resultsDirVal) {
		checked_resultsDirVal = true;
		if (!(resultsDirVal.endsWith("/") || resultsDirVal.endsWith("\\"))) {  resultsDirVal += "/"; }
		this.resultsDirVal = resultsDirVal;
	}

	public String getModelFileVal() {
		return modelFileVal;
	}

	public void setModelFileVal(String modelFileVal) {
		this.modelFileVal = modelFileVal;
	}

	public Set<String> getTargetPredVal() {
		return targetPredVal;
	}

	public boolean isDisableMultiClass() {
		return disableMultiClass;
	}

	public Set<String> getLoadPredModelVal() {
		return loadPredModelVal;
	}

	public boolean isLearnRegression() {
		return learnRegression;
	}

	public void setLearnRegression(boolean learnRegression) {
		this.learnRegression = learnRegression;
	}

	public int getMaxTreesVal() {
		return maxTreesVal;
	}

	public double getDefaultStepLenVal() {
		return stepLenVal;
	}

	public int getRdnIterationStep() {
		return rdnIterationStep;
	}

	public double getSamplePosProbVal() {
		return samplePosProbVal;
	}

	public double getSampleNegsToPosRatioVal() {
		return sampleNegsToPosRatioVal;
	}

	public String getAucPathVal() {
		return aucPathVal;
	}

	public double getTestNegsToPosRatioVal() {
		return testNegsToPosRatioVal;
	}

	public String getExtraMarkerForFiles(boolean includeTestSkew) {
		// TODO(@hayesall): Factor out the need for the file system.
		String result = "_";
		result += "pos_";
		result += "neg_";
		if (maxLiteralsInAnInteriorNodeVal >= 0)    { result += "Lits"  + maxLiteralsInAnInteriorNodeVal; }
		if (maxTreesVal                    >= 0)    { result += "Trees" + maxTreesVal; }
		if (sampleNegsToPosRatioVal        >= 0)    { result += "Skew"     + (int) sampleNegsToPosRatioVal; }
		if (includeTestSkew &&
				testNegsToPosRatioVal      >= 0)    { result += "TestSkew" + (int) testNegsToPosRatioVal; }
		return result;
	}

	public int getMaxLiteralsInAnInteriorNode() {
		return maxLiteralsInAnInteriorNodeVal;
	}

	public boolean isJointModelDisabled() {
		return jointModelDisabled;
	}

	public boolean isLearnMLN() {
		return learnMLN;
	}

	public boolean isSoftM() {
		return SoftM;
	}

	public void setLearnMLN(boolean learnMLN) {
		this.learnMLN = learnMLN;
	}

	public double getAlpha() {
		return alpha;
	}

	public double getBeta() {
		return beta;
	}

	public void setBeta(double beta) {
		this.beta = beta;
	}

	public boolean isLearnProbExamples() {
		return learnProbExamples;
	}

}
