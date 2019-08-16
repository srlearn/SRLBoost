package edu.wisc.cs.will.Boosting.Utils;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Utils.Utils;

// TODO(@hayesall): Replace this with an actual commandline parser.

public class CommandLineArguments {

	public CommandLineArguments() {
		super();
	}

	/**
	 * Steps to add new arguments
	 * 1. Define a "static final" string for the flag
	 * 2. Define a variable that is set by the flag
	 * 3. Create a getter and setter for the variable.
	 * 4. Set the value of the variable from the flags in parseArgs
	 * 5. Define a usage string in getUsageString
	 */

	private static final String argPrefix = "-";
	public static final String learn = "l";

	// Divide inference examples into this many bins.  THIS IS NEEDED WHEN THE SIZE OF A TESTSET IS TOO LARGE.
	public static int modN = 10;

	// '-1' means do ALL.
	private int doInferenceIfModNequalsThis = -1;
	private static final String indicatorOfModN = "useMod";
	private static final String indicatorOfDoEveryNth = "doWhenMod";

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
	
	private static final String useOCC = "occ";
	private boolean learnOCC=false;
	
	private static final String sampleOCCFlag = "dropPos";
	private double dropPos=0.0;
	
	private static final String learnMLNClauses = "mlnClause";
	private boolean learningMLNClauses=false;
	
	private static final String numMLNClauses = "numMLNClause";
	private int numberOfMLNClauses=5;
	
	private static final String maxMLNLength = "mlnClauseLen";
	private int maxMLNClauseLength=2;
	
	private static final String noTargetModes = "removeTarget";
	private boolean noTargetModesInitially = false;

	private static final String hiddenLitFlag = "hidden";
	private String hiddenStrategy = "ignore";

	private static final String hideSampleFlag = "hideProb";
	private double hiddenLitProb = -1;

	private static final String hideNegSampleFlag = "hideNegProb";
	private double hiddenNegLitProb = -1;

	private static final String outputAlchFlag = "outputFacts";
	private String outputAlchDBFile = null;

	private static final String createHiddenFlag = "createHidden";
	private boolean createHiddenFile = false;
	
	private static final String reportMissFlag = "reportHiddenEx";
	private boolean reportHiddenEx = true;

	private static final String rdnIterFlag = "iter";
	private int rdnIterationStep = -1;

	private static final String emSampleFlag = "numState";
	private int numberOfHiddenStates = -1;

	private static final String ignoreStateProbFlag = "noStateProb";
	private boolean ignoreStateProb = false;

	private static final String emSampleProbFlag = "emSampleProb";
	private double emSampleProb = 1;

	private static final String learnCurve = "lc";
	private boolean printLearningCurve = false;

	private static final String outName = "outSuffix";
	public String outFileSuffix = null;

	public static final String infer = "i";
	private boolean inferVal=false;

	private static final String useYap = "y";
	private boolean useYapVal=false;

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
	
	private static final String adviceFile = "advice";
	private String adviceFileVal = null;

	private static final String yapBin = "yapBin";
	private String yapBinVal = "/u/t/u/tushar/code/yap/bin/yap";

	private static final String yapBias = "yapBias";
	private String yapBiasVal = "";

	public static final String targetPred = "target";
	private Set<String> targetPredVal = null;

	private static final String hiddenPredFlag = "hiddenPred";
	private Set<String> hiddenPredVal = null;

	private static final String loadModelPredFlag = "loadPredModel";
	private Set<String> loadPredModelVal = null;

	private static final String saveModel = "save";
	private boolean saveModelVal=false;

	private static final String maxTrees = "trees";
	private int maxTreesVal=10;

	private static final String noLazybase = "noLazy";
	private boolean usingDefaultClausebase = false;

	private static final String autoCreateNeg = "createNeg";
	private boolean createSyntheticEgs = false;

	private static final String printLeafIds = "printLeafId";
	private boolean printingTreeStats = false;

	private static final String disableJointModel = "noJointModel";
	private boolean jointModelDisabled =false;

	private static final String disableChkPtFlag = "disableChkPts";
	private boolean noCheckPointing=false;

	private static final String disableAdviceFlag = "disableAdvice";
	private boolean disableAdvice = false;

	private static final String regressionFlag = "reg";
	private boolean learnRegression = false;

	private static final String probFlag = "probEx";
	private boolean learnProbExamples = false;

	private static final String disableMultiClassFlag = "noMulti";
	private boolean disableMultiClass = false;

	private static final String priorAdviceFlag = "priorAdvice";
	private String priorAdvice="advice.txt";

	private static final String maxInteriorNodeLits = "maxNodeLits";
	private int maxLiteralsInAnInteriorNodeVal = 1;

	private static final String bagOriginalExamplesKey   = "bag";
	private static final String noBagOriginalExamplesKey = "noBag";
	private boolean bagOriginalExamples = false;

	private static final String stepLen = "step";
	private double stepLenVal =1;

	private static final String sampleNegsToPosRatio = "negPosRatio";
	private double sampleNegsToPosRatioVal = 2;

	private static final String printAllEgFlag		= "printAllEgToo";
	private boolean printAllExamplesToo = false;

	private static final String testNegsToPosRatio = "testNegPosRatio";
	private double testNegsToPosRatioVal = -1;
	private static final String testPosString      = "testPosString"; // Allow overriding of the default.
	private String stringForTestsetPos = "pos";
	private static final String testNegString      = "testNegString"; // Allow overriding of the default.
	private String stringForTestsetNeg  = "neg";
	private static final String testFactsString    = "testFactsString"; // Allow overriding of the default.
	private String stringForTestsetFacts = "facts";
	private static final String testHiddenString    = "testHiddenString"; // Allow overriding of the default.
	private String stringForTestsetHidden = "hidden";

	// TODO(@hayesall): Investigate and remove.
	private static final String treelearner = "yapTree";
	private String treelearnerVal = "/u/t/u/tushar/code/tildecrf_20091116/treelearner/treelearner.pl" ;

	private static final String aucPath = "aucJarPath";
	private String aucPathVal = null;

	private static final String modelName = "modelSuffix";
	private String modelFileVal = null;


	private static final String samplePosProb = "samplePositive";
	private double samplePosProbVal = -1.0;

	private static final String reweighEx = "reweigh";
	public boolean reweighExamples = false;

	private static final String useProbWts = "probWt";
	private boolean useProbabilityWeights = false;
	
	public int getDoInferenceIfModNequalsThis() {
		return doInferenceIfModNequalsThis;
	}

	private String getAnyStringForModEquals() {
		if (doInferenceIfModNequalsThis < 0) { return ""; }
		return "whenModEquals" + doInferenceIfModNequalsThis + "_";
	}

	// TODO(@hayesall): Abandon all hope ye who enter here.
	public boolean parseArgs(String[] args) {

		for (int i = 0; i < args.length; i++) {

			if (args[i].trim().isEmpty())
				continue;

			Utils.println("args[" + i + "] = " + args[i]);

			if (argMatches(args[i], "noLockFiles")) {
				useLockFiles = false;
				continue;
			}

			if (argMatches(args[i], indicatorOfModN)) {
				modN = Integer.parseInt(args[++i]);
				continue;
			}			
			if (argMatches(args[i], indicatorOfDoEveryNth)) {
				doInferenceIfModNequalsThis = Integer.parseInt(args[++i]);
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
			
			if (argMatches(args[i], useOCC)) {
				learnOCC = true;
				continue;
			}

			if (argMatches(args[i], sampleOCCFlag)) {
				dropPos = Double.parseDouble(args[++i]);
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
			if (argMatches(args[i], printAllEgFlag)) {
				printAllExamplesToo = true;
				if (isArgumentNotAFlag(args, i+1)) {
					printAllExamplesToo = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], noTargetModes)) {
				noTargetModesInitially = true;
				if (isArgumentNotAFlag(args, i+1)) {
					noTargetModesInitially = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], hiddenLitFlag)) {
				hiddenStrategy = args[++i];
				continue;
			}
			if (argMatches(args[i], hideSampleFlag)) {
				hiddenLitProb = Double.parseDouble(args[++i]);
				continue;
			}
			if (argMatches(args[i], hideNegSampleFlag)) {
				hiddenNegLitProb = Double.parseDouble(args[++i]);
				continue;
			}
			if (argMatches(args[i], outputAlchFlag)) {
				outputAlchDBFile = args[++i];
				continue;
			}
			if (argMatches(args[i], createHiddenFlag)) {
				createHiddenFile = true;
				if (isArgumentNotAFlag(args, i+1)) {
					createHiddenFile = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			
			if (argMatches(args[i], reportMissFlag)) {
				reportHiddenEx = true;
				if (isArgumentNotAFlag(args, i+1)) {
					reportHiddenEx = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], rdnIterFlag)) {
				rdnIterationStep = Integer.parseInt(args[++i]);
				continue;
			}
			
			if (argMatches(args[i], emSampleFlag)) {
				numberOfHiddenStates = Integer.parseInt(args[++i]);
				continue;
			}
			
			if (argMatches(args[i], ignoreStateProbFlag)) {
				ignoreStateProb = true;
				if (isArgumentNotAFlag(args, i+1)) {
					ignoreStateProb = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			
			if (argMatches(args[i], emSampleProbFlag)) {
				emSampleProb = Double.parseDouble(args[++i]);
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
			if (argMatches(args[i], useProbWts)) {
				useProbabilityWeights = true;
				if (isArgumentNotAFlag(args, i+1)) {
					useProbabilityWeights = Utils.parseBoolean(args[++i]);
				}
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
			if (argMatches(args[i], useYap)) {
				useYapVal = true;
				if (isArgumentNotAFlag(args, i+1)) {
					useYapVal = Utils.parseBoolean(args[++i]);
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
			if (argMatches(args[i], noLazybase)) {
				usingDefaultClausebase = true;
				if (isArgumentNotAFlag(args, i+1)) {
					usingDefaultClausebase = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], autoCreateNeg)) {
				createSyntheticEgs = true;
				if (isArgumentNotAFlag(args, i+1)) {
					createSyntheticEgs = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], printLeafIds)) {
				printingTreeStats = true;
				if (isArgumentNotAFlag(args, i+1)) {
					printingTreeStats = Utils.parseBoolean(args[++i]);
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
			if (argMatches(args[i], adviceFile )) {
				setAdviceFileVal(args[++i]);
				continue; 
			}
			if (argMatches(args[i], yapBin)) {
				yapBinVal = args[++i];
				continue;
			}
			if (argMatches(args[i], yapBias)) {
				yapBiasVal = args[++i];
				continue;
			}
			if (argMatches(args[i], targetPred)) {
				String targetStr = args[++i];
				targetPredVal = new HashSet<String>();
				targetPredVal.addAll(Arrays.asList(targetStr.split(",")));
				continue;
			}
			if (argMatches(args[i], hiddenPredFlag)) {
				String targetStr = args[++i];
				hiddenPredVal = new HashSet<String>();
				hiddenPredVal.addAll(Arrays.asList(targetStr.split(",")));
				continue;
			}
			if (argMatches(args[i], loadModelPredFlag)) {
				String targetStr = args[++i];
				loadPredModelVal = new HashSet<String>();
				loadPredModelVal.addAll(Arrays.asList(targetStr.split(",")));
				continue;
			}
			if (argMatches(args[i], saveModel)) {
				saveModelVal=true;
				if (isArgumentNotAFlag(args, i+1)) {
					saveModelVal = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], disableAdviceFlag)) {
				disableAdvice=true;
				if (isArgumentNotAFlag(args, i+1)) {
					disableAdvice = Utils.parseBoolean(args[++i]);
				}
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
			if (argMatches(args[i], priorAdviceFlag)) {
				priorAdvice = args[++i];
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
			if (argMatches(args[i], treelearner)) {	
				treelearnerVal = args[++i];
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
			if (argMatches(args[i], testPosString)) {
				stringForTestsetPos = args[++i];
				continue;
			}
			if (argMatches(args[i], testNegString)) {
				stringForTestsetNeg = args[++i];
				continue;
			}
			if (argMatches(args[i], testFactsString)) {
				stringForTestsetFacts = args[++i];
				continue;
			}
			if (argMatches(args[i], testHiddenString)) {
				stringForTestsetHidden = args[++i];
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

	/**
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
		// TODO(@hayesall): This should be the result of a -h/--help flag.

		String result = "Usage:\n";
		
		result += argPrefix + learn + " : Use this flag, if you want to enable learning.\n";
		
		result += argPrefix + infer + " : Use this flag, if you want to enable inference.\n";
		
		result += argPrefix + useYap + " : Use this flag, if you want to use Yap for tree learning.\n";
		
		result += argPrefix + noBoosting + " : Use this flag, if you dont want to use boosting.\n";
		
		result += argPrefix + trainDir + " <Training directory> : Path to the training directory in WILL format.\n";
		
		result += argPrefix + testDir + " <Testing directory> : Path to the testing directory in WILL format.\n";
		
		result += argPrefix + modelDir + " <Model directory> : Path to the directory with the stored models[or where they will be stored].\n";
		
		result += argPrefix + yapBin + " <Yap binary> : Path to the Yap binary.\n";
		
		result += argPrefix + yapBias + " <Yap bias file> : Path to the Yap Bias file.\n";
		
		result += argPrefix + treelearner + " <TILDE treelearner file> : Path to the treelearner file.\n";
		
		result += argPrefix + targetPred + " <target predicates> : Comma separated list of predicates that need to be learned/inferred.\n";
		
		result += argPrefix + saveModel + " : Use this flag, if you want to save the learnt models.\n";
		
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

	public boolean isUseYapVal() {
		return useYapVal;
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

	public boolean isPrintAllExamplesToo() {
		return printAllExamplesToo;
	}

	public int getMaxMLNClauseLength() {
		return maxMLNClauseLength;
	}

	public String getHiddenStrategy() {
		return hiddenStrategy;
	}

	public boolean isReportHiddenEx() {
		return reportHiddenEx;
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

	public boolean isUseProbabilityWeights() {
		return useProbabilityWeights;
	}

	public void setUseProbabilityWeights(boolean useProbabilityWeights) {
		this.useProbabilityWeights = useProbabilityWeights;
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
	
	private void setAdviceFileVal(String fileName) {
		adviceFileVal = Utils.replaceWildCards(fileName);
		if (!Utils.fileExists(fileName)) {
			Utils.waitHere("This specified advice file does not exist: \n  " + adviceFileVal);
		}
	}
	
	public boolean isNoTargetModesInitially() {
		return noTargetModesInitially;
	}

	public String getAdviceFileVal() {
		return adviceFileVal;
	}

	public String getYapBinVal() {
		return yapBinVal;
	}

	public String getYapBiasVal() {
		return yapBiasVal;
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

	public Set<String> getHiddenPredVal() {
		return hiddenPredVal;
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

	public String getTreelearnerVal() {
		return treelearnerVal;
	}

	public double getSamplePosProbVal() {
		return samplePosProbVal;
	}

	public double getSampleNegsToPosRatioVal() {
		return sampleNegsToPosRatioVal;
	}

	public boolean isLearnOCC() {
		return learnOCC;
	}

	public double getDropPos() {
		return dropPos;
	}

	public double getHiddenLitProb() {
		return hiddenLitProb;
	}

	public double getHiddenNegLitProb() {
		return hiddenNegLitProb;
	}

	public String getOutputAlchDBFile() {
		return outputAlchDBFile;
	}

	public String getAucPathVal() {
		return aucPathVal;
	}

	public double getTestNegsToPosRatioVal() {
		return testNegsToPosRatioVal;
	}

	public String getStringForTestsetPos() {
		return stringForTestsetPos;
	}

	public String getExtraMarkerForFiles(boolean includeTestSkew) {
		String result = "_";
		if (stringForTestsetPos != null)            { result += stringForTestsetPos + "_"; }
		if (stringForTestsetNeg != null)            { result += stringForTestsetNeg + "_"; }
		 result += getAnyStringForModEquals();
		if (maxLiteralsInAnInteriorNodeVal >= 0)    { result += "Lits"  + maxLiteralsInAnInteriorNodeVal; }
		if (maxTreesVal                    >= 0)    { result += "Trees" + maxTreesVal; }
		if (sampleNegsToPosRatioVal        >= 0)    { result += "Skew"     + (int) sampleNegsToPosRatioVal; }
		if (includeTestSkew &&
				testNegsToPosRatioVal      >= 0)    { result += "TestSkew" + (int) testNegsToPosRatioVal; }
		return result;
	}

	public String getStringForTestsetHidden() {
		return stringForTestsetHidden;
	}

	public int getNumberOfHiddenStates() {
		return numberOfHiddenStates;
	}

	public double getEmSampleProb() {
		return emSampleProb;
	}

	public boolean isIgnoreStateProb() {
		return ignoreStateProb;
	}

	public int getMaxLiteralsInAnInteriorNode() {
		return maxLiteralsInAnInteriorNodeVal;
	}

	public String getStringForTestsetNeg() {
		return stringForTestsetNeg;
	}
	
	public String getStringForTestsetFacts() {
		return stringForTestsetFacts;
	}

	public boolean isJointModelDisabled() {
		return jointModelDisabled;
	}

	public String getDirForAUCfiles(String target, WILLSetup setup) {
		// If models are being written somewhere, then also write AUCs there
		// (this allows us to avoid writing in a dir that only contains INPUT files)
		// Hence, multiple runs can simultaneously use the same input dir, yet write to different output dirs.
		String aucTempDirectory =  (getResultsDirVal() != null ? getResultsDirVal() : setup.getOuterLooper().getWorkingDirectory()) + "AUC/";
		if (getTargetPredVal().size() > 1) { 
			aucTempDirectory += target;
		}			
		if (getModelFileVal() != null) {
			aucTempDirectory += getModelFileVal();
		}
		Utils.ensureDirExists(aucTempDirectory);
		return aucTempDirectory;
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

	public boolean isDisableAdvice() {
		return disableAdvice;
	}

	public String getPriorAdvice() {
		return priorAdvice;
	}

	public boolean isUsingDefaultClausebase() {
		return usingDefaultClausebase;
	}

	public boolean isPrintingTreeStats() {
		return printingTreeStats;
	}

	public boolean isCreateSyntheticEgs() {
		return createSyntheticEgs;
	}

	public boolean isCreateHiddenFile() {
		return createHiddenFile;
	}

}
