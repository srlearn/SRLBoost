package edu.wisc.cs.will.ILP;

import java.io.BufferedReader;
import java.io.File;import java.io.FileNotFoundException;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;
import java.io.IOException;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.AllOfFOPC;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.ILP.TuneParametersForILP.ReasonToStopEarly;
import edu.wisc.cs.will.ResThmProver.DefaultHornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 *
 * @author shavlik
 * 
 * 
    'Full'                          has 2 positive examples and 1 negative examples with advice.
    'ReadyToFly'                    has 2 positive examples and 7 negative examples with advice.
    'TruckIsAtIntersection'         has 4 positive examples and 3 negative examples with advice.
    'AssessGoal'                    has 1 positive examples and 6 negative examples with advice.
    'CallsForColumnFormation'       has 3 positive examples and 3 negative examples with advice.
    'CallsForEchelonLFormation'     has 1 positive examples and 2 negative examples with advice.
    'CallsForLineFormation'         has 2 positive examples and 2 negative examples with advice.
    'CallsForVeeFormation'          has 2 positive examples and 2 negative examples with advice.
    'CallsForWedgeFormation'        has 2 positive examples and 3 negative examples with advice.
    'CompanyHasMinePlow'            has 2 positive examples and 1 negative examples with advice.
    'IsASingleMovingTruckScenario'  has 2 positive examples and 4 negative examples with advice.
    'IsASingleStoppedTruckScenario' has 2 positive examples and 5 negative examples with advice.
    'Near'                          has 5 positive examples and 0 negative examples with advice.    
 *
 */

public class Experimenter { // TODO - maybe this should be ExperimentWithSimulatedData?
	private  ILPouterLoop      outerLooper;
	private  LearnOneClause    learnOneClause;
	private  HornClauseContext context;
	public   Boolean           relevanceEnabled = null;
	
	
	public Boolean DOING_TEMP_HACK = false;

	protected static String  experimentName     = "people/Jude/Testbeds/BLex10/"; //"projects/BootstrapLearning/BL_rawData2/"; // "Jude/Testbeds/BLex10/"; // "Jude/Testbeds/BL/"; // "JudeEx2/Testbeds/BL";
	private  boolean markWithNumberOfExpansions = true;      // false;  // true;
	
	// Use static's here so we can change them in the main() we're using.
	public static boolean createAdviceNoiseFiles = false;     // These need to be done EARLY so we properly mark examples with advice (i.e., redundant advice needs to be removed).
	public static boolean createDataFilesOnly    = false;     // For category noise.  Also creates test sets.
	public static boolean checkWhatIsMissing     = false;   

    private  static double[] droppingProbs   = {0.00, 0.05, 0.10, 0.15, 0.25, 0.37, 0.50, 0.62, 0.75, 0.87, 1.00};
    private  static double[] classLabelProbs = {0.00, 0.03, 0.05, 0.07, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.45};
    private  static double[] fractExamples   = {0.02, 0.04, 0.06, 0.08, 0.10, 0.14, 0.20, 0.24, 0.30, 0.50, 0.74, 1.00}; // These should be 'even' numbers since we want the same number of pos and neg examples in each run.
 // public  final static double[] droppingProbs = {0.00, 0.05, 0.10, 0.15, 0.25, 0.37, 0.50, 0.62, 0.75, 0.87};   // From AdviceProcessor (1.00 not needed there).
    
    // If mainWorkingDir is changed, be sure to include a final '/' at the end of it.
    // AT ONE TIME THE PLAN WAS TO ALLOW THIS TO ONLY IMPACT THE TESTSET FILES, BUT NOW IT IS THE CWD.  TODO cleanup
    protected String  nameForShavlikGroup       = "/u/shavlikgroup/migrated/";
    protected String  mainWorkingDir            = nameForShavlikGroup + experimentName;
    private boolean   runningInWindows          = mainWorkingDir.substring(1).startsWith(":\\"); // A sufficient hack for Windows?
    
    // These are likely to be reset by the command-line arguments.
    public String     directory                 = "./";
    public String     prefix                    = "Full";
    
    private boolean           checkpointEnabled     = false;
    private long              maxTimeInMilliseconds = 3 * 24 * 60 * 60 * 1000L; // As a default, allow a max of three days (e.g., overnight plus the weekend).  This is in milliseconds, but remember that the max time, command-line argument is in seconds!
    private ReasonToStopEarly the_reasonToStopEarly = ReasonToStopEarly.useBestAccuracyToStopEarly;

    protected boolean useAdvice       = true;
    private Set<String> lessonsToSkip = new HashSet<String>(32); 
    private   int     runNumberInUse  =  0;
    protected int     runNumberFirst  =  1; 
    protected int     runNumberLast   = 10;  
    
    public    double  probOfDroppingLiteral           = 0.00;
    protected double  probOfFlippingClassLabel        = 0.00;
    protected double  fractionOfTrainingExamplesToUse = 1.00;
    
    private int     numberOfFolds     =   1; // <------------------
    private int     maxNodesExpanded  = 100; // This is the number of ILP rule bodies that are EXPANDED by adding literals.
    private double  thresholdForUsingTuningSets       = 0.275; // E.g., if our train set has 100 examples, once 27.5 are in use (e.g., in a learning curve), we use a tuning set.
    private double  fractionOfExamplesUsedForTuning   = 0.33;  // NOTE: set the previous value to a negative number to turn off useSingleTrainTuneSplit.
    private int     numberOfRunsToUse = Math.min(10, AdviceProcessor.numberOfRuns);	// Have prep'ed 30?
  
    private boolean useOnion       = true;
    private boolean useRRR         = false;
    private boolean flipFlopPosNeg = false;
    private String  fileExtension            = Utils.defaultFileExtension;
    private String  fileExtensionWithPeriod  = Utils.defaultFileExtensionWithPeriod;

    public OnionFilter onionFilter = null;

    private boolean overWriteOldResults = false; // Please don't change me.  If you need to change this, override it in a subclass via the setupUserOverrides() method.
    
	public  String[] lessonsToUse = {
		/* */
	    "Full", 
		"ReadyToFly",
		"TruckIsAtIntersection",
		"AssessGoal",
		"CallsForColumnFormation",
		"CallsForEchelonLFormation", 
		"CallsForEchelonRFormation",
		"CallsForLineFormation", 
		"CallsForVeeFormation",		
		"CallsForWedgeFormation",
		"CompanyHasMinePlow",
		"IsASingleMovingTruckScenario", 
		"IsASingleStoppedTruckScenario",
		"Near",
		""}; // Stick this at the end so easy/safe to comment out other lines.		

    private Set<Example> posExamplesWithAdvice = null;
    private Set<Example> negExamplesWithAdvice = null;
    
    public Theory        bestTheory;
    public CoverageScore bestTheoryTrainingScore;
    public PredicateName targetPredicateName;

	public Experimenter() { }

    public void setup(String[] args) throws SearchInterrupted {
    	setup(args, false, false);
    }
    public boolean setup(String[] args, boolean onlyScanArgs, boolean skipIfTheoryFileExists) throws SearchInterrupted {
		args = Utils.chopCommentFromArgs(args);

        Utils.Verbosity defaultVerbosity = Utils.isDevelopmentRun() ? Utils.Verbosity.Developer : Utils.Verbosity.Medium;

        processFlagArguments(args);

        if (onlyScanArgs) { return false; }
        
		Utils.seedRandom(12345);

        if ( Utils.isVerbositySet() == false ){
            Utils.setVerbosity(defaultVerbosity);
        }
        
        // See if we need to make this run.  DO THIS BEFORE LOADING ALL THE FILES, SINCE THAT TAKES AWHILE.
        // TODO - check for the RESULTS file?
        if (skipIfTheoryFileExists) {
        	File theoryFile = Utils.ensureDirExists(     directory + "/theories/"       + prefix + "_theory"        + getFilePostfix() + "." + fileExtension);
        	
            if (theoryFile.exists()) { 
            	Utils.println("\n% Since this theory file exists, this run will be skipped (delete or rename the file if you wish to recompute it):\n%  " + theoryFile);
          
                File resultsFile = Utils.ensureDirExists(directory + "/testSetResults/" + prefix + "_testsetResult" + getFilePostfix() + "." + fileExtension);
                if (!resultsFile.exists()) {
                	waitHereUnlessCondorJob("BUT THE CORRESPONDING RESULTS FILE IS MISSING! " + resultsFile);
                	return false;
                }
				Utils.println("\n% Theory and results files already exist.");
				return false;
            }
            File resultsFile = Utils.ensureDirExists(   directory + "/testSetResults/" + prefix + "_testsetResult" + getFilePostfix() + "." + fileExtension);
            if (resultsFile.exists()) { 
            	Utils.println("\n% Although no theory file exists, this run will be skipped because a results file exists (delete or rename the file if you wish to recompute it):\n%  " + resultsFile);  
            	return false;
            }            
            if (onlyCheckingForMissingFiles) {
            	Utils.waitHere("\n% Neither theory nor results file exists.\n   " + theoryFile + "\n   " + resultsFile);
            	return false; 
            }
			Utils.println("\n% Neither theory nor results file exists.\n   " + theoryFile + "\n   " + resultsFile);
        }

        if (!DOING_TEMP_HACK && !overWriteOldResults && !skipIfTheoryFileExists) Utils.waitHere("\n% skipIfTheoryFileExists = " + skipIfTheoryFileExists); // SHOULD THIS HAPPEN FOR THE MLj EXPERIMENTS?
        

		String[] newArgList = new String[4];
		newArgList[0] = getPosTrainExamplesFileName(creatingInitialBIGdata || createAdviceNoiseFiles || createDataFilesOnly);
		newArgList[1] = getNegTrainExamplesFileName(creatingInitialBIGdata || createAdviceNoiseFiles || createDataFilesOnly);
		newArgList[2] = getBKfileName(); // Here we want the original (BK and facts).
		newArgList[3] = getFactsFileName();

        for (int i = 0; i <= 3; i++) { Utils.println("% setup:  newArgList[i] = " + newArgList[i]);}
		if (flipFlopPosNeg) {
			String   temp = newArgList[0];
			newArgList[0] = newArgList[1];
			newArgList[1] = temp;
		}

		Utils.createDribbleFile(directory + "/" + prefix + "_dribble." + fileExtension);
	//	Utils.waitHere(directory + "/" + prefix + "_dribble." + fileExtension);
        
		try {
            HandleFOPCstrings stringHandler = new HandleFOPCstrings(true); // OK for this to be a NEW string handler (since we might be running multiple experiments in sequence).
            stringHandler.setStringsAreCaseSensitive(true); // TODO - don't want this for non-BL tasks.   
            // We want everything new each run.
            context        = new DefaultHornClauseContext(stringHandler);
			outerLooper    = new ILPouterLoop(directory, null, newArgList, new Gleaner(), context);  // Use null for prefix since already in directory.   
			learnOneClause = outerLooper.innerLoopTask;
			if (Utils.getSizeSafely(learnOneClause.targets) < 1) { // TODO - clean this up!
				targetPredicateName = learnOneClause.getPosExamples().get(0).predicateName; // WILL CRASH IF NO POS EXAMPLES.
			} else {
				targetPredicateName = learnOneClause.targets.get(0).predicateName;
			}
        } catch (IOException e) {
        	Utils.reportStackTrace(e);
			Utils.error("Error: " + e);
		}
        setupParameters();

		if (getLearnOneClause().createdSomeNegExamples) {
			Example.writeObjectsToFile(newArgList[1],getLearnOneClause().getNegExamples(), ".", "// Negative examples, including created ones.");
		}

        if (useAdvice || createAdviceNoiseFiles) setupRelevance(runNumberInUse, probOfDroppingLiteral); // Will do an advice-free run if this is NOT called.  If the first argument is < 1, will use ALL the relevance.
        return true;
    }

    
    private void reportDoc(String docStringForCallToOnion, double trainsetAccuracy, double tuneSetAccuracy, double testSetAccuracy) {
        File docFile = Utils.ensureDirExists(directory + "/OnionDoc/" + prefix + "_OnionDoc" + getFilePostfix() + "." + fileExtension); // Use commas to separate files so can concatenate these into a *.csv file so they can be sorted in Excel.
        Utils.println("% Create this Onion documentation file: " + docFile);
    	try {
        	new CondorFileWriter(docFile, false).append("Onion" + getFilePostfix() + (TuneParametersForILP.allOnionDocOnOneLine ? "," : "\n")
        										   + docStringForCallToOnion + (TuneParametersForILP.allOnionDocOnOneLine ? "," : "\n")
        										   + "    Train/Tune/Test accuracies: "
        										   + Utils.truncate(trainsetAccuracy, 4) + "/"
        										   + Utils.truncate(tuneSetAccuracy,  4) + "/"
        										   + Utils.truncate(testSetAccuracy,  4) + "\n").close();
        } catch (IOException e) {
        	Utils.waitHere("% Could not save the current Onion call's documentation string to file:\n%  " + docFile + "\n%  " + e);
        }    	
    }
    
    private void noTheoryWasLearned() {
		Utils.println("\n% The ONION was unable to find an acceptable theory.");
		// Save the theory file.
        File theoryFile = Utils.ensureDirExists(directory + "/theories/"       + prefix + "_theory"        + getFilePostfix() + "." + fileExtension);
        Utils.println("% Create this 'nothing learned' theory: " + theoryFile);
        try {
        	String theoryAsString = "NOTHING LEARNED!";
        	new CondorFileWriter(theoryFile, false).append(theoryAsString).close();
        } catch (IOException e) {
        	Utils.waitHere("% Could not save the learned theory to file:\n%  " + theoryFile + "\n%  " + e);
        }    	
        // Save the result of guessing the majority category. TODO - make this be the case 
        saveDefaultResultsToFile();
    }
    
    private void saveDefaultResultsToFile() {
    	saveResultsToFile(0.5, fractionOfTrainingExamplesToUse < thresholdForUsingTuningSets ? -1.0 : 0.5, 0.5);
    }
    
    private void saveResultsToFile(double trainSetScore, double tuneSetScore, double testSetScore) {
        String testSetFileName = directory + "/testSetResults/" + prefix + "_testsetResult" + getFilePostfix() + "." + fileExtension;
  //	waitHereUnlessCondorJob("testSetFileName = " + testSetFileName);
        File   testSetFile     = Utils.ensureDirExists(testSetFileName);
        try {
        	String resultStr = prefix + ", " + fractionOfTrainingExamplesToUse + ", " + probOfDroppingLiteral + ", " + probOfFlippingClassLabel + ", " + (useAdvice ? "advice" : "noAdvice") + ", " + runNumberInUse;
        	boolean majorityClassIsPos = false; // TO DO FIX THIS.
        	// Put this in for debugging/confirmation purposes.		
        	
	        resultStr += getExperimentSecondarySignature();
        	new CondorFileWriter(testSetFile, false).append(resultStr + ", " + trainSetScore + ", " + tuneSetScore + ", " + testSetScore + "\n").close();
        } catch (IOException e) {
        	Utils.waitHere("% Could not save the testset results to file:\n%  " + testSetFile + "\n%  " + e);
        }
    }
    
    private String getExperimentSecondarySignature() { // This DOES NOT INCLUDE fractionOfTrainingExamplesToUse/probOfDroppingLiteral/probOfFlippingClassLabel/useAdvice
    	return                                                ", [thresholdForUsingTuningSets("    + 
	     Utils.truncate(thresholdForUsingTuningSets,     2) + ")/fractionOfExamplesUsedForTuning(" + // Don't put any extra commas in here!
		 Utils.truncate(fractionOfExamplesUsedForTuning, 2) + ")/maxNodesExpanded("                + 
		 maxNodesExpanded                                   + ")]";
    }


    public boolean isTheoryNothingLearned(File theoryFile) {
    	BufferedReader r = null;
    	try {
    		r = new BufferedReader(new CondorFileReader(theoryFile));    	
    		String line;        
    		line = parseUntil("NOTHING LEARNED", r, null);    		
    		return line != null;
    	}
    	catch(Exception e) {    		
    	}
    	finally {
    		if ( r != null )
				try {r.close();	} catch (IOException e) {}
    	}    	
    	return false;
    }

    public int correctionsByTrevor = 0;

    public CrossValidationFoldResult extractVerifyResultsFromTheory(File theoryFile, File resultsFile) {
        CrossValidationFoldResult result = null;

        BufferedReader r  = null;
        BufferedReader r2 = null;
        try {
            r = new BufferedReader(new CondorFileReader(theoryFile));
            String line;
            
            line = parseUntil("TRAINING Coverage Score", r, null);
            if (line == null) {
                Utils.waitHere("Unable to find TRAINING score in theory " + theoryFile);
            }
            CoverageScore training = parseScore(r);

            line = parseUntil("TUNING Coverage Score", r, null);
            if (line == null) {
                Utils.waitHere("Unable to find TRAINING score in theory " + theoryFile);
            }
            CoverageScore tuning = parseScore(r);

            line = parseUntil("TESTING Coverage Score", r, null);
            if (line == null) {
                Utils.waitHere("Unable to find TRAINING score in theory " + theoryFile);
            }
            CoverageScore testing = parseScore(r);

            if (resultsFile.exists()) {
                r2 = new BufferedReader(new CondorFileReader(resultsFile));
                line = r2.readLine();
                
                boolean badResults = false;
                String newResults = null;

                if (line == null) {
                    Utils.println("Badly formed results file: " + resultsFile);
                    badResults = true;
                    newResults = "Empty results files: Run # " + runNumberInUse + " " + prefix +  " train = " + Utils.truncate(training.getAccuracy(), 4) + " tune = " + Utils.truncate(tuning.getAccuracy()) + " test = " + Utils.truncate(testing.getAccuracy());
                }
                else {
	                String[] fields = line.split(",");
	                if (fields.length != 10) {
	                    Utils.waitHere("Badly formed results file: " + resultsFile);
	                }
	
	                double resultsTraining = Double.parseDouble(fields[7]);
	                double resultsTuning   = Double.parseDouble(fields[8]);
	                double resultsTesting  = Double.parseDouble(fields[9]);
	
	                if (Math.abs(training.getAccuracy() - resultsTraining) > 1e-5) {
	                    Utils.warning("Incorrect training accuracy results in " + resultsFile + ".");
	                    badResults = true;
	                }
	
	                if (Math.abs(tuning.getAccuracy() - resultsTuning) > 1e-5) {
	                    Utils.warning("Incorrect tuning accuracy results in " + resultsFile + ".");
	                    badResults = true;
	                }
	
	                if (Math.abs(testing.getAccuracy() - resultsTesting) > 1e-5) {
	                    Utils.warning("Incorrect testing accuracy results in " + resultsFile + ".");
	                    badResults = true;
	                }
	
	                r2.close();
	                
	                if ( badResults == true ) {
	                    fields[7] = "" + training.getAccuracy();
	                    fields[8] = "" + tuning.getAccuracy();
	                    fields[9] = "" + testing.getAccuracy();
	
	                    StringBuilder stringBuilder = new StringBuilder();
	                    boolean first = true;
	                    for (String string : fields) {
	                        if ( first == false ) {
	                            stringBuilder.append(", ");
	                        }
	                        stringBuilder.append(string);
	                        first = false;
	                    }
	                    stringBuilder.append("\n");
	                    newResults = stringBuilder.toString();
	                }
                }                

                if ( badResults == true ) {
                    Utils.println("\n% Old results:  " + line);
                    Utils.println(  "% New results:  " + newResults);
                    Utils.println(  "% Results file: " + resultsFile);
                    Utils.println("% About to rewrite/correct (#" + Utils.comma(++correctionsByTrevor) + ")results file due to inconsistent theory/results file:\nResults file:" + resultsFile );

                    Utils.copyFile(resultsFile, new CondorFile(resultsFile + ".autocorrected"));
                    
                    saveResultsToFile(training.getAccuracy(), tuning.getAccuracy(), testing.getAccuracy());
                }
            }
            else {
                Utils.println("Result file missing: " + resultsFile + ".");
            }

            result = new CrossValidationFoldResult(0, null, null);
            result.setTrainingCoverageScore(  training);
            result.setEvaluationCoverageScore(testing);

        } catch (Exception e) {
            Utils.warning("Error extracting theory results from " + theoryFile + "\n  " + e);
            e.printStackTrace();
        } finally {
            if (r != null) {
                try {
                    r.close();
                } catch (IOException ex) {
                }
            }
            if (r2 != null) {
                try {
                    r2.close();
                } catch (IOException ex) {
                }
            }
        }


        return result;
    }

    private String parseUntil(String string, BufferedReader r, String errorString) throws IOException {
        String line = null;
        while ((line = r.readLine()) != null) {
        	//Utils.println(line);
            if (line.contains(string) || (errorString != null && line.contains(errorString)) ) {
                return line;
            }
        }
        return null;
    }

    private CoverageScore parseScore(BufferedReader r) throws IOException {
        String line;
        String[] fields;
        
        line = parseUntil("Model Pos", r, null);
        if (line == null) {
            Utils.warning("Unable to find \"Model Pos\" in theory.");
        }
        
        fields = line.split("\\s+");
        
        int tp = Integer.parseInt(fields[3]);
        int fp = Integer.parseInt(fields[4]);

        line = parseUntil("Neg", r, null);
        if (line == null) {
            Utils.warning("Unable to find \"Neg\" in theory.");
        }

        fields = line.split("\\s+");

        int fn = Integer.parseInt(fields[2]);
        int tn = Integer.parseInt(fields[3]);
        
        CoverageScore s = new CoverageScore(tp, fp, tn, fn);
        s.setFalsePositiveMEstimate(0.001);
        s.setFalseNegativeMEstimate(0.001);

        return s;
    }


    // For safety, test with a FRESH LearnOneClause, stringHandler, set of facts (currently reusing the same), etc.
    public CoverageScore getTestSetScore(PredicateName targetPname, Theory theory) throws IOException {
    	if (theory == null) { return null; }
        String[] newArgList = new String[4];
        newArgList[0] = getPosTestExamplesFileName();
        newArgList[1] = getNegTestExamplesFileName();
        newArgList[2] = getBKfileName();
        newArgList[3] = getFactsFileName();
        for (int i = 0; i <= 3; i++) { Utils.println("% getTestSetScore:  newArgList[i] = " + newArgList[i]);}
        if (theory.isNegated()) { theory.rewriteFlipFloppedTheory(false); } 
        LearnOneClause freshL1C      = new LearnOneClause(directory, null, newArgList[0], newArgList[1], newArgList[2], newArgList[3], null, null);
        boolean hold = AllOfFOPC.truncateStrings;
        AllOfFOPC.truncateStrings = false;
        List<Sentence> theoryClauses = freshL1C.getParser().readFOPCstream(theory.toString()); // Reparse so we know it works in a new environment.
        AllOfFOPC.truncateStrings = hold;
        Theory         theoryAnew    = new Theory(freshL1C.getStringHandler());
        context                      = freshL1C.getContext();
        for (Sentence sentence : theoryClauses) {
        	List<Clause> clauses = sentence.convertToClausalForm();
        	for (Clause clause : clauses) {
        		if  (clause.getDefiniteClauseHead().predicateName.name.equals(targetPname.name)) {
        			theoryAnew.addMainClause(clause);  // No need to add these to the context because the getWeightedCoverage code will walk through all the main clauses.
        		}
        		else {
        			theoryAnew.addSupportingClause(clause);
            		context.assertDefiniteClause(clause);
        		}
        	}
        }
        freshL1C.setMEstimatePos(0); // M-estimates are to help avoid overfitting the training set, so not needed here (though 'error bars' would be nice).
        freshL1C.setMEstimateNeg(0);
        CoverageScore results = freshL1C.getWeightedCoverage(theoryAnew);
        Utils.println("\n%getTestSetScore(" + targetPname + (theory.isNegated() ? ", flipped" : "") + ")'s performance:\n" + results.toShortString());
        return results;
    }

    // TODO - we really should only need to look in POS or NEG, but with the possibility of flip-flopping deciding which is appropriate is tricky. So simply look in both. 
    private boolean isAnAdviceExample(Example ex) {
    	if (posExamplesWithAdvice != null && posExamplesWithAdvice.contains(ex)) { return true; }
    	if (negExamplesWithAdvice != null && negExamplesWithAdvice.contains(ex)) { return true; }
    	return false;
    }

    private static int     maxPosTrainExamples = 50;
    private static int     maxNegTrainExamples = 50;

    private String getBKfileName() {
    	if (fractionOfTrainingExamplesToUse > 1.0) {
    		if (probOfDroppingLiteral > 0 || probOfFlippingClassLabel > 0) { Utils.error("Should only use more than 100% of the examples if there is no noise."); }					
			return directory + "/" + prefix + "_bk." + fileExtension;
    	}
    	return     directory + "/" + prefix + "_bk.txt";
    }
    private String getFactsFileName() {
    	if (fractionOfTrainingExamplesToUse > 1.0) {
    		if (probOfDroppingLiteral > 0 || probOfFlippingClassLabel > 0) { Utils.error("Should only use more than 100% of the examples if there is no noise."); }					
			return directory + "/" + prefix + "_facts." + fileExtension;
    	}
    	return     directory + "/" + prefix + "_facts." + fileExtension;
    }
    private String getPosTrainExamplesFileName(boolean useOrigData) {
    	if (useOrigData) { return directory + "/" + prefix + "_pos." + fileExtension; } // Need the ORIGINAL examples because the noisy ones need the advice to be processed first.
    	if (fractionOfTrainingExamplesToUse > 1.0) {
    		if (probOfDroppingLiteral > 0 || probOfFlippingClassLabel > 0) { 
    			Utils.error("Should only use more than 100% of the examples if there is no noise. probOfDroppingLiteral=" + probOfDroppingLiteral + " probOfFlippingClassLabel=" + probOfFlippingClassLabel); 
    		}
    		return directory + "/" + prefix + "_examples" + Utils.truncate(100 * fractionOfTrainingExamplesToUse, 0) + "P_pos" + fileExtensionWithPeriod;
    	}
    	return     directory + "/examplesForExperiments/" + prefix + "_train_examples" + Utils.truncate(100 * fractionOfTrainingExamplesToUse, 0) + "P_pos" + getInnerNameForExampleNoiseFile() + fileExtensionWithPeriod;
    }    
    private String getNegTrainExamplesFileName(boolean useOrigData) {
    	if (useOrigData) { return directory + "/" + prefix + "_neg." + fileExtension; } // Need the ORIGINAL examples because the noisy ones need the advice to be processed first.
    	if (fractionOfTrainingExamplesToUse > 1.0) {
    		if (probOfDroppingLiteral > 0 || probOfFlippingClassLabel > 0) { Utils.error("Should only use more than 100% of the examples if there is no noise."); }		
    		return directory + "/" + prefix + "_examples" + Utils.truncate(100 * fractionOfTrainingExamplesToUse, 0) + "P_neg" + fileExtensionWithPeriod;
    	}
    	return     directory + "/examplesForExperiments/" + prefix + "_train_examples" + Utils.truncate(100 * fractionOfTrainingExamplesToUse, 0) + "P_neg" + getInnerNameForExampleNoiseFile() + fileExtensionWithPeriod;
    }    
    // NOTE: we never add noise to TEST examples.
    private String getPosTestExamplesFileName() {
    	if (fractionOfTrainingExamplesToUse > 1.0) {
    		return directory + "/" + prefix + "_test_pos." + fileExtension;
    	}
    	return directory + "/examplesForExperiments/" + prefix + "_test_pos" + fileExtensionWithPeriod;
    }    
    private String getNegTestExamplesFileName() {
    	if (fractionOfTrainingExamplesToUse > 1.0) {
    		return directory + "/" + prefix + "_test_neg." + fileExtension;
    	}
    	 return directory + "/examplesForExperiments/" + prefix + "_test_neg" + fileExtensionWithPeriod;
    }

    private String getFilePostfix() {
		// TODO - either make this a local var only or clean up its usage.
		boolean includeRunNumber = ( (probOfDroppingLiteral    > 0.0 && probOfDroppingLiteral    <= 1.0) && // Only include here if not included by getInnerNameForExampleNoiseFile().
		 				            !(probOfFlippingClassLabel > 0.0 && probOfFlippingClassLabel <= 1.0));
		return
    	 	"_" + (markWithNumberOfExpansions 
    	 			? (maxNodesExpanded >= 1000 ? (maxNodesExpanded / 1000) + "Kexpansions_" :  maxNodesExpanded + "expansions_")
    	 			: "") + 
    	 	Utils.truncate(100 * fractionOfTrainingExamplesToUse, 0) + "Pexamples" +
    		((probOfDroppingLiteral    > 0.0 && probOfDroppingLiteral <= 1.0)
    			? "_adviceNoise" + Utils.truncate(100 * probOfDroppingLiteral, 0)     : "") +
    		getInnerNameForExampleNoiseFile() + 
			(includeRunNumber // TODO - need a SEPARATE run number for both ADVICE and EXAMPLE noise?  Not if we only vary one.
				? "_run" + runNumberInUse                                             : "") +
			(useAdvice ? ((probOfDroppingLiteral > 0.0 && probOfDroppingLiteral <= 1.0) ? "" : "_allAdvice")
			           : "_noAdvice"); 
    }
    
    private String getInnerNameForExampleNoiseFile() { // Still need to add "_pos.txt" or "_neg.txt" - i.e., leave that to the caller.    	
    	if (probOfFlippingClassLabel > 0.0 && probOfFlippingClassLabel <= 1.0) {
    		return "_exampleNoise" + Utils.truncate(100 * probOfFlippingClassLabel, 0) + "_run" + runNumberInUse;
    	}
    	return "";
    }
	
	private boolean isaCondorJob = false;
	private  void waitHereUnlessCondorJob(String msg) {
		if (isaCondorJob) { Utils.println(msg); } else { Utils.waitHere(msg); }
	}

    private void processFlagArguments(String[] args) throws IllegalArgumentException {
        int offset = 0;

        for (int arg = 0; arg < args.length; arg++) {
            if      (args[arg].equalsIgnoreCase("rrr") || args[arg].equalsIgnoreCase("-rrr")) {
                useRRR = true;
            }
            else if (args[arg].startsWith("offset")) {
                offset = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
            }
            else if (args[arg].startsWith("condorJWS=")  || args[arg].startsWith("-condorJWS=") ||
            		 args[arg].startsWith("condorJWS1=") || args[arg].startsWith("-condorJWS1=") ||
           		     args[arg].startsWith("condorJWS3=") || args[arg].startsWith("-condorJWS3=")) {
            	boolean isCondor3        = (args[arg].startsWith("condorJWS3=") || args[arg].startsWith("-condorJWS3="));
            	isaCondorJob             = true && !runningInWindows;
            	probOfDroppingLiteral    = 0.0;
            	probOfFlippingClassLabel = 0.0;
            	directory = "/u/shavlikgroup/" + experimentName + "/Testbeds/BL/"; // Condor needs absolute pathways.  IN THE ARGS FOR THE CONDOR JOBS
            	if (runningInWindows) directory  = "J:\\" + experimentName + "\\Testbeds\\BL\\";
            	
                int condorID   = offset + Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
                int onesDigit  = (condorID        % 10);
                int tensDigit  = (condorID /   10 % 10);
                int hundsDigit = (condorID /  100 % 10);
                int thousDigit = (condorID / 1000 % 10);
                
                Utils.println("% condorJWS: thousDigit=" + thousDigit + " hundsDigit=" + hundsDigit + "  tensDigit=" + tensDigit + " onesDigit=" + onesDigit);
                
                // FOR NOW: do different Condor runs to vary fractionOfTrainingExamplesToUse  We have already done probOfDroppingLiteral != 0.
                
                runNumberFirst = onesDigit + 21; // <--------
                runNumberLast  = runNumberFirst;
                
                String keeper1 = null;
                String keeper2 = null;
                
                useAdvice = (tensDigit == 2 * (tensDigit / 2));
                if (isCondor3) {
	                switch (tensDigit / 2) { // { 0.0, 0.03, 0.05, 0.07, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35 }  COULD ALSO DO 0.40 AND 0.45
                	case 0: probOfFlippingClassLabel = 0.00; break;  // Only need one run number here since no variation.  So if runNumberFirst > 1, the run will be skipped.
                	case 1: probOfFlippingClassLabel = 0.03; break;
                	case 2: probOfFlippingClassLabel = 0.05; break;
                	case 3: probOfFlippingClassLabel = 0.07; break;
                	case 4: probOfFlippingClassLabel = 0.10; break; 
	                }	                	
                } else {
	                switch (tensDigit / 2) {
                	case 0: probOfFlippingClassLabel = 0.15; break;
                	case 1: probOfFlippingClassLabel = 0.20; break;
                	case 2: probOfFlippingClassLabel = 0.25; break;
                	case 3: probOfFlippingClassLabel = 0.30; break; // also use 0.40 
                	case 4: probOfFlippingClassLabel = 0.35; break; // also use 0.45 
	                }
	            }
                // Might still need to do run #1 for no-advice, probOfFlippingClassLabel = 0.40 (or whatever is used below), especially if condorJWS not used.
                // if ((useAdvice || runNumberFirst > 1) && probOfFlippingClassLabel == 0.00) { probOfFlippingClassLabel = 0.40; } // Take advantage of the fact that with no NOISE, only need ONE run number, plus for with-advice, this case is handled in the advice-noise experiments.
                if (onesDigit > 0 && probOfFlippingClassLabel == 0.00) { probOfFlippingClassLabel = 0.40; } // Take advantage of the fact that with no NOISE, only need ONE run number, plus for with-advice, this case is handled in the advice-noise experiments.
                if (probOfFlippingClassLabel <= 0.0 && runNumberFirst > 1) { runNumberLast = 1; } // Shouldn't reach this, but leave in anyway in case above changes or is commented out.
                
                switch (hundsDigit) {
                	case 0: keeper1 = "Full";                      keeper2 = "IsASingleMovingTruckScenario";  break;
                	case 1: keeper1 = "TruckIsAtIntersection";     break;
                	case 2: keeper1 = "CallsForColumnFormation";   break;
                	case 3: keeper1 = "CallsForEchelonLFormation"; keeper2 = "ReadyToFly"; break; // keeper2 = "IsASingleMovingTruckScenario";  break;
                	case 4: keeper1 = "CallsForEchelonRFormation"; keeper2 = "Near";       break; // keeper2 = "IsASingleStoppedTruckScenario"; break;
                	case 5: keeper1 = "CallsForLineFormation";     break;
                	case 6: keeper1 = "CallsForVeeFormation";      keeper2 = "IsASingleStoppedTruckScenario"; break;
                	case 7: keeper1 = "CallsForWedgeFormation";    break;
                	case 8: keeper1 = "CompanyHasMinePlow";        break;
                	case 9: keeper1 = "AssessGoal";                break;
                }
                /* TEMP PATCH
                if (tensDigit / 2 == 1) {      keeper1 = keeper2; keeper2 = null; }
                else if (tensDigit / 2 == 0) {                    keeper2 = null;                }	
                else {  	                   keeper1 = null;    keeper2 = null;}
                */             
                /*
                if ((tensDigit == 2 || tensDigit == 3) && hundsDigit == 0){ keeper1 = "ReadyToFly";  runNumberLast  = runNumberFirst; probOfFlippingClassLabel = 0.25; } // **** SPECIAL CASES ***
                if ((tensDigit == 2 || tensDigit == 3) && hundsDigit == 1){ keeper1 = "Near";        runNumberLast  = runNumberFirst; probOfFlippingClassLabel = 0.25; }
                if ((tensDigit == 4 || tensDigit == 5) && hundsDigit == 0){ keeper1 = "ReadyToFly";  runNumberLast  = runNumberFirst; probOfFlippingClassLabel = 0.10; } // **** SPECIAL CASES ***
                if ((tensDigit == 4 || tensDigit == 5) && hundsDigit == 1){ keeper1 = "Near";        runNumberLast  = runNumberFirst; probOfFlippingClassLabel = 0.10; }
                */
                for (String str : lessonsToUse) if (!str.equalsIgnoreCase(keeper1) && !str.equalsIgnoreCase(keeper2)) {
                	lessonsToSkip.add(str);
                } 
                
                switch (thousDigit) {
                	case 0: fractionOfTrainingExamplesToUse = 1.00; break; // Note: 0.02 and 0.04 are skipped.
                	case 1: fractionOfTrainingExamplesToUse = 0.74; break;
                	case 2: fractionOfTrainingExamplesToUse = 0.50; break;
                	case 3: fractionOfTrainingExamplesToUse = 0.30; break;
                	case 4: fractionOfTrainingExamplesToUse = 0.20; break;
                	case 5: fractionOfTrainingExamplesToUse = 0.10; break;
                	case 6: fractionOfTrainingExamplesToUse = 0.06; break;
                	case 7: fractionOfTrainingExamplesToUse = 0.14; break;
                	case 8: fractionOfTrainingExamplesToUse = 0.08; break;
                	case 9: fractionOfTrainingExamplesToUse = 0.24; break;
                }
                Utils.println("% condorJWS: [" + runNumberFirst + "," + runNumberInUse + "," + runNumberLast + "] useAdvice=" + useAdvice + " probOfDroppingLiteral=" + probOfDroppingLiteral + "  probOfFlippingClassLabel=" + probOfFlippingClassLabel + " keeper1=" + keeper1 + " keeper2=" + keeper2 + " lessonsToSkip: " + lessonsToSkip);
            }
            else if (args[arg].startsWith("condorJWS2=") || args[arg].startsWith("-condorJWS2=")) {
            	isaCondorJob             = true && !runningInWindows;
            	probOfDroppingLiteral    = 0.0;
            	probOfFlippingClassLabel = 0.0;
            	
                int condorID   = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
                int onesDigit  = (condorID        % 10);
                int tensDigit  = (condorID /   10 % 10);
                int hundsDigit = (condorID /  100 % 10);
                int thousDigit = (condorID / 1000 % 10);
                Utils.println("% condorJWS2: thousDigit=" + thousDigit + " hundsDigit=" + hundsDigit + "  tensDigit=" + tensDigit + " onesDigit=" + onesDigit);
                                
                runNumberFirst = onesDigit + 21; // <--------
                runNumberLast  = runNumberFirst;
                
                useAdvice = true;
                switch (tensDigit) { //  Let condorJWS/condorJWS3 handle non-noise advice runs. if (probOfFlippingClassLabel <= 0.0 && runNumberFirst > 1) { runNumberLast = 1; } // Shouldn't reach this, but leave in anyway in case above changes or is commented out.
                
                	case 0: probOfDroppingLiteral = 0.87; break; // 0.00, 0.05, 0.10, 0.15, 0.25, 0.37, 0.50, 0.62, 0.75, 0.87, 1.00
                	case 1: probOfDroppingLiteral = 0.75; break;
                	case 2: probOfDroppingLiteral = 0.62; break;
                	case 3: probOfDroppingLiteral = 0.50; break;
                	case 4: probOfDroppingLiteral = 0.25; break;
                	case 5: probOfDroppingLiteral = 0.15; break;
                	case 6: probOfDroppingLiteral = 0.10; break;
                	case 7: probOfDroppingLiteral = 0.05; break;
                	case 8: probOfDroppingLiteral = 0.37; break; 
                	case 9: probOfDroppingLiteral = 1.00; if (onesDigit > 1) { runNumberLast = 1; } break; // Only need one run number for these since no variation.
                }
                
                String keeper1 = null;
                String keeper2 = null;
                switch (hundsDigit) {
            	case 0: keeper1 = "Full";                      keeper2 = "IsASingleMovingTruckScenario";  break;
            	case 1: keeper1 = "TruckIsAtIntersection";     break;
            	case 2: keeper1 = "CallsForColumnFormation";   break;
            	case 3: keeper1 = "CallsForEchelonLFormation"; keeper2 = "ReadyToFly"; break; // keeper2 = "IsASingleMovingTruckScenario";  break;
            	case 4: keeper1 = "CallsForEchelonRFormation"; keeper2 = "Near";       break; // keeper2 = "IsASingleStoppedTruckScenario"; break;
            	case 5: keeper1 = "CallsForLineFormation";     break;
            	case 6: keeper1 = "CallsForVeeFormation";      keeper2 = "IsASingleStoppedTruckScenario"; break;
            	case 7: keeper1 = "CallsForWedgeFormation";    break;
            	case 8: keeper1 = "CompanyHasMinePlow";        break;
            	case 9: keeper1 = "AssessGoal";                break;
                }
                
                switch (thousDigit) {
            	case 0: fractionOfTrainingExamplesToUse = 1.00; break;  // Note: 0.08 and 0.24 are skipped (run manually; ie outside of Condor).
            	case 1: fractionOfTrainingExamplesToUse = 0.74; break;
            	case 2: fractionOfTrainingExamplesToUse = 0.50; break;
            	case 3: fractionOfTrainingExamplesToUse = 0.30; break;
            	case 4: fractionOfTrainingExamplesToUse = 0.20; break;
            	case 5: fractionOfTrainingExamplesToUse = 0.10; break;
            	case 6: fractionOfTrainingExamplesToUse = 0.06; break;
            	case 7: fractionOfTrainingExamplesToUse = 0.14; break;
            	case 8: fractionOfTrainingExamplesToUse = 0.04; break;
            	case 9: fractionOfTrainingExamplesToUse = 0.02; break;
                }
                Utils.println("% condorJWS2: [" + runNumberFirst + "," + runNumberInUse + "," + runNumberLast + "] useAdvice=" + useAdvice + " probOfDroppingLiteral=" + probOfDroppingLiteral + "  probOfFlippingClassLabel=" + probOfFlippingClassLabel + " keeper1=" + keeper1 + " keeper2=" + keeper2);
            }
            else if (args[arg].equalsIgnoreCase("true") || args[arg].equalsIgnoreCase("-true")) {
                useRRR = true;
            }
            else if (args[arg].equalsIgnoreCase("false") || args[arg].equalsIgnoreCase("-false")) {
                useRRR = false;
            }
            else if (args[arg].equalsIgnoreCase("std") || args[arg].equalsIgnoreCase("-std")) {
                useRRR = false;
            }
            else if (args[arg].equalsIgnoreCase("flip") || args[arg].equalsIgnoreCase("-flip")) {
                flipFlopPosNeg = true;
            }
            else if (args[arg].startsWith("classNoise=") || args[arg].startsWith("-classNoise=")) {
            	probOfFlippingClassLabel = Double.parseDouble(args[arg].substring(args[arg].indexOf("=") + 1));
            }
            else if (args[arg].startsWith("drop=") || args[arg].startsWith("-drop=")) {
            	probOfDroppingLiteral = Double.parseDouble(args[arg].substring(args[arg].indexOf("=") + 1));
            }
            else if (args[arg].startsWith("examples=") || args[arg].startsWith("-examples=")) {
            	fractionOfTrainingExamplesToUse = Double.parseDouble(args[arg].substring(args[arg].indexOf("=") + 1));
            }
            else if (args[arg].startsWith("cwd=") || args[arg].startsWith("-cwd=") || args[arg].startsWith("dir=") || args[arg].startsWith("-dir=") || args[arg].startsWith("directory=") || args[arg].startsWith("-directory=")) {
            	mainWorkingDir = args[arg].substring(args[arg].indexOf("=") + 1);
            }
            else if (args[arg].startsWith("-prefix=")) {
                prefix = args[arg].substring(args[arg].indexOf("=") + 1);
            }
            else if (Utils.isaInteger(args[arg])) {
                numberOfFolds = Integer.parseInt(args[arg]);
            } // A bare number is interpreted as the number of folds.
            else if (args[arg].startsWith("-folds=")) {
                numberOfFolds = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
            }
//            else if (args[arg].startsWith("-fold=")) {
//                firstFold = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
//                lastFold = firstFold;
//            }
            else if (args[arg].equalsIgnoreCase("-checkpoint")) {
                checkpointEnabled = true;
            }
            else if (args[arg].equalsIgnoreCase("-relevance")) {
                relevanceEnabled = true;
            }
            else if (args[arg].equalsIgnoreCase("-norelevance")) {
                relevanceEnabled = false;
            }
            else if (args[arg].startsWith("-maxTime=") || args[arg].startsWith("-maxTimeInMsec=") || args[arg].startsWith("-maxTimeInMillisec=")) {
                maxTimeInMilliseconds = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1)) * 1000L;
            }
            else if (args[arg].startsWith("-maxTimeInSec=") || args[arg].startsWith("-maxTimeInSeconds=")) {
                maxTimeInMilliseconds = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
            }
            else if (args[arg].equalsIgnoreCase("noAdvice") || args[arg].equalsIgnoreCase("-noAdvice")) {
                useAdvice = false;
            }
            else if (args[arg].equalsIgnoreCase("noadvice") || args[arg].equalsIgnoreCase("-noadvice")) {
                useAdvice = false;
            }
            else if (args[arg].equalsIgnoreCase("advice") || args[arg].equalsIgnoreCase("-advice")) {
                useAdvice = true;
            }
            else if (args[arg].equalsIgnoreCase("useAdvice") || args[arg].equalsIgnoreCase("-useAdvice")) {
                useAdvice = true;
            }
            else if (args[arg].equalsIgnoreCase("useOnion") || args[arg].equalsIgnoreCase("-useOnion")) {
                useOnion = true;
            }
            else if (args[arg].equalsIgnoreCase("onion") || args[arg].equalsIgnoreCase("-onion")) {
                useOnion = true;
            }
            else if (args[arg].equalsIgnoreCase("noonion") || args[arg].startsWith("noOnion") || args[arg].equalsIgnoreCase("-noOnion")) {
                useOnion = false;
            }
            else if (args[arg].startsWith("-extension=") || args[arg].startsWith("extension=")) {
                fileExtension = args[arg].substring(args[arg].indexOf("=") + 1);
            }
            else {
                throw new IllegalArgumentException("Unknown argument specified: " + args[arg]);
            }
        }
    }

    private void setupParameters() {
        Gleaner gleaner = (Gleaner) getLearnOneClause().searchMonitor;
        outerLooper.writeGleanerFilesToDisk = true;
        //		if (args.length > 3) { getLearnOneClause().setMinPosCoverage(Double.parseDouble(args[3])); }
        //		if (args.length > 4) { getLearnOneClause().setMinPrecision(  Double.parseDouble(args[4]));   }
        // Set some additional parameters for the inner-loop runs.
        getLearnOneClause().setMaxNodesToConsider(maxNodesExpanded); // This should be SMALLER THAN THE NEXT BECAUSE THIS IS THE NUMBER OF *POP* FROM OPEN.  I.e., it is the number of EXPANSIONS.
        getLearnOneClause().setMaxNodesToCreate(100 * maxNodesExpanded); // This is the maximum number of nodes to ADD to OPEN.  (WHAT HAPPENS WHEN THIS IS HIT?  ILP SEARCH STOPS?  I ASSUME SO.  NO NEED TO EMPTY OPEN.)
        getLearnOneClause().maxSearchDepth     = 1000;
        getLearnOneClause().verbosity          = 0;
        getLearnOneClause().maxBodyLength      = 7; // Changed by JWS for debugging purposes (feel free to edit).
        getLearnOneClause().maxNumberOfNewVars = 7;
        getLearnOneClause().maxDepthOfNewVars  = 7;
        getLearnOneClause().maxPredOccurrences = 3;
        getLearnOneClause().setMaxNegCoverage(0.4999); // Never cover more than 1/2th the negatives.  TODO - what about the 'always say neg' rule (or its equivalent)?  Assume flip-flop will handle?
        outerLooper.max_total_nodesExpanded    = 1000000;
        outerLooper.max_total_nodesCreated     =     100 * outerLooper.max_total_nodesExpanded;
        outerLooper.maxNumberOfClauses         = 2; // <-----------------------
        outerLooper.maxNumberOfCycles          = 2 * outerLooper.maxNumberOfClauses;
        getLearnOneClause().minNumberOfNegExamples = 1;
        getLearnOneClause().setMinPosCoverage(1);
        getLearnOneClause().restartsRRR = 25;
        getLearnOneClause().stringHandler.setStarMode(TypeSpec.minusMode);
        getLearnOneClause().setMEstimatePos(0.01);
        getLearnOneClause().setMEstimateNeg(0.01);
        gleaner.reportingPeriod = 1000;
        outerLooper.setMinPrecisionOfAcceptableClause(0.5);
        //outerLooper.initialize(false); // We want to initialize this as late as possible.
        outerLooper.setCheckpointEnabled(checkpointEnabled);
        getLearnOneClause().setDumpGleanerEveryNexpansions(1000);
    }

    private void setupRelevance(int runNumber, double probOfDroppping) throws SearchInterrupted {
        if (isRelevanceEnabled(runNumber, probOfDroppping)) {
            File file = getRelevanceFile(runNumber, probOfDroppping);
            try {
                getLearnOneClause().setRelevanceFile(file);
                getLearnOneClause().setRelevanceEnabled(true);
            } catch (FileNotFoundException fileNotFoundException) {
            	Utils.waitHere("Relevance File '" + file + "' not found:\n  " + fileNotFoundException);
                throw new SearchInterrupted("Relevance File '" + file + "' not found:\n  " + fileNotFoundException);
            } catch (IllegalStateException illegalStateException) {
                throw new SearchInterrupted(illegalStateException);
            }
            findExamplesWithAdvice();
        }
        else {
        	if ((createDataFilesOnly && !creatingInitialBIGdata) || createAdviceNoiseFiles || (useAdvice && !creatingInitialBIGdata)) { 
        		Utils.waitHere("Are we sure we don't want relevance enabled?  RunNumber = " + runNumber + ", prob(drop) = " + probOfDroppping + "  relevanceEnabled = " + relevanceEnabled); 
        	}
            getLearnOneClause().setRelevanceEnabled(false);
        }
    }
    
    private void findExamplesWithAdvice() {
    	List<Example> posExWithAdvice = learnOneClause.getAdviceProcessor().getExamplesWithUniqueAdvice(learnOneClause.getPosExamples());
    	List<Example> negExWithAdvice = learnOneClause.getAdviceProcessor().getExamplesWithUniqueAdvice(learnOneClause.getNegExamples());
    	
        posExamplesWithAdvice = new HashSet<Example>();
        for (Example ex : posExWithAdvice) {
            posExamplesWithAdvice.add(ex);
            ex.setAnnotationTerm( ex.getStringHandler().getStringConstant("% Unique Positive Advice"));
            Utils.println("% This POS example has associated advice: " + ex);
        }
        negExamplesWithAdvice = new HashSet<Example>();
        for (Example ex : negExWithAdvice) {
            negExamplesWithAdvice.add(ex);
            ex.setAnnotationTerm( ex.getStringHandler().getStringConstant("% Unique Negative Advice"));
            Utils.println("% This NEG example has associated advice: " + ex);
        }

    	Utils.println("% Read (for '" + prefix + "') " + Utils.comma(posExamplesWithAdvice) + " positive examples and " + Utils.comma(negExamplesWithAdvice) + " negative examples with advice.");
    }
    
    public HornClauseContext getContext() {
        if ( context == null ) {
            if ( outerLooper == null ) {
                context = new DefaultHornClauseContext();
            }
            else {
                context = getLearnOneClause().getContext();
            }
        }
        return context;
    }

    public boolean isRelevanceEnabled(int runNumber, double probOfDroppping) {
        return relevanceEnabled == null ? getRelevanceFile(runNumber, probOfDroppping).exists() : relevanceEnabled;
    }

    public void setRelevanceEnabled(Boolean relevanceEnabled) {
    	Utils.waitHere("setRelevanceEnabled = " + relevanceEnabled);
        this.relevanceEnabled = relevanceEnabled;
    }

    public boolean isRelevanceEnabledSet() {
        return relevanceEnabled != null;
    }
    
    public File getRelevanceFile(int runNumber, double probOfDroppping) {
    	
    	if (createAdviceNoiseFiles) {
            File relevanceFile = new CondorFile(directory + "/" + prefix + "_bkRel." + fileExtension);
            return relevanceFile;    		
    	}
    
    	if (runNumber >= 1 && runNumber <= 10 && probOfDroppping >= 0.0 && probOfDroppping <= 1.0) {
    		
    		if (probOfDroppping >= 1.0) { // No clauses at all in this case.
                File relevanceFile = new CondorFile(directory + "/" + prefix + "_bkRel_noRelevantClauses." + fileExtension);
                Utils.waitHere("DO NOT USE % Looking for  this relevance file: " + relevanceFile + " Exists: " + relevanceFile.exists());
                return relevanceFile; 
    		}    		
    		if (probOfDroppping <= 0.0) { // Use all the DE-DUPLICATED clauses in this case.
                File relevanceFile = new CondorFile(directory + "/clauseNoise/" + prefix + "_allAdviceClauseRel." + fileExtension);
                Utils.println("% Looking for this relevance file: " + relevanceFile + " Exists: " + relevanceFile.exists());
                return relevanceFile; 
    		}
    		
    		if (knownNoiseValue(probOfDroppping, AdviceProcessor.droppingProbs)) {
    			File relevanceFile = new CondorFile(directory + "/clauseNoise/" + prefix + "_prob" + Utils.truncate(100 * probOfDroppping, 0) + "_run" + runNumber + "_AdviceClauseRel." + fileExtension);
                Utils.println("% Looking for this relevance file: " + relevanceFile + " Exists: " + relevanceFile.exists());
    			return relevanceFile;
    		}
    		Utils.error("ProbOfDroppping must be one of " + AdviceProcessor.droppingProbs + ".  You provided: " + Utils.truncate(probOfDroppping, 2));
    	}
       
    	if (createDataFilesOnly) { Utils.waitHere("Should not reach here when creating data files.  RunNumber=" + runNumber + " prob(drop) = " + probOfDroppping); }
    	// Could also use:  "/clauseNoise/" + prefix + "_allAdviceClauseRel" but that is slightly different.
        File relevanceFile = new CondorFile(directory + "/" + prefix + "_bkRel." + fileExtension);
        return relevanceFile;
    }

    public boolean isOverWriteOldResults() {
        return overWriteOldResults;
    }

    public void setOverWriteOldResults(boolean overWriteOldResults) {
        if ( overWriteOldResults == true ) {
            Utils.warning("Overriding 'overWriteOldResults' to true.  I hope you know what you are doing.");
        }
        this.overWriteOldResults = overWriteOldResults;
    }


    
    private boolean knownNoiseValue(double givenProb, double[] knownProbs) {
    	if (knownProbs == null) { return false; }
    	for (double p : knownProbs) {
    		if (Math.abs(givenProb - p) < 0.01) { return true; } // Depending on how format (via Utils.truncate) works, this might not be correct, eg 0.49 vs 0.50, but that will only lead to a file-not-found error that should be relatively easy to figure out.
    	}
    	return false;
    }

    public LearnOneClause getLearnOneClause() {
        return learnOneClause;
    }
    
    public boolean onlyCheckingForMissingFiles = false;    
    private void reportExperimentStatusAndCleanAsNeeded() {
		boolean recreateNewResultsFiles = false;             // <--------------------- These two sort of go hand-in-hand, so maybe clean up to get rid of one.
		boolean call_extractVerifyResultsFromTheory = false; // <---------------------
		boolean reportMissingTheories   = true;
		boolean reportMissingResults    = true;
		boolean onlyReportIfBOTHmissing = false;
		
		int LOWER =     0; 
		int UPPER = 99999;
		
		Utils.doNotCreateDribbleFiles  = false;
		Utils.createDribbleFile(directory + (reportMissingTheories && reportMissingResults
															? (recreateNewResultsFiles ? "missingFiles.txt"       : "missingFilesOnly.txt")
															: (reportMissingTheories   ? "missingTheoryFiles.txt" : "missingResultsFiles.txt"))); 
		//Utils.createDribbleFile(directory + "missingFilesFakedButReasonabletoDoSo.txt");
		int countOfFilesConsidered = 0, countOfFilesMissingTheories = 0, countOfFilesMissingResults = 0, countOfBothMissing = 0;
		
		for (int advice = 0; advice <= 1; advice++) {
			if (advice > 0) { useAdvice = true; } else { useAdvice = false; }
			
			for (int d = 0; d < droppingProbs.length; d++) {
				probOfDroppingLiteral = droppingProbs[d];
				if (!useAdvice && probOfDroppingLiteral > 0) { continue; }

				for (int f = 0; f < classLabelProbs.length; f++) {
					probOfFlippingClassLabel = classLabelProbs[f];
					if (probOfDroppingLiteral > 0 && probOfFlippingClassLabel > 0) { continue; }
					runNumberFirst = 1;
					if (probOfDroppingLiteral <= 0.0 && probOfFlippingClassLabel <= 0.0) { runNumberLast = 1; }	else { runNumberLast = 10; }	
					
					for (int e = 0; e < fractExamples.length; e++) {
						fractionOfTrainingExamplesToUse = fractExamples[e];
						
						for (String str : lessonsToUse) for (runNumberInUse = runNumberFirst; runNumberInUse <=  runNumberLast; runNumberInUse++) {	
							if (lessonsToSkip.contains(str) || "".equalsIgnoreCase(str) || runNumberLast < runNumberInUse) { continue; }							
							
							prefix    = str;		
							directory = mainWorkingDir + str;	
							countOfFilesConsidered++;
							
							if (countOfFilesConsidered < LOWER || countOfFilesConsidered > UPPER) { // Utils.waitHere("LOWER? " + LOWER + " " + UPPER); 
								continue; 
							}
							
							if (countOfFilesConsidered % 1000 == 0) { 
								System.out.println("@ COUNT " + Utils.comma(countOfFilesConsidered) + "  " + str + " e = " + e + " f = " + f + " d = " + d + " advice = " + advice + "  " + getFilePostfix()); 
							}
						//	waitHereUnlessCondorJob(str + " flip=" + probOfFlippingClassLabel + " drop=" + probOfDroppingLiteral + " advice=" + useAdvice + "  " + m.getFilePostfix());
							File theoryFile  = Utils.ensureDirExists(directory + "/theories/"       + prefix + "_theory"        + getFilePostfix() + "." + fileExtension);
							File resultsFile = Utils.ensureDirExists(directory + "/testSetResults/" + prefix + "_testsetResult" + getFilePostfix() + "." + fileExtension);
							
							boolean missing_theoryFile  = !theoryFile.exists();
							boolean missing_resultsFile = !resultsFile.exists();

		         			if (missing_theoryFile && missing_resultsFile) { countOfBothMissing++;          }
		         			if (missing_theoryFile)                        { countOfFilesMissingTheories++; }
		         			if (missing_resultsFile)                       { countOfFilesMissingResults++;  }
							
							if (reportMissingTheories && reportMissingResults && missing_theoryFile && missing_resultsFile) {
			         			Utils.println("\nMISSING THEORY:  #" + Utils.comma(countOfFilesMissingTheories) + " (of " + Utils.comma(countOfFilesConsidered) + "): " + theoryFile); 
			         			Utils.println(  "MISSING RESULTS: #" + Utils.comma(countOfFilesMissingResults)  + " (of " + Utils.comma(countOfFilesConsidered) + "): " + resultsFile);					         				
			         		}
							if (reportMissingTheories && !reportMissingResults  && !onlyReportIfBOTHmissing) Utils.println("\nMISSING THEORY:  #" + Utils.comma(countOfFilesMissingTheories) + " (of " + Utils.comma(countOfFilesConsidered) + "): " + theoryFile);
							if (reportMissingResults  && !reportMissingTheories && !onlyReportIfBOTHmissing) Utils.println("\nMISSING RESULTS: #" + Utils.comma(countOfFilesMissingResults)  + " (of " + Utils.comma(countOfFilesConsidered) + "): " + resultsFile);
			         				         			
				         	if (missing_theoryFile) { 
								if (!missing_resultsFile) {
									Utils.waitHere("Make the noTheoryWasLearned file?  THIS SHOUILD NO LONGER HAPPEN. ");
									noTheoryWasLearned(); // If no theory exists, but there are results, create the 'no theory learned' (this should no longer happen - before no-theory only produced a results file, but no theory file, however we need to distinguish not-yet-tried from no-theory-learned.							
								}
							}
				         	if (missing_resultsFile) { 
				         		if (recreateNewResultsFiles && !missing_theoryFile) { 
				         		//	Utils.println("What happened: " + theoryFile);
				         			
				         			Utils.println("Recompute @ COUNT " + Utils.comma(countOfFilesConsidered) + "  " + str + " e = " + e + " f = " + f + " d = " + d + " advice = " + advice + "  " + getFilePostfix());
				         			Utils.println("Have:        " + theoryFile);
				         			Utils.println("But missing: " + resultsFile);

                                    if ( call_extractVerifyResultsFromTheory && isTheoryNothingLearned(theoryFile) == false ) {
                                        CrossValidationFoldResult r = extractVerifyResultsFromTheory(theoryFile, resultsFile);
                                        if ( r != null ) {
                                        	Utils.waitHere("About to create missing results file from theory file:\nResults file:" + resultsFile );
                                            Utils.println("Creating Missing Results file " + resultsFile);
                                            Utils.waitHere("Need to fix because TUNING sets no longer used.");
                                            saveResultsToFile(r.getTrainingCoverageScore().getAccuracy(), -123.456, r.getEvaluationCoverageScore().getAccuracy());
                                        }
                                        else {
                                            Utils.warning("Attempted to recreate results file but failed: " + resultsFile);
                                        }
                                    }
                                    else if (call_extractVerifyResultsFromTheory) {
                                    	Utils.waitHere("NOTHING LEARNED: " + theoryFile + ".\n  Will create the 50/50/50 results file.");
                                    	if (missing_resultsFile) saveDefaultResultsToFile(); // Put this extra check in for safety.
                                    } else {
                                    	Utils.waitHere("You might want to set call_extractVerifyResultsFromTheory=true and rerun?");
                                    }
				         		}				         		
				         	}
                            else if ( call_extractVerifyResultsFromTheory && !missing_theoryFile){
                            	if ( isTheoryNothingLearned(theoryFile) == false ) {
                            		extractVerifyResultsFromTheory(theoryFile, resultsFile);
                            	}
                            	else if (missing_resultsFile) {
                            		Utils.println("NOTHING LEARNED BUT THEORY FILE EXISTS: " + theoryFile + "\nWILL SAVE 0.50/0.50/0.50 as the results file.  TODO: correct for data skew");
                            		saveDefaultResultsToFile(); 
                            	} else { Utils.println("HEY! The results file already exists, so keeping that one."); }
                            }
						}
					}
				}
			}
		}
		Utils.println(  "\ncountOfFilesConsidered      = " + Utils.comma(countOfFilesConsidered)
					  + "\ncountOfFilesMissingTheories = " + Utils.comma(countOfFilesMissingTheories)
					  + "\ncountOfFilesMissingResults  = " + Utils.comma(countOfFilesMissingResults)
					  + "\ncountOfBothMissing          = " + Utils.comma(countOfBothMissing));
		System.exit(0);
    }

    public void setupUserOverrides() {

    }


    private static boolean creatingInitialBIGdata = false;


    public class RecordActiveAdviceSearchListener implements ILPSearchListener {
        ILPparameterSettings currentOnionSettings = null;
        int currentFold;

        public ILPSearchAction onionLayerStarting(TuneParametersForILP onion, ILPparameterSettings onionLayer) {
            currentOnionSettings = onionLayer;
            return ILPSearchAction.PERFORM_LOOP;
        }

        public void onionLayerFinished(TuneParametersForILP onion, ILPparameterSettings onionLayer) {
        }

        public ILPSearchAction crossValidationFoldStarting(ILPCrossValidationLoop cvLoop, int fold) {
            return ILPSearchAction.PERFORM_LOOP;
        }

        public void crossValidationFoldFinished(ILPCrossValidationLoop cvLoop, int fold) {
            this.currentFold = fold;

        }

        public ILPSearchAction outerLoopStarting(ILPouterLoop outerLoop) {
            // Record the advice for this currentFold & Onion layer...
            if ( useAdvice ) {
                String fileName = directory + "/activeAdvice/" + prefix + "_activeAdvice" + getFilePostfix() + "_onionLayer" + currentOnionSettings.getOnionLayer() + "_cvFold" + currentFold + "." + fileExtension;
          //	waitHereUnlessCondorJob("testSetFileName = " + testSetFileName);
                File   file     = Utils.ensureDirExists(fileName);
                try {

                    new CondorFileWriter(file, false).append(outerLoop.getActiveAdvice().toString() + "\n").close();
                } catch (IOException e) {
                    Utils.waitHere("% Could not save the active advice to file:\n%  " + file + "\n%  " + e);
                }
            }

            return ILPSearchAction.PERFORM_LOOP;
        }

        public void outerLoopFinished(ILPouterLoop outerLoop) {
        }

        public ILPSearchAction innerLoopStarting(LearnOneClause learnOneClause) {
            return ILPSearchAction.PERFORM_LOOP;
        }

        public void innerLoopFinished(LearnOneClause learnOneClause) {

        }

    }
}
