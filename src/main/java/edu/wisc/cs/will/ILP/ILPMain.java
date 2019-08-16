package edu.wisc.cs.will.ILP;

import java.io.File;
import edu.wisc.cs.will.Utils.condor.CondorFile;

import java.io.FileNotFoundException;
import java.io.IOException;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.ResThmProver.DefaultHornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 *
 * @author twalker
 */
public final class ILPMain {

    public ILPouterLoop outerLooper;

    private LearnOneClause learnOneClause;

    public HornClauseContext context;

    public int numberOfFolds = 1;

    public String directory;

    public String prefix = null;

    public int firstFold = 0;

    public int lastFold = -1;

    public boolean checkpointEnabled = false;

    public boolean useRRR = false;

    public boolean flipFlopPosNeg = false;

    public String fileExtension = Utils.defaultFileExtension;

    boolean useOnion = true;

    public Boolean relevanceEnabled = true;

    private static final String testBedsPrefix = "../Testbeds/"; // But DO include the backslash here.

    public ILPMain() {
    }

    public void setup(String... args) throws SearchInterrupted {
        args = Utils.chopCommentFromArgs(args);

        Utils.Verbosity defaultVerbosity = Utils.isDevelopmentRun() ? Utils.Verbosity.Developer : Utils.Verbosity.Medium;

        processFlagArguments(args);

        Utils.seedRandom(12345);

        if (Utils.isVerbositySet() == false) {
            Utils.setVerbosity(defaultVerbosity);
        }

        if (lastFold == -1) {
            lastFold = numberOfFolds - 1;
        }

        boolean partialRun = (firstFold != 0 && lastFold != numberOfFolds - 1);

        setupDirectoryAndPrefix(args);

        String[] newArgList = new String[4];
        newArgList[0] = directory + "/" + prefix + "_pos." + fileExtension;
        newArgList[1] = directory + "/" + prefix + "_neg." + fileExtension;
        newArgList[2] = directory + "/" + prefix + "_bk." + fileExtension;
        newArgList[3] = directory + "/" + prefix + "_facts." + fileExtension;

        if (flipFlopPosNeg) {
            String temp = newArgList[0];
            newArgList[0] = newArgList[1];
            newArgList[1] = temp;
        }

        Utils.createDribbleFile(directory + "/" + prefix + "_dribble" + (useRRR ? "_rrr" : "") + (flipFlopPosNeg ? "_flipFlopped" : "") + (partialRun ? "_fold" + firstFold + "to" + lastFold : "") + "." + fileExtension);
        //	Utils.waitHere(directory + prefix + "_dribble" + (useRRR ? "_rrr" : "") + (flipFlopPosNeg ? "_flipFlopped" : "") + (partialRun ? "_fold" + firstFold + "to" + lastFold : "" ) + "." + fileExtension);

        try {
            //	HandleFOPCstrings stringHandler = new HandleFOPCstrings(lowerCaseMeansVariable);
            if (context == null) {
                context = new DefaultHornClauseContext();
            }
            outerLooper = new ILPouterLoop(directory, prefix, newArgList, new Gleaner(), context);
        } catch (IOException e) {
            Utils.reportStackTrace(e);
            Utils.error("File not found: " + e.getMessage());
        }
        setupParameters();

        if (getLearnOneClause().createdSomeNegExamples) {
            Example.writeObjectsToFile(newArgList[1], getLearnOneClause().getNegExamples(), ".", "// Negative examples, including created ones.");
        }

        setupRelevance();
    }

    private void processFlagArguments(String[] args) throws IllegalArgumentException {
        // Allow these three to come in any order.
        for (int arg = 1; arg < args.length; arg++) {
            if (args[arg].equalsIgnoreCase("rrr") || args[arg].startsWith("-rrr")) {
                useRRR = true;
            }
            else if (args[arg].equalsIgnoreCase("true") || args[arg].startsWith("-true")) {
                useRRR = true;
            }
            else if (args[arg].equalsIgnoreCase("false") || args[arg].startsWith("-false")) {
                useRRR = false;
            }
            else if (args[arg].equalsIgnoreCase("std") || args[arg].startsWith("-std")) {
                useRRR = false;
            }
            else if (args[arg].startsWith("flip") || args[arg].startsWith("-flip")) {
                flipFlopPosNeg = true;
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
            else if (args[arg].startsWith("-fold=")) {
                firstFold = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
                lastFold = firstFold;
            }
            else if (args[arg].equals("-checkpoint")) {
                checkpointEnabled = true;
            }
            else if (args[arg].equals("-relevance")) {
                relevanceEnabled = true;
            }
            else if (args[arg].equals("-norelevance")) {
                relevanceEnabled = false;
            }
            else if (args[arg].startsWith("-maxTime=")) {
                int i = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
                if (i <= 0) {
                }
                else {
                }
            }
            else if (args[arg].startsWith("useOnion") || args[arg].equalsIgnoreCase("-useOnion")) {
                useOnion = true;
            }
            else if (args[arg].startsWith("onion") || args[arg].equalsIgnoreCase("-onion")) {
                useOnion = true;
            }
            else if (args[arg].startsWith("noonion") || args[arg].startsWith("noOnion") || args[arg].equalsIgnoreCase("-noOnion")) {
                useOnion = false;
            }
            else if (args[arg].startsWith("-") == false) {
                fileExtension = args[1];
            }
            else {
                throw new IllegalArgumentException("Unknown argument specified: " + args[arg]);
            }
        }
    }

    private void setupDirectoryAndPrefix(String[] args) throws IllegalArgumentException {
        // LearnOnClause performs the inner loop of ILP.
        directory = args[0];
        File dir = new CondorFile(directory);
        if (dir.isDirectory() == false) {
            dir = new CondorFile(testBedsPrefix + directory);
        }
        if (dir.isDirectory() == false) {
            throw new IllegalArgumentException("Unable to find problem directory '" + directory + "'.");
        }
        directory = dir.getPath();
        if (prefix == null) {
            prefix = dir.getName();
        }
        if (prefix.endsWith("/")) {
            prefix = prefix.substring(0, prefix.length() - 1);
        }
    }

    private void setupParameters() {
        Gleaner gleaner = (Gleaner) getLearnOneClause().searchMonitor;
        outerLooper.writeGleanerFilesToDisk = true;
        //		if (args.length > 3) { getLearnOneClause().setMinPosCoverage(Double.parseDouble(args[3])); }
        //		if (args.length > 4) { getLearnOneClause().setMinPrecision(  Double.parseDouble(args[4]));   }
        // Set some additional parameters for the inner-loop runs.
        getLearnOneClause().setMaxNodesToConsider(10000); // <-----------------------
        getLearnOneClause().setMaxNodesToCreate(100000);
        getLearnOneClause().maxSearchDepth = 1000;
        getLearnOneClause().verbosity = 0;
        getLearnOneClause().maxBodyLength = 4; // Changed by JWS for debugging purposes (feel free to edit).
        getLearnOneClause().maxNumberOfNewVars = 6;
        getLearnOneClause().maxDepthOfNewVars = 6;
        getLearnOneClause().maxPredOccurrences = 6;
        outerLooper.max_total_nodesExpanded = 100000; // <-----------------------
        outerLooper.max_total_nodesCreated = 10 * outerLooper.max_total_nodesExpanded;
        outerLooper.maxNumberOfClauses = 2; // <-----------------------
        outerLooper.maxNumberOfCycles = 2 * outerLooper.maxNumberOfClauses;
        getLearnOneClause().minNumberOfNegExamples = 1;
        getLearnOneClause().setMinPosCoverage(1);
        getLearnOneClause().restartsRRR = 25;
        getLearnOneClause().stringHandler.setStarMode(TypeSpec.plusMode);
        getLearnOneClause().setMEstimatePos(0.01); // <-----------------------
        getLearnOneClause().setMEstimateNeg(0.01); // <-----------------------
        gleaner.reportingPeriod = 1000;
        outerLooper.setMinPrecisionOfAcceptableClause(0.5);// <-----------------------
        //outerLooper.initialize(false); // We want to initialize this as late assert possible.
        outerLooper.setCheckpointEnabled(checkpointEnabled);
        getLearnOneClause().setDumpGleanerEveryNexpansions(1000);
    }

    private void setupRelevance() throws SearchInterrupted {
        if (isRelevanceEnabled()) {
            try {
                File file = getRelevanceFile();
                getLearnOneClause().setRelevanceFile(file);
                getLearnOneClause().setRelevanceEnabled(true);
            } catch (FileNotFoundException fileNotFoundException) {
                throw new SearchInterrupted("Relevance File '" + getRelevanceFile() + "' not found:\n  " + fileNotFoundException);
            } catch (IllegalStateException illegalStateException) {
                throw new SearchInterrupted(illegalStateException);
            }
        }
        else {
            getLearnOneClause().setRelevanceEnabled(false);
        }
    }

    public HornClauseContext getContext() {
        if (context == null) {
            if (outerLooper == null) {
                context = new DefaultHornClauseContext();
            }
            else {
                context = getLearnOneClause().getContext();
            }
        }

        return context;
    }

    public boolean isRelevanceEnabled() {
        return relevanceEnabled == null ? getRelevanceFile().exists() : relevanceEnabled;
    }

    public File getRelevanceFile() {
        File relevanceFile = new CondorFile(directory + "/" + prefix + "_bkRel." + fileExtension);

        return relevanceFile;
    }

    public LearnOneClause getLearnOneClause() {
        return outerLooper.innerLoopTask;
    }

}
