/*
 * General-purpose utilities, basically a collection of functions.
 * http://www.eclipse.org/articles/Article-TPTP-Profiling-Tool/tptpProfilingArticle.html
 * http://www.eclipse.org/tptp/home/downloads/drops/TPTP-4.2.0.html#tptp-plugins
 * http://www.ibm.com/developerworks/offers/lp/demos/summary/javaprofile.html
 */

// TODO(@hayesall): `getPrecision`, `getRecall`, `getFBeta`, `getF1`, `getAccuracy` belong in a "metrics" class
// TODO(@hayesall): `help_getScratchDirForUser` needs to be destroyed in a fire.
// TODO(@hayesall): Many of these are FileSystem methods. Abstracting the file system as a class would help.

package edu.wisc.cs.will.Utils;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.regex.Matcher;

import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.Utils.condor.CompressedInputStream;
import edu.wisc.cs.will.Utils.condor.CompressedOutputStream;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;
import edu.wisc.cs.will.Utils.condor.CondorUtilities;
import java.io.BufferedWriter;
import java.io.OutputStreamWriter;
import java.util.regex.Pattern;

/**
 * Some general-purpose utilities. This class is basically a collection of
 * functions intended to be accessible to and used by many classes. In keeping
 * with the spirit of functions, all the fields and methods of this class are
 * static.
 * 
 * @author shavlik
 */
public class Utils {
	
	// For large-scale runs we do not want to create dribble (nor 'debug') files. 
	public static Boolean doNotCreateDribbleFiles  = false;
	private static Boolean doNotPrintToSystemDotOut = false;

    // If the strings MYUSERNAME appear in file names, they will be replaced with these settings.
	private static String MYUSERNAME       = null; // If we add to this list, edit replaceWildCards().
    private static String MYSCRATCHDIR     = null;
	

	/** Stores whether this is a developer run.
     *
     * This should null initially.  The getter/setter will initialize it
     * appropriately the first time it is accessed.  Please do not use it
     * directly, as that will probably result in a null exception somewhere
     * along the line.
     */
    private static Boolean developmentRun = null; // Should be null.  See comment.

    /** Stores whether verbose output should be used.
     *
     * This should null initially.  The getter/setter will initialize it
     * appropriately the first time it is accessed.  Please do not use it
     * directly, as that will probably result in a null exception somewhere
     * along the line.
     */
    private static Boolean verbose = null; // Should be null.  See comment.

    /** Stores whether waitHereEnabled output should be used.
     *
     * This should null initially.  The getter/setter will initialize it
     * appropriately the first time it is accessed.  Please do not use it
     * directly, as that will probably result in a null exception somewhere
     * along the line.
     */
    private static Boolean waitHereEnabled = null; // Should be null.  See comment.

    /** Stores whether severeErrorThrowsEnabled output should be used.
     *
     * This should null initially.  The getter/setter will initialize it
     * appropriately the first time it is accessed.  Please do not use it
     * directly, as that will probably result in a null exception somewhere
     * along the line.
     */
    private static Boolean severeErrorThrowsEnabled = null; // Should be null.  See comment.

    private static Set<MessageType> filteredMessageTypes = EnumSet.noneOf(MessageType.class);

	// These relate to determining whether or not someone is a WILL developer.
	// WILL developers should create a file whose name is that stored by DEVELOPER_MACHINE_FILE_NAME 
	// in their 'home directory'.  
	//   In Windows this typically is "C:\\Documents and Settings\\shavlik", where 'shavlik' is replaced by one's login name.
	//   In Unix, this is "~/:
	// You can call getUserHomeDir() to find out.	
    private static final String DEVELOPER_MACHINE_PROPERTY_KEY = "edu.wisc.cs.bl.devrun"; // Used to see if this is a 'developer run' - if not, less might be printed and waitHere()'s will become warnings.
    private static final String DEVELOPER_MACHINE_FILE_NAME    = "runWILLasDeveloper.txt";


    /** Some Standard verbosity levels.  
     * 
     * The verbosity level can be set via the setVerbosity method.  That actually updates
     * the verbose, extraVerbose, waitHereEnabled, and severeErrorThrowsEnabled settings.
     * 
     * These are just suggested levels.  All of the four controlling factors can be overridden by setting
     * the appropriate value through the setter.
     */
    public enum Verbosity {
        Developer(true,true,true,true,true),  // Print everything and waitHeres wait, severeError cause a throw.
        DeveloperNoWait(true,true,false,true,false),      // Print everything, waitHeres don't wait, severeError cause a throw.
        High(false,true,false,true,false),
        Medium(false,true,false,false,false),   // Print everything, waitHeres don't wait, severeError just print error
        Low(false,false,false,false,false);     // Print nothing.

        boolean developmentRun;
        boolean print;
        boolean waitHere;
        boolean severeWarningThrowsError;
        boolean extraVerbose;

        Verbosity(boolean developmentRun, boolean print, boolean waitHere, boolean severeWarningThrowsError, boolean extraVerbose) {
            this.developmentRun = developmentRun;
            this.print    = print;
            this.waitHere = waitHere;
            this.severeWarningThrowsError = severeWarningThrowsError;
            this.extraVerbose = extraVerbose;
        }
    }

    /** Sets the verbose, extraVerbose, waitHereEnabled, and severeErrorThrowsEnabled according to the indicated verbosity.
     *
     * These are just standard settings.  You can override these with the appropriate setters
     * for the specific settings.
     */
    public static void setVerbosity(Verbosity verbosity) {
        developmentRun           = verbosity.developmentRun;
        verbose                  = verbosity.print;
        waitHereEnabled          = verbosity.waitHere;
        severeErrorThrowsEnabled = verbosity.severeWarningThrowsError;
    }

    /** The Default file extension to add to "normal" files.
     *
     * This does not (and should not) include a . prior to the extension.
     */
    public static final String defaultFileExtension           = "txt";
    public static final String defaultFileExtensionWithPeriod = "." + defaultFileExtension;

    /**
     * How much two numbers (outside of (-1, 1) can differ before they are no longer considered
     * equivalent.
     */
    private static final double EQUIVALENCE_TOLERANCE = 0.0000001; 
    // FOr numbers in [-1, 1] use this (probably could simply use Double.MIN_NORMAL).
    private static final double EQUIVALENCE_TOLERANCE_SMALL_NUMBERS = 8 * Double.MIN_NORMAL;

    /**
     * If non-null, copy all printing to this stream as well.
     */
    private static PrintStream dribbleStream       = null;  // <----- 'state' being held in this static.  BUGGY if multiple threads running.
    private static PrintStream dribbleStream2      = null;  // <----- 'state' being held in this static.  BUGGY if multiple threads running.
    private static PrintStream debugStream         = null;  // <----- 'state' being held in this static.  BUGGY if multiple threads running.
    private static PrintStream warningStream       = null;  // <----- 'state' being held in this static.  BUGGY if multiple threads running.
    private static PrintStream warningShadowStream = null;  // <----- 'state' being held in this static.  BUGGY if multiple threads running.

    /** The random instance for all the random utility functions. */
    private static Random randomInstance = new Random(112957);

    private static Map<String,Integer> warningCounts = new HashMap<>();

	private static BufferedReader inBufferedReader;

	private static final int maxStringLength = 25000;
    /**
     * Displays a string to the standard output stream and the dribble stream if
     * applicable. Ends with a newline.
     *
     */
    public static void println(String strRaw, boolean printRegardless) {
    	if (printRegardless || isVerbose() ) {
    		String str = (strRaw == null || strRaw.length() <= maxStringLength ? strRaw : strRaw.substring(0, maxStringLength) + " ... [string too long]");
    		if (!doNotPrintToSystemDotOut) { System.out.println(str); }
    		if (dribbleStream != null) { dribbleStream.println(str); }  // No need to flush since println already does so
    	}
    }

    public static void printlnErr(MessageType type, String str) { // Use this when adding some temp prints so it is easy to find them when you want to later delete (or comment out) them.
    	if ( isMessageTypeEnabled(type) ) printlnErr(str);
    }
    public static void printlnErr(String strRaw) {
    	if ( isVerbose() ) {
    		String str = (strRaw == null || strRaw.length() <= maxStringLength ? strRaw : strRaw.substring(0, maxStringLength) + " ... [string too long]");
    		boolean hold = doNotPrintToSystemDotOut;
    		doNotPrintToSystemDotOut = false; // If these printout become too much, we can add a 3rd flag to override these ...
            System.err.println(str);
            if (dribbleStream != null) { dribbleStream.println(str); }  // No need to flush since println already does so.
            doNotPrintToSystemDotOut = hold;
    	}
    }
    public static void println(String str) {
    	println(str, false);
    }
    public static void println(MessageType type, String str) {
    	if ( isMessageTypeEnabled(type)) println(str, false);
    }

    /**
     * Displays a string to the standard output stream and the dribble stream if
     * applicable. No newline at the end.
     */
    public static void print(String strRaw, boolean printRegardless) {
    	if (printRegardless || isVerbose()) {
    		String str = (strRaw == null || strRaw.length() <= maxStringLength ? strRaw : strRaw.substring(0, maxStringLength) + " ...");
    		if (!doNotPrintToSystemDotOut) {System.out.print(str); }
    		if (dribbleStream != null) { dribbleStream.print(str); }
    	}
    }
    public static void print(String str) {
    	print(str, false);
    }
    public static void print(MessageType type, String str) {
    	if ( isMessageTypeEnabled(type)) print(str, false);
    }

    public static String comma(int value) { // Always use separators (e.g., "100,000").
    	return String.format("%,d", value);    	
    }    
    public static String comma(long value) { // Always use separators (e.g., "100,000").
    	return String.format("%,d", value);    	
    }   
    public static String comma(double value) { // Always use separators (e.g., "100,000").
    	return String.format("%,f", value);    	
    }
    public static String comma(Collection<?> collection) {
    	return comma(getSizeSafely(collection));
    }
    public static String comma(Map<?,?> map) {
    	return comma(getSizeSafely(map));
    }
	
	public static String[] chopCommentFromArgs(String[] args) {
	  if (args == null) { return null; } // Written with help from Trevor Walker.
	  int commentStart = -1;
	  for (int i = 0; i < args.length; i++) {
		  if (args[i] != null && args[i].startsWith("//") ) {
			  commentStart = i;
			  break;
		  }
	  }
	  if (commentStart < 0) { return args; }
      String[] newArgs = new String[commentStart];
	  System.arraycopy(args, 0, newArgs, 0, commentStart);
	  return newArgs;
	}
	
    /**
     * Converts a list to a string that shows at most 100 elements.
     * 
     * @param list The list to print.
     * @return A string representing the first 100 elements of the given list,
     *         or null if the given list is null.
     */
    public static String limitLengthOfPrintedList(Collection<?> list) {
        return limitLengthOfPrintedList(list, 100);
    }

    /**
     * Converts a collection to a string that shows at most maxSize elements.
     * 
     * @param collection The collection to print.
     * @param maxItems How many elements to print, at most.
     * @return A string representing at most the first maxSize elements of the given
     *         collection, or null if the given collection is null.
     */
	   public static String limitLengthOfPrintedList(Collection<?> collection, int maxItems) {
        if (collection == null) {
            return null;
        }
        int size = getSizeSafely(collection);
        if (size <= maxItems) {
            return collection.toString();
        }
        Iterator<?> iter = collection.iterator();
        StringBuilder result = new StringBuilder("[" + iter.next());
        if (size > 1) {
            for (int i = 1; i < maxItems; i++) {
                result.append(", ").append(iter.next());
            }
        }
        return result + ", ..., plus " + comma(size - maxItems) + " more items]";
    }
	   
    /**
     * Converts a map to a string that shows at most maxSize elements.
     * 
     * @param map The map to print.
     * @param maxItems How many set elements to print, at most.
     * @return A string representing the first maxSize elements of the given
     *         map, or null if the given map is null.
     */
	public static String limitLengthOfPrintedList(Map<?,?> map, int maxItems) {
		if (map == null) { return null; }
		return limitLengthOfPrintedList(map.entrySet(), maxItems);
	}
	public static String limitLengthOfPrintedList(Map<?,?> map) {
		return limitLengthOfPrintedList(map, 100);
	}

    /**
	 * Save some typing when throwing generic errors.
     */
	public static void error(String msg) {
        warning_println("\nERROR:   " + msg);
		if ( CondorUtilities.isCondor() ) {
			System.err.println("\nERROR:   " + msg);
	        // Nice to print the calling stack so one can see what caused the error ...
			// Doing it this way puts the stack in the ERROR file.
			(new Exception()).printStackTrace();
            println("\n" + msg);
	        println("\nSince this is a condor job, will exit.");
	        cleanupAndExit();
		}
		throw new WILLthrownError("\n " + msg);
	}
	public static void error() {
		throw new WILLthrownError("\n Should not happen ...");
	}

	/**
	 * Provide a simple way to mark code that still needs to be written.
     *
     */
	public static void writeMe(String msg) {
		error("writeMe: " + msg);
	}
	public static void writeMe() {
		error("writeMe");
	}

    /**
     * Flushes the standard output stream.
     */
    public static void flush() {
        if (isVerbose() && !doNotPrintToSystemDotOut) { System.out.flush(); }
    }

    /**
     * Sort (in place this list of doubles and remove duplicate values (where
     * 'duplicate(a,b)' is 'not diffDoubles(a,b).'
     *
     * Sort (in place this list of doubles and remove duplicate values (where
     * 'duplicate(a,b)' is defined by the comparator). public static <E> void
     * sortAndRemoveDuplicates(List<E> items, Comparator<E> comparator) {
     * Collections.sort(items); <--- error here E prev = null; for (Iterator<E>
     * iter = items.iterator(); iter.hasNext(); ) { E item = iter.next(); if
     * (prev == null || comparator.compare(item, prev) == 0) { prev = item; } //
     * BUG: wont remover duplicate NULLS. Use a counter to see if at first item?
     * else { iter.remove(); } } }
     *
     * @param items List to be sorted and duplicates removed.
     */
    public static void sortListOfDoublesAndRemoveDuplicates(List<Double> items, double tolerance, double toleranceSmallNumbers) {  // TODO use the above and make diffDoubles a comparator.
    	Collections.sort(items);

    	Double prev = null;
    	for (Iterator<Double> iter = items.iterator(); iter.hasNext(); ) {
    		Double d = iter.next();
    		if (prev == null || diffDoubles(prev, d, tolerance, toleranceSmallNumbers)) { prev = d; }
    		else { iter.remove(); }
    	}
	}

    public static void sortListOfDoublesAndRemoveDuplicates(List<Double> items) {
    	sortListOfDoublesAndRemoveDuplicates(items, EQUIVALENCE_TOLERANCE, EQUIVALENCE_TOLERANCE_SMALL_NUMBERS);
    }
    
    /**
     * "Safely" returns the size of a collection.
     *
     * @return The size of the given collection, or zero if the collection is null.
     */
    public static int getSizeSafely(Collection<?> collection) {
        if (collection == null) { return 0; }
        return collection.size();
    }
    public static int getSizeSafely(Map<?,?> map) {
        if (map == null) { return 0; }
        return map.size();
    }
    public static int getSizeSafely(String str) {
        if (str == null) { return 0; }
        return str.length();
    }
    public static int getSizeSafely(Iterator<?> collection) {
    	if (collection == null) { return 0; }
    	int counter = 0;
    	while(collection.hasNext()) {
    		collection.next();
    		counter++;
    	}
    	return counter;
    }
    public static int getSizeSafely(Integer integer) { // This version helps if we lookup in a <Object,Integer> map; i.e., default to 0 if not there. 
        if (integer == null) { return 0; }
        return integer;
    }

    // TODO(@hayesall): Utils/MapOfSets.java uses this?
    static String getStringWithLinePrefix(String string, String prefix) {
        if (prefix != null && !prefix.isEmpty() && !string.isEmpty()) {

            StringBuilder stringBuilder = new StringBuilder();


            int index = -1;
            int lastIndex = 0;

            stringBuilder.append(prefix);

            while ((index = string.indexOf("\n", index + 1)) != -1) {
                String s = string.substring(lastIndex, index + 1);

                if (!s.isEmpty()) {
                    if (lastIndex != 0) {
                        stringBuilder.append(prefix);
                    }
                    stringBuilder.append(s);
                }

                lastIndex = index + 1;
            }

            if (lastIndex != 0) {
                stringBuilder.append(prefix);
            }
            stringBuilder.append(string.substring(lastIndex));

            return stringBuilder.toString();
        }
        else {
            return string;
        }
    }

    /**
     * Create a file-name string from this directory and (possibly partial) fileName. 
     * (Could just return a File, but this is what other methods are expecting.)
     * 
     * @param directoryRaw The directory containing the file.
     * @param fileNameRaw The name of the file.
     * @return A path string indicating the given file within the given directory.
     */
    public static String createFileNameString(String directoryRaw, String fileNameRaw) {
    	String directory = replaceWildCards(directoryRaw);
    	String fileName  = replaceWildCards(fileNameRaw);
    	
        if (directory == null) { return fileName; }
        File f = new CondorFile(fileName);
        if (f.isAbsolute()) { return fileName; }

        f = new CondorFile(directory, fileName);
        ensureDirExists(f);
        return f.getPath();
    }
    
    // Should we cache?  If we do, cache needs to be cleared whenever any of these keywords are changed.
    private static Map<String,String> environmentVariableResolutionCache = new HashMap<>(4);
    public static String replaceWildCards(String original) {
    	if (original == null) { return null; }
    	String lookup = environmentVariableResolutionCache.get(original);
    	if (lookup != null) { return lookup; }

        lookup = original;

		lookup = !lookup.contains("MYUSERNAME") ? lookup : lookup.replaceAll("MYUSERNAME", getMyUserName()); // Break into multiple lines so we can localize bugs better.
    	lookup = !lookup.contains("MYPATHPREFIX") ? lookup : lookup.replaceAll("MYPATHPREFIX",     getMyPathPrefix());
    	lookup = !lookup.contains("SHAREDPATHPREFIX") ? lookup : lookup.replaceAll("SHAREDPATHPREFIX", getSharedPathPrefix());
    	lookup = !lookup.contains("MYSCRATCHDIR") ? lookup : lookup.replaceAll("MYSCRATCHDIR",     getMyScratchDir());
    	environmentVariableResolutionCache.put(original, lookup);
    	return lookup;
    }	
	public static String replaceWildCardsAndCheckForExistingGZip(String fileNameRaw) {
		String fileName = replaceWildCards(fileNameRaw);
		if (fileName.endsWith(".gz")) { return fileName; } // If already a gzip'ed file, simply return.
		
		// Otherwise see if BOTH versions exist.
		File regular = new CondorFile(fileName);
		File gZipped = new CondorFile(fileName + ".gz");
		boolean regExists = regular.exists();
		boolean zipExists = gZipped.exists();
		if (regExists && zipExists) {
			long dateReg = regular.lastModified();
			long dateZip = gZipped.lastModified();
			
			if  (dateZip >= dateReg) { 
				warning("Both regular and gzip'ed versions of this file exist; will use NEWER one:\n " + fileName + ".gz");
				return fileName + ".gz";  // Use the NEWER file.
			}
			warning(    "Both regular and gzip'ed versions of this file exist; will use NEWER one:\n " + fileName );
			return fileName;
		}
		if (gZipped.exists()) {
			return fileName + ".gz";
		}
		return fileName;
	}
    
    // Allow user names to be overwritten, though that can be dangerous.
    private static void setMyUserName(String newValue) {
    	MYUSERNAME = Matcher.quoteReplacement(newValue);
    	environmentVariableResolutionCache.clear();
    }
    private static void setMyScratchDir(String newValue) {
    	MYSCRATCHDIR = Matcher.quoteReplacement(newValue);
    	environmentVariableResolutionCache.clear();
    }
    
    private static String getMyUserName() {
    	if (MYUSERNAME == null) { setMyUserName(getUserName(true)); } 	// Probably no need for quoteReplacement on MYUSERNAME, but do on all for consistency/simplicity.
    	return MYUSERNAME;
    }
    private static String getMyPathPrefix() {
        return "MYPATHPREFIXisUnset";
    }
    private static String getSharedPathPrefix() {
        return "SHAREDPATHPREFIXisUnset";
    }
	private static String getMyScratchDir() {
    	if (MYSCRATCHDIR == null) { setMyScratchDir(help_getScratchDirForUser()); } // Will get into an infinite loop without the "help_" prefix.
    	return MYSCRATCHDIR;
	}

    /**
     * Waits for input on standard input after displaying "Waiting for user input".
     */
    public static boolean waitHere() {
    	return waitHere("", false, null);
    }
    public static boolean waitHere(String msg) {
    	return waitHere(msg, false, null);
    }
    public static boolean waitHere(String msg, String skipWaitString) {
        return waitHere(msg, false, skipWaitString);
    }
    public static void waitHereErr(String msg) {
    	if ( msg != null && !msg.isEmpty()) {
    		printlnErr(msg);
            waitHere(msg, false, null);
            return;
    	}
        waitHere(msg, false, null);
    }

    /** Prints out the message msg, possibly waiting for user input prior to continuing.
     *
     * waitHere prints out the message msg and then, based on the verbosity setting,
     * possibly waits for user input prior to continuing.
     * <p>
     * If waitHereRegardless is true,this method will always wait for user input.
     * <p>
     * If skipWaitString is non-null,
     * that string will be used to cache the number of times waitHere was called for that
     * specific skipWaitString and subsequent waitHere's will the same skipWaitString will
     * not wait, regardless of the verbosity.
     *
     * @return False if an exception occurs while reading input from the user, true otherwise.
     */
    public static boolean waitHere(String msg, boolean waitHereRegardless, String skipWaitString) {

        int occurenceCount = 1;
        if ( skipWaitString != null ) {
           Integer i = warningCounts.get(skipWaitString);
           if ( i != null ) occurenceCount = i+1;
           warningCounts.put(skipWaitString, occurenceCount);
        }

    	if (!waitHereRegardless && !isWaitHereEnabled() && occurenceCount == 1) {
            if ( msg != null && !msg.isEmpty()) {
                print("\n% Skipping over this 'waitHere': " + msg + "\n", true);
            }
    		return true;
    	}

        if (!waitHereRegardless && occurenceCount > 1) {
            return true;
        }

        // Let's collect these in dribble files.
        warning_println("\nWaitHere:    " + msg);


		boolean hold = doNotPrintToSystemDotOut;
		doNotPrintToSystemDotOut = false; // If these printout become too much, we can add a 3rd flag to override these ...
        print("\n% WaitHere: " + msg + "\n%  ...  Hit ENTER to continue or 'e' to interrupt. ", waitHereRegardless);
        doNotPrintToSystemDotOut = hold;

		if ( CondorUtilities.isCondor() ) {
			error("\nSince this is a condor job, will exit.");
		} else { warning_println("NOTE: Utils.java thinks this job is NOT running under Condor."); }
		
        try {
        	if (inBufferedReader == null) { inBufferedReader = new BufferedReader(new InputStreamReader(System.in)); }
        	String readThis = inBufferedReader.readLine();
        //	println("read: " + readThis);
        	if (readThis != null && readThis.startsWith("e")) { // This had been 'interrupt' instead of 'error' but then these might not be immediately caught, and doing just that is the intent of an 'e' being pressed.
        		try {
        			error("You requested the current run be interrupted by returning something that starts with 'e' (for 'esc' or 'error' or 'elmo' or 'ebola').");
        		} catch (WILLthrownError e) {
        			reportStackTrace(e);
        			println("Hit the Enter key to continue if you wish.");
        			inBufferedReader.readLine();
        		}
        	}
        } catch (IOException e) {
            // Ignore any errors here.
        	inBufferedReader = null;  // If something went wrong, reset the reader. 
        	return false;
        }
        return true; // The main reason for returning values is so that waitHere's can be placed inside conditionals.
    }

    private static void cleanupAndExit() {

        if (dribbleStream != null) {
            dribbleStream.close();
        	compressFile(dribbleFileName);
        }

        if (dribbleStream2 != null) {
            dribbleStream2.close();
        	compressFile(dribbleFileName2);
        }

        if (debugStream != null) {
        	debugStream.close();
        	compressFile(debugFileName);
        }

        if (warningStream != null) {
        	warningStream.close();
        	compressFile(warningFileName);
        }

        if (warningShadowStream != null) {
        	warningShadowStream.close();
        	compressFile(warningShadowFileName);
        }

        System.exit(0);
    }

    /**
     * Prints a warning header on standard output.
     */
    public static void warning() {
        println("\n***** Warning *****\n"); // Don't print to warning stream since no message.
    }
    /** Prints a warning header on standard output that includes the given message.
     *
     * @param str A message describing the warning.
     */
    public static void warning(String str) {
        warning(str, null);
    }
    public static void warning(MessageType type, String str) {
        if ( isMessageTypeEnabled(type) ) warning(str, null);
    }
    /** Prints a warning header on standard output that includes the given message.
     *
     * If skipWarningString is non-null, the warning associated with that string will only be
     * printed the first time the warning occurs.
     */
    public static void warning(String str, String skipWarningString) {

        int occurenceCount = 1;
        if ( skipWarningString != null ) {
           Integer i = warningCounts.get(skipWarningString);
           if ( i != null ) occurenceCount = i+1;
           warningCounts.put(skipWarningString, occurenceCount);
        }

        if ( occurenceCount == 1 ) {
        	warning_println("\nWARNING: " + str);
            println("\n***** Warning: " + str + " *****\n");
        }
    }
    /**
     * Prints a warning header on standard output that includes the given message and waits sleepInSeconds.
     */
    public static void warning(String str, int sleepInSeconds) {
        warning(str, sleepInSeconds, null);
    }
    public static void warning(MessageType type, String str, int sleepInSeconds) {
        if ( isMessageTypeEnabled(type) ) warning(str, sleepInSeconds);
    }

    /**
     * Prints a warning header on standard output that includes the given message and waits sleepInSeconds.
     *
     * If skipWarningString is non-null, the warning associated with that string will only be
     * printed the first time the warning occurs.
     *
     */
    public static void warning(String str, int sleepInSeconds, String skipWarningString) {
        int occurenceCount = 1;
        if ( skipWarningString != null ) {
           Integer i = warningCounts.get(skipWarningString);
           if ( i != null ) occurenceCount = i+1;
           warningCounts.put(skipWarningString, occurenceCount);
        }

        if ( occurenceCount == 1 ) {
            warning_println("\nWARNING: " + str);

            // Make sure we only wait if the user is at a verbosity level where it
            // makes sense to wait.
            if ( isWaitHereEnabled() ) {
                println("\n***** Warning: " + str + " (Waiting " + sleepInSeconds + " seconds.) *****\n");
                sleep(sleepInSeconds);
            } else {
                println("\n***** Warning: " + str + " *****\n");
            }
        }
    }    
    public static void severeWarning(String str) {
        warning_println("\nSEVERE:  " + str);
    	if (isSevereErrorThrowsEnabled()) { error(str); }
    	else { println("\n% ***** Severe Warning: " + str + " *****\n", true); }
    }
    
    private static void sleep(int sleepInSeconds) {
        if (sleepInSeconds > 0) {
            try {
                Thread.sleep(1000 * sleepInSeconds);
            } catch (InterruptedException e) {
                e.getStackTrace();
            }
        }
    }

    /**
     * @return A copy of the given string with the case of the first character
     *         changed (e.g., "xyz" becomes "Xyz").
     */
    public static String changeCaseFirstChar(String old) {
        // Seems String.replace can't be used to simply replace the FIRST occurrence of a char, so brute-force this.
        if (old == null || old.equals("")) {
            return old;
        }
        char    firstChar          = old.charAt(0);
        boolean firstCharLowerCase = Character.isLowerCase(firstChar);
        String oldFirstChar = Character.toString(firstChar);
        String newFirstChar = (firstCharLowerCase ? oldFirstChar.toUpperCase(): oldFirstChar.toLowerCase());
        // old is at least 1 character long, so taking the substring is guaranteed to work
        // If old is only 1 character long 'old.substring(1)' returns the empty string
        return newFirstChar + old.substring(1);
    }

    // This is one place that this class maintains state (so if two threads running, their dribble files will interfere).
    private static String dribbleFileName = null;

    /**
     * Creates a dribble file with the given name in the current working
     * directory.
     *
     * @param fileNameRaw The name of the dribble file.
     */
    public static void createDribbleFile(String fileNameRaw) {

        if (dribbleStream != null) {
            dribbleStream.println("\n\n// Closed by a createDribble call with file = " + fileNameRaw);
        }

    	if (doNotCreateDribbleFiles) { return; }
    	if (!isVerbose()) { return; }
    	closeDribbleFile();
        String fileName = replaceWildCards(fileNameRaw);
        try {
        	ensureDirExists(fileName);
            CondorFileOutputStream outStream = new CondorFileOutputStream(fileName);
            dribbleStream = new PrintStream(outStream, false); // No auto-flush (can slow down code).
            dribbleFileName = fileName;
            println("% Running on host: " + getHostName());
        } catch (FileNotFoundException e) {
        	reportStackTrace(e);
            error("Unable to successfully open this file for writing:\n " + fileName + ".\nError message: " + e.getMessage());
        }
    }

    // This is one place that this class maintains state (so if two threads running, their dribble files will interfere).
    private static String dribbleFileName2 = null;

    private static void closeDribbleFile() {
    	dribbleFileName = null;
    	if (dribbleStream == null) { return; }
    	dribbleStream.close();
    	dribbleStream = null;
    }

    // This is another place that this class maintains state (so if two threads running, their debug files will interfere).
    private static String debugFileName = null;

    // This is another place that this class maintains state (so if two threads running, their debug files will interfere).
    private static String warningFileName = null;

    // Also write warnings to this file (one might go into one directory and the other into a different directory).
    private  static String warningShadowFileName = null;

    private static void warning_println(String str) {
		if (warningStream       != null) { warningStream.println(str);       }
		if (warningShadowStream != null) { warningShadowStream.println(str); }
    }

    /**
     * Sets the seed on the random instance.
     * @param seed The random seed.
     */
    public static void seedRandom(long seed) {
        randomInstance.setSeed(seed);
    }

    /**
     * @return The next random double.
     */
    public static double random() {
        return randomInstance.nextDouble();
    }

    /**
     * @param upper The upper bound on the interval.
     * @return A random number in the interval [1, upper).
     */
    public static int random1toN(int upper) {
        return randomInInterval(1, upper);
    }

    /**
     * @param upper The upper bound on the interval.
     * @return A random number in the interval [0, upper).
     */
    public static int random0toNminus1(int upper) {
        return randomInInterval(0, upper);
    }

    /**
     * @param lower The lower end of the interval.
     * @param upper The upper end of the interval. It is not possible for the
     *              returned random number to equal this number.
     * @return Returns a random integer in the given interval [lower, upper).
     */
    private static int randomInInterval(int lower, int upper) {
        return lower + (int) Math.floor(random() * (upper - lower));
    }

    /**
     * Shorten this list to maxLength by removing elements IN PLACE. Elements
     * are randomly discarded until the list is short enough. If the list is
     * already short enough, it is unchanged.
     * 
     * @param <E>
     *            The element type of the list.
     * @param items
     *            The list.
     * @param maxLength
     *            The maximum length the list should be.
     * @return The given list with maxLength or fewer elements.
     */
    public static <E> List<E> reduceToThisSizeByRandomlyDiscardingItemsInPlace(List<E> items, int maxLength) {
    	if (items == null) { return null; }
        int size = items.size();
        if (size <= maxLength) { return items; }

        int numberToDiscard = size - maxLength;
        for (int i = 0; i < numberToDiscard; i++) {
            int index = randomInInterval(0, size);
            items.remove(index);
            size--;
        }
        return items; // Probably no need to return this, since caller knows, but might as well do so (for one thing, this allows the caller to use a functional programming style).
    }

    /**
     * Variant of getIthItemInCollection() that works with any collection.
     */
    public static <E> E getIthItemInCollectionUnsafe(Collection<E> items, int index) {
    	int counter = 0;
        // Need to do the next() else will not advance in the iterator.
        for (E next : items) {
            if (counter++ == index) {
                return next;
            }
        }
		error("Could not find the " + index + "th item in a collection of size " + items.size());
		return null;
    }

    /**
     * Randomly select a number of items from this list.
     * 
     * @param <E> The element type of the list.
     * @param numberToChoose How many elements to return.
     * @param list The list of elements to choose from.
     * @return A new list containing the specified number of elements from the
     *         given list, or the original list if it was shorter than
     *         numberToChoose.
     * @see Utils#chooseRandomNfromThisList(int, List, boolean)
     */
    public static <E> List<E> chooseRandomNfromThisList(int numberToChoose, List<E> list) {
        return chooseRandomNfromThisList(numberToChoose, list, false);
    }

    /**
     * Randomly select a number of items from this list. If
     * maintainOrdering=true, the order in the original list will be preserved
     * (possibly at a runtime cost).
     * 
     * @param <E> The element type of the list.
     * @param numberToChoose How many elements to return.
     * @param list The list of elements to choose from.
     * @param maintainOrdering Whether the order of the list is maintained.
     * @return A new list containing the specified number of elements from the
     *         given list, or the original list if it was shorter than
     *         numberToChoose.
     */
    private static <E> List<E> chooseRandomNfromThisList(int numberToChoose, List<E> list, boolean maintainOrdering) {
        if (list == null || numberToChoose < 0) { return null; }
        int length = list.size();

        if (numberToChoose >= length) { return list; }

        List<E> result = new ArrayList<>(numberToChoose);
        if (numberToChoose == 0) {  return result; }

        if (!maintainOrdering && numberToChoose < length / 4) { // We'll collect items if only a few.
            int counter = 0;
            while (counter < numberToChoose) {
                int itemToKeep = random0toNminus1(length);
                E selectedItem = list.get(itemToKeep);
                if (!result.contains(selectedItem)) {
                    result.add(selectedItem);
                    counter++;
                }
            }
        } else { // Otherwise we'll copy list then randomly discard items.  Notice there the ORDER of the list is unchanged (which is why the first version can be overridden).
            result.addAll(list); // Copy the list.
            int counter = length;
            while (counter > numberToChoose) { // Could be a FOR loop, but mirror what is done above.
                int itemToDiscard = random0toNminus1(counter);
                result.remove(itemToDiscard);
                counter--;
            }

        }
        return result;
    }

    /**
     * @param d A number (double).
     * @return Whether the given double is a number (not not a number). (Note
     *         that by this definition infinity is included as a number.)
     */
    public static boolean isaNumber(double d) {
        return !Double.isNaN(d);
    }

    /**
     * Compares two numbers to see if they are different.
     * 
     * @param a A number.
     * @param b A number.
     * @return True if the two given numbers differ by more than a certain
     *         tolerance.
     * @see #EQUIVALENCE_TOLERANCE
     */
    private static boolean diffDoubles(double a, double b, double tolerance, double toleranceSmallNumbers) {
    	double  diff        = Math.abs(a - b);
        boolean firstResult = diff > tolerance;
        if (firstResult) { return true; }
        // See if we're dealing with small numbers.
        if (a > -1 && a < 1 && b > -1 && b < 1) {
        	return diff > toleranceSmallNumbers;
        }
        return false;
    }
    public static boolean diffDoubles(double a, double b) {
    	return diffDoubles(a, b, EQUIVALENCE_TOLERANCE, EQUIVALENCE_TOLERANCE_SMALL_NUMBERS);
    }

    /**
     * Formats the given floating point number by truncating it to one decimal
     * place.
     * 
     * @param d A number.
     * @return A string containing the given number formatted to one decimal place.
     */
    public static String truncate(double d) {
        return truncate(d, 1);
    }

    /**
     * Format the given floating point number by truncating it to the specified
     * number of decimal places.
     * 
     * @param d
     *            A number.
     * @param decimals
     *            How many decimal places the number should have when displayed.
     * @return A string containing the given number formatted to the specified
     *         number of decimal places.
     */
    public static String truncate(double d, int decimals) {
    	double abs = Math.abs(d);
    	if (abs > 1e13)             { 
    		return String.format("%."  + (decimals + 4) + "g", d);
    	} else if (abs > 0 && abs < Math.pow(10, -decimals))  { 
    		return String.format("%."  +  decimals      + "g", d);
    	}
        return     String.format("%,." +  decimals      + "f", d);
    }

    /**
     * Truncates a double and returns it as a string with at least one and at
     * most "decimals" decimal places. Notice that this does not ROUND (i.e, if
     * the first of the dropped digits was '5' or higher, could add 1 to the
     * last digit returned .. One complication of trying to implement rounding
     * is that one needs to deal with "carrying" (eg, 0.99995 becoming 1.0000).
     * Might want to check out to see if Java now handles this better, say in
     * NumberFormat or Formatter. If requested, puts space in front of positive
     * numbers - so printouts align.
     * 
     * @param d A number.
     * @param decimals The number of decimal places in the string version.
     * @param addSpaceBeforePosNumbers Whether to add space before positive numbers (so they are in alignment with the '-' sign before negative numbers).
     * @return A string containing the number formatted as described above.
     */
    public static String truncate(double d, int decimals, boolean addSpaceBeforePosNumbers) { // This should always produce at least one decimal (by official documentation some years ago).
        String str = String.format("$,d", d);
        int index = str.indexOf(".");

        // Patch for the above bug.  (Doesn't add "decimals" 0's, but that's ok.)
        if (index < 0)  return str.concat(".0");

        int indexE = indexOfIgnoreCase(str, index);
        if (indexE > 0) // In scientific notation.
        {
            String result = str.substring(0, Math.min(indexE, index + decimals + 1)) + "e" + Integer.valueOf(str.substring(indexE + 1));

            if (d < 0 || !addSpaceBeforePosNumbers)
                return result;
            else
                return " " + result;
        }
        final String substring = str.substring(0, Math.min(str.length(), index + decimals + 1));
        if (d < 0 || !addSpaceBeforePosNumbers)
            return substring;
        else
            return " " + substring;
    }

    /**
     * A version of java.lang.String.indexOf(String, int) that ignores case.
     * (Since there isn't an CASELESS indexOf, adapt the existing code.)
     * 
     * @param str The string to search.
     * @param fromIndex The index to start at.
     * @return The index of the start of query, or -1 if the query was not
     *         found.
     */
    private static int indexOfIgnoreCase(String str, int fromIndex) {
        int qlength = "e".length();
        int max = (str.length() - qlength);

        test: for (int i = (Math.max(fromIndex, 0)); i <= max; i++) {
            int k = 0, j = i, n = qlength;
            char schar, qchar;
            while (n-- > 0) {
                schar = str.charAt(j++);
                qchar = "e".charAt(k++);
                if ((schar != qchar)
                        && (Character.toLowerCase(schar) != Character.toLowerCase(qchar)))
                    continue test;
            }
            return i;
        }
        return -1;
    }

    /**
     * Create the cross product of a list of list. I.e., { {a,b}, {c, d} -&gt; {
     * {a,c}, {a,d}, {b,c}, {b,d} }. Since this is general-purpose utility, it
     * has been placed here. If this causes memory-usage problems, convert to an
     * iterative version.
     * 
     * @param <E> The element type of the inner lists.
     * @param allArgPossibilities A list of lists containing the elements for the cross product.
     * @param maximumSize The maximum size of the result. Items will be randomly deleted.
     * @return A list containing the cross product of the given lists.
     */
    public static <E> List<List<E>> computeCrossProduct(List<? extends Collection<E>> allArgPossibilities, int maximumSize) {
	    // NOTE: do not use Set<List<E>> since DUPLICATES will be removed.
	    // Here are some calculations for reducing the size of the cross-product set "as we go" (rather than during post-processing).
	    //   Li is the number of items that are expected to be produced after set i is recursively merged in.
	    //   L1 = maximumSize
	    //   Pi is the probability that an item in set i is added.
	    // 		L1 = P1 x S1 x L2 // L2 is the reduced set that comes from the first recursive call.
	    // 		L2 = P2 x S2 x L3 // L3                                        second
	    // 		...
	    // 		Ln = Pn x Sn      // The bottoming-out of the recursion.
	    //   After some algebra:
	    // 		P1 x P2 x ... x Pn = L1 / (S1 x S2 x ... Sn)
	    // 	 If we let Pi = Q / Si, where Q is the Nth root of L1, then we get what we want.
	    //	Note: we ignore SINGLETON sets in the calculation (i.e., of 'n'), since they don't impact size.
    	if (maximumSize < 1) { return null; }
    	double Q = -1.0;
        if (maximumSize < Integer.MAX_VALUE) {
        	int size    = 1; 
			int counter = 0;
			for (Collection<E> possibilities : allArgPossibilities) {
				size *= possibilities.size();
				if (possibilities.size() > 1) { counter++; }
			}
			if (size > maximumSize) { Q = Math.pow(maximumSize, 1.0/counter); }
        }
    	return computeCrossProduct(allArgPossibilities, Q);
    }
    /**
     * See computeCrossProduct(List<Collection<E>> allArgPossibilities, int maximumSize)
     * In this version, maximumSize defaults to infinity.
     */
    public  static <E> List<List<E>> computeCrossProduct(List<? extends Collection<E>> allArgPossibilities) {
    	return computeCrossProduct(allArgPossibilities, Integer.MAX_VALUE);
    }
    private static <E> List<List<E>> computeCrossProduct(List<? extends Collection<E>> allArgPossibilities, double Q) {
        if (allArgPossibilities == null) { return null; }
        int length = allArgPossibilities.size();
        if (length < 1) { return null; }
        List<List<E>> allArgPossibilitiesForRest = null;
        Collection<E> firstCollection = allArgPossibilities.get(0);

        int sizeOfFirstCollection = firstCollection.size();

        if (length > 1) {
            //  Of the results of the recursion, about probOfRandomlyDiscarding * sizeOfFirstList
            allArgPossibilitiesForRest = computeCrossProduct(allArgPossibilities.subList(1, length), Q);
        }
        List<List<E>> results = new ArrayList<>(4);
        double prob =  Q / sizeOfFirstCollection;

        // For each choice for the first argument, ...
        for (E term : firstCollection) {
            if (allArgPossibilitiesForRest != null) {
                // ... combine with each possible choice for the rest of the args.
                for (List<E> restArgs : allArgPossibilitiesForRest) {
                	List<E> args = new ArrayList<>(1 + restArgs.size());
                    args.add(term);
                    args.addAll(restArgs);
                    if (Q < 0.0 || sizeOfFirstCollection <= 1 || random() < prob) { results.add(args); }
                }
            } else {
                // No choices for the rest of the list, so wrap each choice for the first of the list (could save some new'ing if the first list is of length one, but that would make this code more complicated).
            	List<E> args = new ArrayList<>(1);
                args.add(term);
                results.add(args);
            }
        }
        return results;
    }
    
    // This is specific to MLNs.  Determine the weight that a single MLN clause should have it it is to produce this probability.
	public static double getLogWeightForProb(double prob) {
		double maxClauseWeight = Sentence.maxWeight;
		if (prob == 0) {
			return -maxClauseWeight;
		}
		if (prob == 1) {
			return maxClauseWeight;
		}
		double logWt = Math.log(prob/(1-prob));
		if (logWt > maxClauseWeight) {
			return maxClauseWeight;
		}
        return Math.max(logWt, -maxClauseWeight);
	}
    /**
     * Write these objects to this file. Start with a header string (e.g., a
     * comment) and have all lines (except the header) ends with finalEOLchars.
     * 
     * @param fileName A string containing the name of the file to use for output.
     * @param objects The objects to write to the named file.
     * @param finalEOLchars A string appended to the end of each line, but before the newline.
     * @param headerStringToPrint A description for the beginning of the file.
     */
    public static void writeObjectsToFile(String fileName, Collection<?> objects,
            							  String finalEOLchars, String headerStringToPrint) { // If object is a number, need an extra space so the period doesn't look like a decimal point.
        try {
        	ensureDirExists(fileName);
            CondorFileOutputStream outStream = new CondorFileOutputStream(fileName);
            PrintStream      stream    = new PrintStream(outStream);
            if (headerStringToPrint != null) {
                stream.println(headerStringToPrint);
            }
            int counter = 0;
            int total   = objects.size();
            for (Object obj : objects) { // If speed is an issue, could first check for COUNT and FRACTION in finalEOLchars.
            	counter++;
                stream.println(obj.toString() + finalEOLchars.replace("COUNT", comma(counter) + "").replace("FRACTION", Utils.truncate((1.0 * counter) / total, 6)));
            }
            stream.close();
        } catch (FileNotFoundException e) {
        	reportStackTrace(e);
            error("Unable to successfully open this file for writing: " + fileName + ".  Error message: " + e.getMessage());
        }
        
    }    

	/**
	 * Reads file <filePath> into a string.
	 * 
	 * Works for gzipped files as well.  
	 * 
	 * @return  file as a string
	 * 
	 * This code taken directly from http://snippets.dzone.com/posts/show/1335
	 * (andrewspencer post on July 21, 2010)
	 */
	private static String readFileAsString(String fileNameRaw) throws IOException {
		String fileName = replaceWildCards(fileNameRaw);
		if (fileName.endsWith(".gz")) { // BUGGY if caller asks for *.gz file but really wanted the newer one if both * and *.gz exist.
			return readFromGzippedFile(fileName);
		} else if (fileExists(fileName + ".gz")) {
			if (!fileExists(fileName)) {
				return readFromGzippedFile(fileName + ".gz");
			}
			File regular = new CondorFile(fileName);
			File gZipped = new CondorFile(fileName + ".gz");
			boolean regExists = regular.exists();
			boolean zipExists = gZipped.exists();
			if (regExists && zipExists) {
				long dateReg = regular.lastModified();
				long dateZip = gZipped.lastModified();
				
				if  (dateZip >= dateReg) { 
					warning("Both regular and gzip'ed versions of this file exist; will read NEWER one:\n " + fileName + ".gz");
					return readFromGzippedFile(fileName + ".gz");  // Use the NEWER file.
				}
				warning("Both regular and gzip'ed versions of this file exist; will read NEWER one:\n " + fileName);
				return readFileAsString(new CondorFile(fileName));
			}
		}
	    return readFileAsString(new CondorFile(fileName));
	}

	private static String readFileAsString(File file) throws IOException {
	    byte[] buffer = new byte[(int) file.length()];
	    BufferedInputStream f = null;
	    try {
	        f = new BufferedInputStream(new FileInputStream(file));
	        f.read(buffer);
	    } finally {
	        if (f != null) try { f.close(); } catch (IOException ignored) { }
	    }
	    return new String(buffer);
	}

    public static void writeStringToFile(String stringToPrint, File file) {
        try {
        	ensureDirExists(file);
            CondorFileOutputStream outStream = new CondorFileOutputStream(file);
            PrintStream               stream = new PrintStream(outStream);
            stream.println(stringToPrint);
            stream.close();
        } catch (FileNotFoundException e) {
        	reportStackTrace(e);
            // TODO replace this error with an exception
            error("Unable to successfully open this file for writing:\n " + file.getName() + ".\nError message:\n " + e.getMessage());
        }
    }  
    public static void touchFile(String fileName) {
    	touchFile(ensureDirExists(fileName));
    }

    private static void touchFile(File file) {
    	ensureDirExists(file);
        // Seems unnecessar
    	if (isDevelopmentRun()) { appendString(file, "\n// Touched at " + getDateTime() + ".\n", false); }
    }

	public static String setFirstCharToRequestedCase(String str, boolean uppercaseFirstChar) {
		String result = str;

        if (str != null) {
            if (str.length() == 1) {
                char f = str.charAt(0);
                if (Character.isLetter(f) && Character.isUpperCase(f) != uppercaseFirstChar) {
                    if (uppercaseFirstChar) {
                        result = str.toUpperCase();
                    } else {
                        result = str.toLowerCase();
                    }
                }
            }
            else if (str.length() > 1) {
                char f = str.charAt(0);
                if (Character.isLetter(f) && Character.isUpperCase(f) != uppercaseFirstChar) {
                    String firstLetter;
                    if (uppercaseFirstChar) {
                        firstLetter = str.substring(0, 1).toUpperCase();
                    } else {
                        firstLetter = str.substring(0, 1).toLowerCase();
                    }
                    String rest = str.substring(1);
                    result = firstLetter + rest;
                }
            }
        }
        return result;
	}

	public static boolean isaInteger(String string) {
		try {
			Integer.parseInt(string);
			return true;
		} catch (NumberFormatException e) { return false; }
	}

   /** Returns a pretty String starting with prefix, ending with suffix, and contain a comma separated list of the collection items.
    *
    * @param <T> Type of the collection. Any object will do.
    * @param prefix Can be null if no prefix is wanted.
    * @param suffix Can be null if no suffix is wanted.
    * @param items Items to print.  Uses item.toString() to print each.
    * @return String in the form "&ltprefix>&gt[s]&ltitem>&gt[, &ltitem&gt ... ][ and &ltitem&gt ] &ltsuffix&gt".
    */
    public static <T> String getPrettyString(String prefix, String suffix, Collection<T> items) {
        StringBuilder sb = new StringBuilder();

        if (prefix != null) {
            sb.append(prefix);
        }

        else if (items.size() == 1) {
            sb.append(items.iterator().next());
        }
        else {
            // Slide in an s if the prefix doesn't end in a space.
            // This assume a certain gramatical form, which may be wrong,
            // but oh well...

            int count = 0;
            for (T item : items) {
                if (count > 0 ) {
                    if (count == items.size() - 1) {
                        if ( items.size() > 2) {
                            sb.append(",");
                        }
                        sb.append(" and ");
                    }
                    else {
                        sb.append(", ");
                    }
                }
                sb.append(item);
                count++;
            }
        }
        if (suffix != null && !suffix.startsWith(" ")) {
            sb.append(" ");
        }
        if (suffix != null) {
            sb.append(suffix);
        }

        return sb.toString();
    }

    /** Returns the maximum of a list of doubles */
    public static double max(double ... values) {
        double max = Double.NEGATIVE_INFINITY;

        if ( values != null ) {
            for (double value : values) {
                if (value > max) {
                    max = value;
                }
            }
        }

        return max;
    }

    /** Returns the maximum of a list of object based on a comparitor.
     *
     * @param <T> Type of object to be compared.
     * @param comparator Comparator to use for the comparison.
     * @param objects Objects to compare.
     * @return Returns the object with the highest rank according to the comparator.
     * If multiple object have the same rank, the earliest on in the list will be
     * returned.
     */
    public static <T> T argmax(Comparator<T> comparator, T ... objects) {
        T max = null;

        if ( objects != null ) {
            for (T object : objects) {
                if (object != null && (max == null || comparator.compare(object, max) > 0)) {
                    max = object;
                }
            }
        }

        return max;
    }

    public static double getPrecision(double truePositives, double falsePositives) {

        double denominator = truePositives + falsePositives;

        if ( denominator > 0 ) {
            return truePositives / denominator;
        }
        else {
            return Double.NaN;
        }
    }

    public static double getRecall(double truePositives, double falseNegatives) {

        double denominator = truePositives + falseNegatives;

        if ( denominator > 0 ) {
            return truePositives / denominator;
        }
        else {
            return Double.NaN;
        }
    }

    public static double getFBeta(double beta, double truePositives, double falsePositives, double falseNegatives) {

        double p = getPrecision(truePositives, falsePositives);
        double r = getRecall(truePositives, falseNegatives);

        return getFBeta(beta,p,r);
    }

    private static double getFBeta(double beta, double precision, double recall) {

        if ( Double.isNaN(precision) || Double.isNaN(recall) ) {
           return Double.NaN;
        } else {
           return (1 + beta * beta) * precision * recall / ( beta * precision + recall);
        }
    }

    public static double getF1(double truePositives, double falsePositives, double falseNegatives) {
        return getFBeta(1, truePositives, falsePositives, falseNegatives);
    }

   public static double getF1(double precision, double recall) {
       return getFBeta(1, precision, recall);
   }

    public static double getAccuracy(double truePositives, double falsePositives, double trueNegatives, double falseNegatives) {

        double numerator   = truePositives                  + trueNegatives;
        double denominator = truePositives + falsePositives + trueNegatives + falseNegatives;

        if ( denominator > 0 ) {
            return numerator / denominator;
        }
        else {
            return Double.NaN;
        }
    }

    private static final Pattern numberPattern = Pattern.compile("-?[0-9]+(\\.[0-9]+)?([eE]-?[0-9]+)?");

    /**
    * Replace all problematic characters with underscores.
    * @param string  The string to convert. 
    * */
    private static String changeMarkedCharsToUnderscores(String string) {
		if (string == null) { return null; }

        StringBuilder sb = null;
        int length = string.length();
        boolean nonDigitFound = false;
        for(int index = 0; index < length; index++) {

            char c = string.charAt(index);
            if (!nonDigitFound) { nonDigitFound = Character.isLetter(c); } // BUGGY if scientific notation.
            if (Character.isWhitespace(c) || c == '=') { nonDigitFound = false; }

            switch(c) {
            	case '.': // JWS: we want this to persist (to handle doubles).  BUGGY on a string like "123.4abc"
            		if ( !nonDigitFound &&
            			 index    > 0      && Character.isDigit(string.charAt(index - 1)) && 
            			(index+1) < length && Character.isDigit(string.charAt(index + 1))) {
            			break;
            		}
            	case '-':
            		if (index == 0) { break; } // Leading minus sign OK.
            		if (index > 1 && index < length - 2 && Character.isDigit(string.charAt(index - 2)) &&
            			(string.charAt(index - 1) == 'E' || string.charAt(index - 1) == 'e') &&
            			Character.isDigit(string.charAt(index + 1))) {
            			// Looks like scientific notation.
            			break;
            		}
                case '?':
                case '!':
                case '#':
                case '$':
                case '%':
                case '&':
                case '(':
                case ')':
                case '{':
                case '}':
                case '[':
                case ']':
                case '|':
                case '*':
                case '+':
                case ',':
                case '/':
                case ':':
                case ';':
                case '<':
                case '=':
                case '>':
                case '@':
                case '^':
                case '`':
                case '~':
                case ' ':
                case '"':
                case '\t':
                case '\'':
                case '\\':
                    if ( sb == null ) {
                        sb = new StringBuilder(string);
                    }
                    sb.setCharAt(index, '_');
                    if (!nonDigitFound) { nonDigitFound = ((c != '-') && (c != '+')); }
                    break;
                default:
                    break;
            }
        }

        return sb == null ? string : sb.toString();
    }
    private static String cleanString(String str, HandleFOPCstrings stringHandler) {
    	return cleanString(str, stringHandler, false);
    }
	public static String cleanString(String str, HandleFOPCstrings stringHandler, boolean hadQuotesOriginally) { // TODO - do a better job when there is a leading '-' (ie, it might not be a minus sign).
		if (str == null || str.isEmpty() || str.charAt(0) == '-') { return str; } // An exception to this rule.  The last disjunct (too crudely?) tests for negative numbers.
        if ( numberPattern.matcher(str).matches()) return str;
		String trimmed = str.trim();
		if (stringHandler != null && stringHandler.doVariablesStartWithQuestionMarks() 
				&& trimmed.length() > 1 // This line added by caden, internal block assumes length of at least 2
				&& trimmed.charAt(0) == '?') {
			String subStr = trimmed.substring(1);
			if (subStr.length() > 0 && subStr.charAt(0) == '?') { // Had multiple question marks (which DO mean something in IL but we are not exploiting that).
				return cleanString(subStr, stringHandler);
			}
			return "?" + cleanString(trimmed.substring(1), stringHandler);
		}
		String result = (hadQuotesOriginally ? str : changeMarkedCharsToUnderscores(str.trim()));
		if (!hadQuotesOriginally && result != null && result.length() > 0 && result.charAt(0) == '_') {
			// waitHere("Starts with underscore: '" + str + "' -> '" + result + "'.");
			if (stringHandler.usingStdLogicNotation()) {
				result = "U" + result;
			} else {
				result = "u" + result;  // Leading underscores have special semantics, so don't let them survive cleaning.
			}
		}
		return result;
	}

	public static String createSafeStringConstantForWILL(String string, HandleFOPCstrings stringHandler) {
		if (string == null)    { return null;   }
		if (string.equals("")) { return string; }
		
		if (stringHandler.doVariablesStartWithQuestionMarks()) {
			if (string.charAt(0) == '?') {
				return createSafeStringConstantForWILL("qm_" + string.substring(1), stringHandler); // Get rid of any leading question mark in a constant.
			}
			return cleanString(string, stringHandler);
		}
		
		String result = cleanString(string, stringHandler);

		if (!Character.isLetter(result.charAt(0))) {
            // This will also handle a leading underscore, which indicates (in all notations) a variable.
		    result = "c_" + result;
		} else {
		    result = changeCaseFirstChar(result);
        }

        // Make these canonical.
        // TODO(?): allow an override?
        return stringHandler.getStringConstant(result).getName();
	}

    private static String getUserHomeDir() {
	   return System.getProperty("user.home");
	}

    public static String getUserName() {
        return getUserName(false);
    }

    private static String getUserName(boolean makeSafeString) {
        String result = System.getProperty("user.name");
        if (!makeSafeString) { return cleanString(result, null); }
        return result;
    }

    private static String help_getScratchDirForUser() {
        // Don't call ensureDirExists() or CondorFile() from here or will get an infinite loop.

        // Note: this will fail for any Condor jobs that flock.

    	String userName = getUserName();
    	if ("shavlik".equals(userName) || "tkhot".equals(userName) || "siddharth".equals(userName)) {
    		String dir = "";
    		if      (isRunningWindows()) {
                // Be sure to end with '\\' (or '/' for Linux).  Use Linux notation since sometimes backslashes disappear as strings get pushed through many methods.
    			dir = "C:/WILLscratch/"; }
    		else if (isRunningLinux())   {
    			// tkhot runs out of space on 15K docs so using shavlikgroup
    			if ("tkhot".equals(userName)) {
    				dir = "/u/shavlikgroup/people/Tushar/WILLscratch/";
    			} else {
                    // Had been (8/11) "/scratch/" but dont want these to be on every machine (sometimes didn't have 'write' privileges in Condor).
    				dir = "/u/" + userName + "/WILLscratch/";
    			}
    		} else {
        		error("Unclear which OS '" + userName + "' is running.");  
    		}
    		try {
    			File f = new File(dir);
                // If we have problems here, rewrite to use /u/userName if /scratch doesn't exist - but maybe scratch always exists?
    			f.mkdirs();
    		} catch (Exception e) {
    			dir = "/u/" + userName + "/WILLscratch/";
    			File f = new File(dir);
    			f.mkdirs();
    		}
    		if ((new File(dir)).exists()) { return dir; }
    		waitHere("Cannot create a scratch dir for: " + userName);
    		return dir;
    	}
    	error("getScratchDirForWisconsinUser has encountered an unknown user name: " + userName);
    	return null;
    }

	public static boolean isRunningWindows() {
        return System.getProperty("os.name").toLowerCase().contains("windows");
    }
	
	private static boolean isRunningLinux() {
        return System.getProperty("os.name").toLowerCase().contains("linux");
    }
	
	public static Boolean fileExists(String fileName) {
		return ((new CondorFile(fileName)).exists());
	}

    /**
     * Copy content of file f1 into file f2
     */
    // Found at: http://www.computer-faqs.com/2009/01/30/how-to-copy-text-file-in-java/
    public static void copyFile(File f1, File f2) {
    	if (f1.getName().endsWith(".gz")) { waitHere("Use copyCompressedFile for " + f1.getName()); }
    	if (f2.getName().endsWith(".gz")) { waitHere("Use copyCompressedFile for " + f2.getName()); }
    	try {
    		ensureDirExists(f1);
    		ensureDirExists(f2);
            CondorFileReader reader = new CondorFileReader(f1);
            CondorFileWriter writer = new CondorFileWriter(f2, false); // Create a new file.
            int line;
            while ((line = reader.read()) != -1) {  // Read line from text file and write to destination file
                writer.write(line);
            }
            reader.close();
            writer.close();
        } catch (FileNotFoundException ffx) {
        	reportStackTrace(ffx);
            error("FileNotFoundException: " + ffx);
        } catch (IOException iox) {
        	reportStackTrace(iox);
            error("IOException: " + iox);
        }
    }
    
    public static void appendString(File file, String str) {
    	appendString(file, str, true);
    }

    public static void appendString(File file, String str, boolean useLock) {
        if (str != null && !str.isEmpty()) {
    		ensureDirExists(file);
            CondorFileWriter writer = null;
            boolean lockObtained = false;
            try { // Open the file.
                lockObtained = !useLock || obtainLock(file);

                writer = new CondorFileWriter(file, true);
                writer.append(str);
                if (!str.endsWith("\n")) {
                    writer.append("\n");
                }

            } catch (IOException e) {
            	reportStackTrace(e);
                error(e.toString());
            } finally {
                if (writer != null) {
                    try {
                        writer.close();
                    } catch (IOException ignored) {
                    }
                }

                if (lockObtained && useLock) {
                    releaseLock(file);
                }
            }
        }
    }

    public static boolean obtainLock(File fileToLock) throws IOException {
		ensureDirExists(fileToLock);
        File lockFile = new CondorFile(fileToLock.getParentFile(), "." + fileToLock.getName() + ".lock");

        long wait = 0; // Since starting at 1 second might be too long, start at 0 and add 1 after multiplying by 1000.
        while( !lockFile.createNewFile() ) {
        	long waitToUse = wait * 1000 + 1;
        	// Use this one so that the info on locking appears even when filtering (eg, via grep) the output.
            // TODO(?): do we care this isn't in the dribble file? In case we might, print twice.
            System.err.println("Lock file " + lockFile + " already exists.  Waiting " + convertMillisecondsToTimeSpan(waitToUse) + " to obtain lock.");
            println(           "Lock file " + lockFile + " already exists.  Waiting " + convertMillisecondsToTimeSpan(waitToUse) + " to obtain lock.");
        	try {
                Thread.sleep(waitToUse);
            } catch (InterruptedException ignored) {
            }
            wait = Math.min(55 + random1toN(11), Math.max(1, 2 * wait)); // Never wait more than 60 seconds, but add some randomness in case two waits are in synch.
        }
        return true;
    }

    public static void releaseLock(File fileToLock) {
        File lockFile = new CondorFile(fileToLock.getParentFile(), "." + fileToLock.getName() + ".lock");
        ensureDirExists(lockFile);
        if (!lockFile.delete()) { error("Could not delete: " + lockFile); }
    }

    // OK if this is global because we're simply making and never deleting directories (unless the user does so manually).
    private static Set<String> ensured = new HashSet<>(4);
    public static File ensureDirExists(File file) {
    	if (file == null) { return null; }
    	return ensureDirExists(file.getAbsolutePath());
    }
    public static File ensureDirExists(String file) {
    	if (file == null) { return null; }
    	if (file.endsWith("/") || file.endsWith("\\")) { file += "dummy.txt"; } // A hack to deal with directories being passed in.
		File f = new CondorFile(file);

    	String parentName = f.getParent();
    	File   parentDir  = (parentName == null ? null : f.getParentFile());
		if (parentDir != null && !ensured.contains(parentName) && !parentDir.exists()) { 
			if (!parentDir.mkdirs()) { // Be careful to not make the file into a directory.
				waitHere("Unable to create (sometimes these are intermittent; will try again)\n   file      = " + file +
																						    "\n   parentDir = " + parentDir);
				parentDir.mkdirs();
			}
			ensured.add(parentName); 
		}
		return f;
	}

	public static String getDateTime() {
        DateFormat dateFormat = new SimpleDateFormat("H:mm:ss M/d/yy"); //"yyyy/MM/dd HH:mm:ss"
        Date       date       = new Date();
        return dateFormat.format(date);
    }
	
	private static final long millisecInMinute = 60000;
	private static final long millisecInHour   = 60 * millisecInMinute;
	private static final long millisecInDay    = 24 * millisecInHour;
	public static String convertMillisecondsToTimeSpan(long millisec) {
		return convertMillisecondsToTimeSpan(millisec, 0);
	}
	public static String convertMillisecondsToTimeSpan(long millisec, int digits) {
		if (millisec ==    0) { return "0 seconds"; } // Handle these cases this way rather than saying "0 milliseconds."
		if (millisec <  1000) { return comma(millisec) + " milliseconds"; } // Or just comment out these two lines?
		if (millisec > millisecInDay)    { return comma(millisec / millisecInDay)    + " days and "    + convertMillisecondsToTimeSpan(millisec % millisecInDay,    digits); }
		if (millisec > millisecInHour)   { return comma(millisec / millisecInHour)   + " hours and "   + convertMillisecondsToTimeSpan(millisec % millisecInHour,   digits); }
		if (millisec > millisecInMinute) { return comma(millisec / millisecInMinute) + " minutes and " + convertMillisecondsToTimeSpan(millisec % millisecInMinute, digits); }
		
		return truncate(millisec / 1000.0, digits) + " seconds"; 
	}
	
	private static String getHostName() { // Written largely by Trevor.
		try {
			InetAddress addr = InetAddress.getLocalHost();
			String hostName = addr.getHostName();
			if (hostName == null) { return "unknownHost"; }
			int locFirstPeriod = hostName.indexOf('.');
			if (locFirstPeriod > 0) { // Not sure what a leading period would be, but keep it if this case ever occurs.
				return hostName.substring(0, locFirstPeriod);
			}
			return hostName;
		} catch (UnknownHostException e) {
			return "unknownHost";
		}
    }
	
	private static final Runtime sys_runtime = Runtime.getRuntime();
	public static String reportSystemInfo() {
		sys_runtime.gc();
		long   memoryInUse = sys_runtime.totalMemory() - sys_runtime.freeMemory();
		
		return "Using " + comma(memoryInUse) + " memory cells.";
	}

    /**
	 * Recursive remove an existing directory.
     */
    public static boolean delete(File file) { // Also see deleteDirectory [I think I (JWS) wrote deleteDirectory and Trevor wrote this one.]
        if (file.isDirectory()) {
            File[] files = file.listFiles();
            for (File file1 : files) {
                if (!delete(file1)) {
                    return false;
                }
            }
        }
        return file.delete();
    }

   public static boolean delete(String fileName) {
	   return delete(new CondorFile(fileName));
   }

    public static boolean isDevelopmentRun() {
        if ( developmentRun == null ) {
            setupVerbosity();
        }

        return developmentRun;
    }

    private static boolean isSevereErrorThrowsEnabled() {
        if ( severeErrorThrowsEnabled == null ) {
            setupVerbosity();
        }

        return severeErrorThrowsEnabled;
    }

    private static boolean isVerbose() {
        if ( verbose == null ) {
            setupVerbosity();
        }

        return verbose;
    }

    private static boolean isWaitHereEnabled() {
        if ( waitHereEnabled == null ) {
            setupVerbosity();
        }

        return waitHereEnabled;
    }

    public static boolean isVerbositySet() {
        return verbose != null;
    }

    /** Return whether the properties indicate that we are a developer.
     *
	 * Here is some code to decide whether a run is a development run based first on Java system properties
	 * and then on the presence of a file. The system property is important because it allows more flexibility,
	 * e.g. a particular run can be specified as a development run from the command line, from a Maven run,
	 * from your Eclipse run configuration, etc.
     * <P>
     * Try to use the other isXXX settings to control what you print or do.  That will allow for
     * finer grain control by the end user.
	 */
    private static boolean checkDevelopmentProperties() {

		// Find out if this is a development run.  Err on the side of answering no.

		// If a system property is already defined with a value, use that value.
		// Otherwise, populate the system property by looking for a file.
		String value = System.getProperty(DEVELOPER_MACHINE_PROPERTY_KEY);

		if (value != null) {
		    return value.equalsIgnoreCase("true");
		}
		// Decide whether this is a development run based on the presence of a file in the user's home directory
		String userHomeDirectory  = getUserHomeDir();
		ensureDirExists(userHomeDirectory);
		File   developmentRunFile = new CondorFile(userHomeDirectory, DEVELOPER_MACHINE_FILE_NAME);
		boolean result = developmentRunFile.exists();

		if (result) {
			// Set the system property as well (canonicalize if already set)
			System.setProperty(DEVELOPER_MACHINE_PROPERTY_KEY, Boolean.toString(result));
		}
		return result;
    }

    private static void setupVerbosity() {
        if ( checkDevelopmentProperties() ) {
            setVerbosity(Verbosity.Developer);
        }
        else {
            setVerbosity(Verbosity.Medium);
        }
    }
    
	public static void reportStackTrace(Throwable e) {
		if (isDevelopmentRun()) {
			flush();
			StackTraceElement[] trace = e.getStackTrace();
			int traceSize = trace.length;
			int sizeToUse = Math.min(traceSize, 50); // <-------- change this if you need to see more of the stack.
			println("\n% Stack trace:");
			if (sizeToUse < traceSize) {
				for (int i = 0; i < sizeToUse / 2; i++) {
					println("%  Element #" + (traceSize - i) + ": " + trace[i].toString());
				}
				println("% ...");
				for (int i = sizeToUse / 2; i > 0; i--) {
					println("%  Element #" +              i  + ": " + trace[traceSize - i].toString());
				}
			} else {
				for (int i = 0; i < sizeToUse; i++) {
					println("%  Element #" + (traceSize - i) + ": " + trace[i].toString());
				}		
			}
		} else {
			e.printStackTrace();
		}
	}

    public static <T> String toString(Collection<T> collection, String divider) {
        StringBuilder sb = new StringBuilder();

        boolean first = true;

        for (T object : collection) {
            if (!first) {
                sb.append(divider);
            }
            first = false;
            sb.append(toString(object, divider));
        }
        return sb.toString();
    }

    public static <T,S> String toString(Map<T,S> map, String divider) {
        StringBuilder sb = new StringBuilder();

        boolean first = true;

        for (Map.Entry<T, S> entry : map.entrySet()) {
            if (!first) {
                sb.append(divider);
            }
            first = false;
            sb.append(toString(entry.getKey(),divider)).append(" => ").append(toString(entry.getValue(), divider));
        }

        return sb.toString();
    }

    public static String toString(Object object, String divider) {
        if ( object == null ) {
            return null;
        }
        else if (object instanceof Collection) {
            Collection collection = (Collection) object;
            return toString(collection, divider);
        }
        else if (object instanceof Map) {
            Map map = (Map) object;
            return toString(map, divider);
        }
        else {
            return object.toString();
        }
    }

    /**
     * Parses a string into a list of strings. Can handle formats:
     * {1,2, 3,4}
     * 1,2,3,4
     * "{","[","("," "
     * 
     * Make sure to put { in quotes if it is an input
     * Make sure that the string is not surrounded by quotes otherwise
     * we cant tell if """,""" is a list of " and "[ie {","}] or a list of two empty strings[ie {"", ""}] surrounded by quotes.
     * @param input Input string
     * @return list of strings from the list
     */
    public static List<String> parseListOfStrings(String input) {
    	String[] items = input.split(",");
    	    	
    	List<String> result = new ArrayList<>();
    	for (String item : items) {
			result.add(item.trim());
		}
    	
    	String firstItem = result.get(0);     	
    	String lastItem = result.get(result.size()-1);
    	// the first item may have {
    	if (firstItem.startsWith("{")) {
    		firstItem = firstItem.substring(1).trim();
    		if (lastItem.endsWith("}")) {
    			lastItem = lastItem.substring(0, lastItem.length()-1).trim();
    		} else {
    			error("String starts with \"{\" but doesnt end with \"}\" :" + input);
    		}
    	} else {
    		if (lastItem.endsWith("}")) {
    			error("String doesnt start with \"{\" but ends with \"}\" :" + input);
    		}
    	}
    	
    	result.set(0, firstItem);
    	result.set(result.size()-1, lastItem);

        // Remove quotes
        for (int i = 0; i < result.size(); i++) {
            String item = result.get(i);
            if (item.startsWith("\"") && item.endsWith("\"")) {
                item = item.substring(1, item.length()-1);
                // Dont trim here, as the quotes would be used to prevent removing whitespace
                result.set(i, item);
            }

        }
        return result;
    }

	public static String removeAnyOuterQuotes(String str) {
		if (str == null || !str.startsWith("\"")) { return str; }
		return str.substring(1, str.length() - 1);
	}

    public static boolean isMessageTypeEnabled(MessageType type) {
        return !filteredMessageTypes.contains(type);
    }

	public static Boolean parseBoolean(String bool) {
		return bool.equalsIgnoreCase("true") ||
				bool.equalsIgnoreCase("1") ||
				bool.equalsIgnoreCase("t") ||
				bool.equalsIgnoreCase("y") ||
				bool.equalsIgnoreCase("yes");
	}
	
	public static String unzipFileIfNeeded(String fileName) throws IOException {
		if (fileName.endsWith(".gz")) {
			String readString  = readFromGzippedFile(fileName);
			String newFileName = fileName.subSequence(0, fileName.lastIndexOf(".gz")).toString();
			writeStringToFile(readString, new CondorFile(newFileName));
			return newFileName;
		}
		return null;
	}

	public static void compressFile(String fileNameRaw) {
		int minSizeToCompressInK = 1000;
        compressFile(fileNameRaw, minSizeToCompressInK);
    }

	private static void compressFile(String fileNameRaw, int toUse_minSizeToCompressInK) {
		if (fileNameRaw == null) { return; }
		String fileName = replaceWildCardsAndCheckForExistingGZip(fileNameRaw);
		if (fileNameRaw.endsWith(".gz")) { 
			println("%    No need to compress since already in 'gz' format: " + fileName); 
			return;
		}
		
		File    f = new CondorFile(fileName);
		long size = f.length() / 1000; // The units of File.length() are BYTES.
		if (size < toUse_minSizeToCompressInK) {
			println("%    No need to compress since small: " + fileName);
			return;
		}
        copyAndGzip(fileName, fileName, true);
    }
	
	private static void copyCompressedFile(String fileName1, String fileName2) {
		String renamed1 = replaceWildCards(fileName1);
		String renamed2 = replaceWildCards(fileName2);	
		if (renamed1.equals(renamed2)) {
			Utils.waitHere("You are requesting a file be copied to itself: " + renamed1);
			return;
		}
		try {
			writeToGzippedFile(renamed2, readFromGzippedFile(renamed1)); // Probably a better way to do this (maybe use copyDirectory below?), but simply reading-writing line-by-line failed (at least between Windows and Linux).
		} catch (IOException e) {
			reportStackTrace(e);
			error("Problem in copyCompressedFile: " + e);
		}
	}	

	private static boolean copyAndGzip(String fileName1, String fileName2, boolean removeUnzippedVersionOfFileName2) {
		// It is ok to have fileName1 = fileName2 since ".gz" might be added to fileName2.
		try {
			String  renamed1   = replaceWildCards(fileName1);
			String  renamed2   = replaceWildCards(fileName2);
			boolean compressed;

            // See if a compressed version exists if the regular version doesn't.
			if (!Utils.fileExists(renamed1) && Utils.fileExists(renamed1 + ".gz")) {
				copyCompressedFile(renamed1, renamed2);
				compressed = true;
			} else {
				compressed = writeToGzippedFile(renamed2, readFileAsString(renamed1));
			}
			if (compressed && removeUnzippedVersionOfFileName2) {
				File renamed2AsFile = new CondorFile(renamed2);
				if ( renamed2AsFile.exists()) { renamed2AsFile.delete(); } 
			}
			return compressed;
		} catch (IOException e) {
			reportStackTrace(e);
			error("Problem in copyAndGzip:\n   " + e);
			return false;
		}
	}
	
	public static void moveAndGzip(String fileName1raw, String fileName2raw, boolean removeUnzippedVersionOfFileName2) {
		String fileName1 = replaceWildCards(fileName1raw);
		String fileName2 = replaceWildCards(fileName2raw);
		if (fileName1.equals(fileName2)) {
			compressFile(fileName1);
			return;
		}
		if (!copyAndGzip(fileName1, fileName2, removeUnzippedVersionOfFileName2)) {
			Utils.waitHere("Something went wrong: moveAndGzip\n   " + fileName1raw + "\n   " + fileName2raw);
		}
		(new CondorFile(fileName1)).delete();
	}

    private static String readFromGzippedFile(String fileNameRaw) throws IOException {
		String fileName = replaceWildCards(fileNameRaw);
        StringBuilder stringBuilder;
        BufferedReader reader = null;
        try {
            reader = new BufferedReader(new InputStreamReader(new CompressedInputStream(new CondorFile(fileName))));
            stringBuilder = new StringBuilder();

            String s;

            while ((s = reader.readLine()) != null) {
                stringBuilder.append(s).append("\n");
            }

        } finally {
            if ( reader != null ) try {
                reader.close();
            } catch (IOException ignored) {
            }
        }
        return stringBuilder.toString();
    }

    private static boolean writeToGzippedFile(String fileNameRaw, String stringToWrite) throws IOException {
		String       fileName = replaceWildCards(fileNameRaw);   
		ensureDirExists(fileName);
        BufferedWriter writer = null;
        try { // Assume the caller knows that this file is big enough to warrant compression.
        	writer = new BufferedWriter( new OutputStreamWriter(new CompressedOutputStream(fileName, true)));

            writer.append(stringToWrite);
        }
        finally {
            try {
                if (writer != null) {
                    writer.close();
                }
            } catch (IOException iOException) { return false; }
        }
        return true;
    }
}
