package edu.wisc.cs.will.FOPC_MLN_ILP_Parser;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings.VarIndicator;
import edu.wisc.cs.will.FOPC.PredicateName.FunctionAsPredType;
import edu.wisc.cs.will.ResThmProver.VariantClauseAction;
import edu.wisc.cs.will.Utils.*;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileInputStream;

import java.io.*;
import java.net.URL;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.wisc.cs.will.Utils.MessageType.*;


// TODO(?): clean up so that the currentDirectory is always intelligently set (and rest after reading a file).

// Aside: search for this: Because the silly IL language has a weird way of dealing with lists, 'correct' for that here.
//        if the parser has problems with named arguments and unbracketed lists.

// Useful when printing things: tokenizer.lineno()

/*
 * Parse a file (or some other text stream) as one containing FOPC sentences as well as "directives" to MLN's, ILP, etc.
 * Directives include the following.   Note that many commands need to be terminated with a '.' or a ';'
 *
 *   setParam:       paramName = paramValue.        // Set this parameter to the value.  The equal sign and EOF are optional (so must all be on one line).
 *                                                  // Note that the parser does not check for valid parameter names nor values.  Later instances check this, and hence
 *                                                  // error reports might come much later.
 *
 *                                                  // Note: if a parameter - assume its name is xyz - is set it can be referred to later by @xyz.
 *                                                  //       CURRENTLY THIS ONLY WORDS FOR NUMBERS (more specifically, only via calls to processNumber) AND SINGLE TOKENS.
 *
 * 	 import:         fileName.                      // Read in another file.  Can provide full path names; otherwise will be relative to the directory in which the current file resides.  An extension of Utils.defaultFileExtensionWithPeriod will be added if the file name w/o any extension does not exist.
 *   importLibrary:  fileName.                      // Read in a pre-existing library file.  Only file names without an extension should be provided.
 *                                                  //  Existing libraries: arithmeticInLogic
 *                                                  //                      comparisonInLogic
 *                                                  //                      differentInLogic
 *                                                  //                      listsInLogic
 *                                                  //  Modes for each of those libraries have the same names as above, but are prefixed with "modes_"
 *                                                  //  Currently all libraries are automatically loaded.  To override, do:     setParam: loadAllLibraries = false.
 *
 *   numericFunctionAsPred: predName/numbArgs,      // A special-case determinate, where the specified argument (counting from 1) is the "output"
 *                   arg=#                          // when all the other variables are bound.  In addition, this argument is NUMERIC (TODO might want to redefine this).
 *
 *   				 Besides 'numeric' other prefixes are allowed to "FunctionAsPred."  Here is the complete list:
 *   					      numeric,       bool,  // 'Categorical' is a "string token" (ie, an atom) and 'structured' is something involving an FOPC function.
 *
 *
 *   bridger:        predName/numbArgs              // A special-case determinate, where the role of this predicate is to enable the addition of some other predicate(s).
 *
 *   inline:         predName/numbArgs              // This predicate, which needs to be a Horn clause, will have its body 'in lined' into
 *   												// learned clauses.  For example, if we inline 'Q(x) :- R(x), S(x)' and have learned
 *   												// 'P(x) :- Q(x), W(x)', the result will be 'P(x) :- R(x), S(x), W(x)'.
 *   												// It is an error if predName/arity matches more than one clause.
 *
 *   relevant:       predName/numbArgs, strength.   // A way to give hints about the relevance of literals to the concept being learned.
 *   												// The strengths are one of those in 'enum RelevanceStrength' (if the strength is
 *   												// left out, it defaults to RELEVANT).  The comma is optional but an EOL is mandatory (since long relevance statement might require than one line for readability).
 *
 *   												// Currently the code only matches on 'predName'
 *   												// and ignores 'numbArgs' but these should be given nevertheless (the long-term intent
 *   												// is that 'numbArgs=-1' will mean "for all versions of literals that use 'predName').
 *   												// This is closely related to 'cost' but the TuneParametersForILP class uses
 *   												// relevant's but not cost's.  (The current implementation assigns 'relevant' to costs
 *   												// so no need to use both.)
 *
 *   												// Can also include the 'max' and 'maxPerInputVars' optional arguments used in 'mode'.
 *
 *                                                  // Advanced isVariant of the above.  All the new head predicates will have 'inline' asserted for them.
 *                                                  // Each 'newHead' will actually be a unique predicate name.
 *                                                  // Also, literals should be TYPED here since new modes created (if a variable appears more than once.
 *                                                  // only need to type the FIRST occurrence - additional TYPE'ing OK, but need to be consistent or an error will result).
 *                                                  // Since these lead to 'mode' specifications, can also use [maxP=#] and [maxPerInputVars=#] here (see mode: for explanation).
 *                                                  // These need to be AFTER the strength.
 *   relevant:           literal,  strength.        //   Will add:                                   'relevant: newHead/#FVs, strength'
 *   relevant:       NOT(literal), strength.        //   Will add: 'newHead(FVs) :- \+ literal.' and 'relevant: newHead/#FVs, strength'
 *    												//      Where FVs are the free variables in literal.
 *   relevant:   	 [lit1, ..., litN], strength.   //   Will add: 'newHead(allArgsInLiterals) :- literal1, ..., literalN.' and 'relevant: newHead/#allArgsInLiterals, strength'  Plus will 'inline newHead'
 *   relevant:    AND(lit1, ..., litN), strength.   //   Same as above, but []'s not used.  Note that for ANDs there cannot be embedded lists.
 *   relevant:     OR(lit1, ..., litN), strength.   //   Will add: 'newHead(allArgsInLiterals) :- literal1.' ... 'newHead(allArgsInLiterals) :- literalN.' and 'relevant: newHead/#allArgsInLiterals, strength'
 *   											    //   Note here 'newHead' is NOT inlined.  This means it needs to be carried around in any new theories learned.
 *                                                  //   Note that for OR, embedded lists and AND(lit1, lit2, ..., litN) are allowed.  Embedded lists are implicitly combined with AND.
 *                                                  //   However, in neither case can a NOT be embedded (parser would need to be extended substantially).
 *           ... head = typedHeadLiteral            // NOTE: in the above 'relevant' statements using AND, OR, and NOT, there is an other optional argument:
 *                                                  //          head = typedHeadLiteral
 *                                                  // This will be the head of the inference rule produced from the 'relevant' - if 'head' is not provided, one will be created.
 *
 *           ... noAutoNegate                       // The AND, OR, and 'bare' literal relevant's will also create not_P :- \+ P, with one lower relevance value (but never less than neutral
 *                                                  // (no provided strength is less than neutral, not additional relevant's created).  This flag overrides that.  (TODO - add a global flag that does for all relevant's.)
 *
 *   containsCallable: predicate/arity.             // Specifies that the terms of the literal/function with the indicates predicate name may be callable elements.
 *                                                  // An example of this is negation by failure, in which the first term is the clause to execute to determine if
 *                                                  // the negation by failure succeeds or fails.
 *
 *   cost:           predName/numbArgs, real        // The cost (e.g., for scoring clauses) associated with this predicate name (with this many arguments) is 'real.'  The comma is optional.  The EOL should be ';' if the 'real' is an integer (since otherwise the decimal point ['.'] confuses the parser).  Default cost = 1.
 *   mode:           typed_literal                  // This states the types of the arguments in this literal.
 *                   [target=pred/numbArgs]         // Types are + (an 'input' variable; MUST be present earlier in the clause), - (an 'output' variable; need not already be present in the clause), and # (a constant; need not already be present).
 *                   [max=#]                        // Also, '$' means use a variable that only appears ONCE and '^' means only use a NEW variable.  A variable can be followed by '!k' or $k' - the former means "this predicate will be true for EXACTLY k possible values for this argument, where the latter is similar but for "AT MOST K."
 *  			     [maxPerInputVars=#].           // Optionally [not yet implemented] can say that the above mode only applies when learning this target.  A sample is 'parentOf/2' (the literal whose predicate name is 'parentOf' and which has two arguments).
 *  			     		                        // Optionally say that typed_literal can appear in a learned clauses at most # (some integer) times.
 *  			     				                // Optionally indicate that PER SETTING to the 'input' (i.e. '+') variables, can occur at most this many times (an idea taken from Aleph).
 *              // More notes on modes:
 *				//   If a +mode, then MUST use an previously added variable of same type.
 *				//   If a $mode, then MUST use into an previously added variable that APPEARS ONLY ONCE EARLIER IN THE CLAUSE.
 *				//   If a -mode, then CAN  use an previously added variable of same type.
 *				//   If a ^mode, then treat SAME as '-' but ONLY create a new variable (ie, do NOT use other new variables of this type created for this literal)
 *				//   If a #mode, then use one of the selected positive SEEDs and find a constant of that type.  TODO - use ANY seed?  maybe the negatives offer some good values?
 *				//   If a &#64;mode (at sign), then use the SPECIFIC value given (should be a constant and not a variable).
 *				//   If a &mode, then combine '-' and '#'.
 *				//   If a :mode, then combine '+' and '#'.  TODO - allow MULTIPLE CHARACTERS (eg, any pair)!
 *
 *
 *   isaInterval:    predName/numbArgs.             // Inform ILP that this predicate specifies a 1D (numbArgs=3), 2D (numbArgs=6), or 3D (numbArgs=9) number interval (a.k.a., a 'tile').  E.g.: 'isaInterval: ageInRange/3' says that ageInRange(lower, value, upper) is true when lower &lt;= value &lt; upper.  This information is used to prune search spaces.
 *
 *   precompute:     fileName = string, clause.     // This Horn ('definite' actually) clause should be precomputed.  Can also use 'precompute1' to 'precompute99' to put results in separate files (so if there is a crash, only need to precompute some of the data).
 *                                                  // Precomputed facts in precomputeN will be available when precomputing M, for M > N.
 *                                                  // If the optional "fileName = string" is present (comma afterwards is optional), 'string' is used as the file name; otherwise 'precomputedN.txt' is.
 *
 *   prune:          prunableLiteral,               // If a literal that is a variant of 'ifPresentLiteral' is in already in a clause being learned,
 *                   ifPresentLiteral,              // do not add something that also a variant of 'prunableLiteral' - the commas and the final '.' (or ';') are optional.
 *                   [warnIf(N)].                   // The optional third argument says to complain if there are N or more existing rules whose head unifies with 'ifPresentLiteral' since this pruning is based on the assumption that less than N such rules exist (i.e., the 'precompute:' facility assumes N=1).
 *
 *   prune:          prunableLiteral.               // It is also possible for a literal to be pruned INDEPENDENTLY of the current clause's body, e.g. f(x,x) might be a tautalogy.
 *                                                  // Here the EOL (i.e., '.' or ';') is mandatory (to distinguish from the above version of 'prune:') and there cannot be a 'warnIf' (since they don't make sense here).
 *
 *   pruneTrue and pruneFalse                       // These can be used instead of 'prune' to state the REASON for the pruning.
 *
 *   queryPred:      predName/numbArgs.             // Used for MLNs.  The EOL ('.' or ';') is optional.
 *
 *   range:          type = {value1, ..., valueN}.  // Specify the possible values for this type.  The outer braces are optional. The shorthand "..." can be used for integer-valued ranges.
 *
 *   usePrologVariables:   true/false/yes/no/1/0.   // These determine whether or not lower case is a variable (standard logic) or a constant (Prolog).
 *   useStdLogicVariables:   ditto                  // These can be reset in the middle of files, and the instances created will be correct, but text files produced are likely to be inconsistent (TODO: each variable and constant needs to record its case at time of creation?  Tricky, though since 'john' and 'John' might map to the same constant.)
 *   useStdLogicNotation:             ditto
 *   usePrologNotation:               ditto
 *
 *   nonOperational:
 *      <NonOperationalPredicateName>/<Arity>   // Specifies a non-operational predicate's operational predicate names.
 *      operational=<OperationalPredicate>
 *      [, operational=<OperationalPredicate]*
 *
 *   The following all take predicateName/arity (and an optional EOL ['.' or ';']).
 *
 *      okIfUnknown:                                // It is OK if during theorem proving this predicate is undefined.  Helps catch typos.  If numberArgs='#' then applies to all versions of predName.  The EOL ('.' or ';') is optional.
 *
 * Everything else is interpreted as an FOPC sentence (using the strings "ForAll" and "ThereExists" ["Exists" is also OK, but "All" is NOT since it is a built-in Prolog predicate] and
 * the standard logical connectives of {'and', 'or', '^', '&', 'v', '->', ':-', etc.).  FOPC sentences can be weighted using one of the following:
 *
 * 		weight = double  FOPC.
 *      wgt    = double  FOPC.
 *      weight(double)   FOPC.
 *      wgt(double)      FOPC.
 *
 *   Can also use this to mark examples that are not binary valued.  NOTE: this is stored in the 'weight' field and so cannot currently have weighted examples with non-Boolean output values.
 *      output = double  FOPC.
 *   All other variants of the above, where 'output' replaces 'weight' or 'out' replaces 'wgt' are acceptable.
 *   Can also do this (ie, 'regressionExample' is a special predicate name):
 * 		regressionExample(FOPC, double).  // TODO - also allow:  weightedExample(FOPC, double)?
 *   Related to this, one can also do annotatedExample(FOPC, annotationString).  See LearnOneClause.processReadExample.
 *
 * where 'double' is some real number (integers are OK). In all of these cases a comma can optionally separate the weight specification and the FOPC sentence.
 *
 * Can also add annotation to examples
 *
 * Also a "bare" double that starts a sentence and is NOT followed by an in-fix operator is interpreted as a weight on the following FOPC sentence.
 *
 * Notes: The term EOL in this file is used as shorthand to mean the GRAMMATICAL end of a statement, rather than the end of a line in a file.
 *        Case doesn't matter, except when distinguishing between variables and constants.   For predicate and function names, the first version encountered will be the one used, e.g., if "P" is encountered first, then later cases of "p" will become "P" as well.
 *
 * TODO  handle \+ w/o parens
 *
 *
 */
public class FileParser {
	private                 boolean dontPrintUnlessImportant = true;
    
    public          static final boolean allowSingleQuotes        = true; // If true, can use single quotes to wrap strings.
	 
	// Allows user to set it to a higher number but doesn't penalize all runs where there are fewer precomputes
	// It is mildly risky to make this a static, but acceptable.
	private    static int numberOfPrecomputeFiles = 125;

	// The parser can create additional predicates, by negating relevance statements it receives. This is used as the prefix for such predicate names.
	// It is made static for each access w/o a parser instance and made final to cannot be changed if multiple WILLs are active.
	private static final String will_notPred_prefix  = "wiNOT_";

	private              int maxWarnings  = 100; // This can be reset via 'setParameter maxWarnings = 10'

	public final HandleFOPCstrings  stringHandler;
	private StreamTokenizerJWS tokenizer;
	private List<Sentence>[]   sentencesToPrecompute;
	private String[]           sentencesToPrecomputeFileNameToUse;
	private Set<LiteralToThreshold> literalsToThreshold;
	private String             directoryName      = null;
	private String             prefix             = null;
	private String             fileName           = null;

	private final boolean treatAND_OR_NOTasRegularNames = false; // If true, treat AND and OR as function or predicate names.  (Used for IL parsing, for example.)


	public FileParser(HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
	}

	public List<Sentence> getSentencesToPrecompute(int index) {
		if (sentencesToPrecompute == null) { return null; }
		return sentencesToPrecompute[index];
	}

	public String getFileNameForSentencesToPrecompute(int index) {
		if (sentencesToPrecomputeFileNameToUse == null) { return null; }
		return sentencesToPrecomputeFileNameToUse[index];
	}

	private void setFileNameForSentencesToPrecompute(int index, String nameRaw, boolean isaDefaultName) {
		String name = Utils.replaceWildCards(nameRaw);
		if (sentencesToPrecomputeFileNameToUse == null) { sentencesToPrecomputeFileNameToUse = new String[getNumberOfPrecomputeFiles()]; }
		String old = getFileNameForSentencesToPrecompute(index);
		if (old != null && (old.equals(name) || isaDefaultName)) { return; }
		if (old != null && !old.startsWith("precomputed")) { 
			Utils.waitHere("setFileNameForSentencesToPrecompute for precompute" + (index > 0 ? index : "") + ":\n  Had " + old + " but now setting\n  To  " + name + "  There cannot be multiple names for the same precompute file.");
			return;
		}
		sentencesToPrecomputeFileNameToUse[index] = stringHandler.precompute_file_prefix + name;
		if (stringHandler.precompute_file_postfix != null && 
			!sentencesToPrecomputeFileNameToUse[index].endsWith(stringHandler.precompute_file_postfix)) {
			sentencesToPrecomputeFileNameToUse[index] += stringHandler.precompute_file_postfix;
		}
	}

	public Collection<LiteralToThreshold> getLiteralsToThreshold() {
		return literalsToThreshold == null ? Collections.EMPTY_SET : literalsToThreshold;
	}

	// Return what seems to be the working directory for the current task.
	public void setDirectoryName(String name) {
		checkDirectoryName(name);
	}
	public String getDirectoryName() {
		return directoryName;
	}
	public void setPrefix(String name) {
		prefix = name;
	}
	public String getPrefix() {
		return prefix;
	}

	// This does not allow any non-literals in the file (other than comments).
	// However it DOES allow a literal to NOT have a trailing '.' or ';' (some programs output their results in such a notation).
	public List<Literal> readLiteralsInPureFile(String fNameRaw) {
		String  fName          = Utils.replaceWildCardsAndCheckForExistingGZip(fNameRaw);

		List<Literal> results = new ArrayList<>(4);
		try {
			File   file               = (getFileWithPossibleExtension(fName));
			String newDirectoryName   = file.getParent();
			String hold_directoryName = directoryName;
			checkDirectoryName(newDirectoryName);
			this.fileName = fName; // Used to report errors.
			InputStream  inStream = new CondorFileInputStream(file);

			tokenizer = new StreamTokenizerJWS(new InputStreamReader(inStream)); // Don't need to do more than 2-3 push backs, so don't need a big buffer.
			initTokenizer(tokenizer);
			while (tokenizer.nextToken() != StreamTokenizer.TT_EOF) {
				tokenizer.pushBack();
				Literal lit = processLiteral(false);
				results.add(lit);
				peekEOL(true); // Suck up an optional EOL.
			}			
			inStream.close();
			checkDirectoryName(hold_directoryName);
		}
		catch (FileNotFoundException e) {
			Utils.reportStackTrace(e);
			Utils.error("Unable to successfully read this file: " + fName);
		}
		catch (Exception e) {
			Utils.reportStackTrace(e);
			Utils.error("Unable to successfully parse this file: " + fileName + ".\n  Have read " + Utils.comma(results) + " literals.\nNOTE THIS METHOD DOES NOT HANDLE PARSER INSTRUCTIONS!\nError message: " + e.getMessage());
		}
		return results;
	}

	public List<Sentence> readFOPCfile(String fName) {
		return readFOPCfile(fName, false);
	}

	private void checkDirectoryName(String newDirectoryName) {
		if (newDirectoryName == null) {
		} // If this is from a reset of a 'hold' of a directory name, don't reset back to null.
		else if (directoryName == null) {
			directoryName = newDirectoryName;
		} else if (!directoryName.equals(newDirectoryName)) {
			directoryName = newDirectoryName;
		}
	}

	private List<Sentence> readFOPCfile(String fNameRaw, boolean okIfNoSuchFile) {
		String fName = Utils.replaceWildCardsAndCheckForExistingGZip(fNameRaw);
		try {
			File   file               = (getFileWithPossibleExtension(fName));
			String newDirectoryName   = file.getParent();
			String hold_directoryName = directoryName;
			checkDirectoryName(newDirectoryName);
			this.fileName = fName; // Used to report errors.
			InputStream  inStream = new CondorFileInputStream(file);
			List<Sentence> result = readFOPCstream(file, inStream);
			inStream.close();
			checkDirectoryName(hold_directoryName);

			return result;
		}
		catch (FileNotFoundException e) {
			if (okIfNoSuchFile) { return null; }
			Utils.reportStackTrace(e); 
			Utils.error("Unable to successfully read this file:\n  " + fName + "\n Error message: " + e.getMessage());
		}
		catch (Exception e) {
			Utils.reportStackTrace(e);
			Utils.error("Unable to successfully parse this file: " + fileName + ".  Error message: " + e.getMessage());
		}
		return null;
	}
	
	// If a file exists, add the default Utils.defaultFileExtensionWithPeriod extension.
	private File getFileWithPossibleExtension(String fileNameRaw) throws IOException {
		if (fileNameRaw == null) {
			Utils.error("Should not call with a NULL file name.");
		}
		String fileName = Objects.requireNonNull(fileNameRaw).trim();
		File f = new CondorFile(fileName);
		if (!f.exists()) {
			f = new CondorFile(fileName + Utils.defaultFileExtensionWithPeriod);
			if (!f.exists()) {
				f = new CondorFile(fileName + ".bk"); // Try another built-in file name.
				if (!f.exists()) {
					f = new CondorFile(fileName + ".mln"); // Try yet another built-in file name.
					if (!f.exists()) {
						f = new CondorFile(fileName + ".db"); // Try yet another built-in file name.
						if (!f.exists()) {
							f = new CondorFile(fileName + ".fopcLibrary"); // Try yet another built-in file name.
							if (!f.exists()) {
								throw new FileNotFoundException();
							}
						}
					}
				}
			}
		}
		return f;
	}

	/*
	 * A variant of readFOPCfile(String fileName) where an input stream
	 * instead of a file name is provided.
	 * @return A list of sentences, the result of parsing the given file.
	 */
	private List<Sentence> readFOPCstream(File file, InputStream inStream) throws ParsingException {

        // This is a big hack to pass around the name with stream.
        // There are better ways to do this, but not at this point in time.
        Reader r;
        if ( inStream instanceof NamedInputStream ) {
            r = new NamedReader(new InputStreamReader(inStream), inStream.toString());
	}
        else {
            r = new InputStreamReader(inStream);
        }

		return readFOPCreader(file, r);
	}

	/*
	 * A variant of readFOPCfile(String fileName) where a string instead of
	 * a file name is provided.
	 */
	public List<Sentence> readFOPCstream(String string) {
		try {
			return readFOPCreader(new StringReader(string), null); // Fine that there is no directory here, since reading a string.
		}
		catch (Exception e) {
			Utils.reportStackTrace(e);
			Utils.error("Error parsing: '" + (string != null && string.length() > 1500 ? string.substring(0, 1500) + " ..." : string) + "'."); return null;
		}
	}

	public List<Sentence> readFOPCreader(Reader inStream, String newDirectoryName) {
		String hold_directoryName = directoryName;
		if (newDirectoryName != null) { checkDirectoryName(newDirectoryName); }
		List<Sentence> results = readFOPCreader(null, inStream);
		if (newDirectoryName != null) { checkDirectoryName(hold_directoryName); }
		return results;
	}

	private void initTokenizer(StreamTokenizerJWS theTokenizer) {
		theTokenizer.resetSyntax();                // Clear everything so we can reset to what we want.
		theTokenizer.ordinaryChar('/');
		theTokenizer.slashSlashComments();     // The string "//" is interpreted as a "comment from here to end of line."
		theTokenizer.slashStarComments();     // The string "/* starts a comments that ends at "*/".
		theTokenizer.commentChar('%');             // Also used YAP Prolog's character for "comment from here to end of line."
		theTokenizer.lowerCaseMode();         // Do NOT convert everything to lower case (case differentiates variables from constants, plus we want to print things out using the case users provided).
		theTokenizer.eolIsSignificant();      // EOL is NOT significant.  Instead need a ' or a ';' to indicate EOL.
		theTokenizer.quoteChar('"');               // Allow quoted tokens.  Quoted tokens are always constants, regardless of the case of their first letter.
		theTokenizer.quoteChar('\'');
		theTokenizer.whitespaceChars(' ', ' ');    // Specify the white-space characters.
		theTokenizer.whitespaceChars('\n', '\n');	//   Newline (aka, line feed).
		theTokenizer.whitespaceChars('\r', '\r');	//   Carriage return.
		theTokenizer.whitespaceChars('\t', '\t');	//   Tab.
		theTokenizer.wordChars('A', 'Z');          // The legal characters in tokens.  Ideally should not start with a number, but no big deal.
        theTokenizer.wordChars(192, 255);          // Mark (some) accented characters as word characters.
		theTokenizer.wordChars('a', 'z');
		theTokenizer.wordChars('\u00AA', '\u00FF'); // THIS IS DONE BOTH HERE AND IN StringConstant (though not harmful - just adds more quote marks than are necessary, when only done in one place, some problems arose).
		theTokenizer.wordChars('0', '9');
		theTokenizer.wordChars('_', '_');
		theTokenizer.wordChars('?', '?');
	}

	private static final Pattern precomputePattern = Pattern.compile("precompute([0-9]+)");
    
	/*
	 * A variant of readFOPCfile(String fileName) where a 'reader' instead
	 * of a file name is provided.
	 */
	private List<Sentence> readFOPCreader(File file, Reader inStream) {
		if (file == null && inStream == null) { return null; }

		VarIndicator holdVarIndicator = stringHandler.getVariableIndicatorNoSideEffects(); // Be sure to pop back to current setting after reading.
		String fileNameForErrorReporting  = "stream";
        if ( file != null ) {
            fileNameForErrorReporting =file.getParent();
        }
        else if ( inStream instanceof NamedReader ) {
            fileNameForErrorReporting = inStream.toString();
        }

		String hold_directoryName = directoryName;
		String parent = (file == null ? null : file.getParent());
		if (file != null) {	checkDirectoryName(parent);	}

		List<Sentence> listOfSentencesReadOrCreated = new ArrayList<>(8);
		tokenizer = new StreamTokenizerJWS(inStream); // Don't need to do more than 2-3 push backs, so don't need a big buffer.
		initTokenizer(tokenizer);
		
		
		// Note: the following should be "stand-alone words":  '(', ')', ',', ', ';'. '[', ']'
		int tokenRead;
		Sentence nextSentence;

		try {
			tokenRead = tokenizer.nextToken();
			while (tokenRead != StreamTokenizer.TT_EOF) {  // TODO discard this test code below

				nextSentence = null;
				// Use this very carefully!
				// If true, will avoid copying sentences as recursive calls, due to imports, return.

				// TODO(@hayesall): Which of these are actually listed?
				switch (tokenRead) {
					case StreamTokenizer.TT_WORD:
						String currentWord = tokenizer.sval();
						boolean colonNext = checkAndConsume(':'); // If the next character is a colon, it will be "sucked up" and 'true' returned.  Otherwise it will be puhsed back and 'false' returned.
						if (colonNext && currentWord.equalsIgnoreCase("setParam"))       { processSetParameter(); break; }
						if (colonNext && currentWord.equalsIgnoreCase("setParameter"))   { processSetParameter(); break; }
						if (colonNext && currentWord.equalsIgnoreCase("mode"))           { processMode(listOfSentencesReadOrCreated); break; }
						if (colonNext && currentWord.equalsIgnoreCase("numericFunctionAsPred"))           { processFunctionAsPred();           break; }
						if (colonNext && currentWord.equalsIgnoreCase("bridger"))        { processBridger();     break; }
						if (colonNext && currentWord.equalsIgnoreCase("temporary"))      { processTemporary();   break; }
						if (colonNext && currentWord.equalsIgnoreCase("inline"))         { processInline();      break; }
						if (colonNext && currentWord.equalsIgnoreCase("relevant"))       { processRelevant(       listOfSentencesReadOrCreated); break; } // Can add a sentence, so pass in the collector.
                        if (colonNext && currentWord.equalsIgnoreCase("nonOperational")) { processNonOperational(); break; }
                        if (colonNext && currentWord.equalsIgnoreCase("relevantLiteral")) {
                            processRelevantLiteralNew(listOfSentencesReadOrCreated);
                            break;
                        } // Can add a sentence, so pass in the collector.
                        if ( colonNext && currentWord.equalsIgnoreCase("alias")) {
                            processLiteralAlias();
                            break;
                        }
                        if ( colonNext && currentWord.equalsIgnoreCase("containsCallable"))  { processContainsCallables(); break; }
                        if (colonNext && currentWord.equalsIgnoreCase("supportLiteral"))      { processSupporter();   break; }
                        if (colonNext && currentWord.equalsIgnoreCase("supportingPredicate")) { processSupporter();   break;}
                        if (colonNext && currentWord.equalsIgnoreCase("supportPredicate"))    { processSupporter();   break; }
						if (colonNext && currentWord.equalsIgnoreCase("cost"))                { processCost();   break; }
						if (colonNext && currentWord.equalsIgnoreCase("precompute"))          { processPrecompute(0); break; } 
						if (colonNext && currentWord.startsWith("precompute"))     {
							// Do the regex matching now.
							Matcher m = precomputePattern.matcher(currentWord);
							if (m.matches()) {
								String pMat = m.group(1);
								int numPrecompute = Integer.parseInt(pMat);
								processPrecompute(numPrecompute);
								break;
							}
							Utils.waitHere("Word starts with 'precompute' but doesn't match: " + precomputePattern);
						}
						if (colonNext && currentWord.equalsIgnoreCase("prune"))          { processPrune(0); break; }
						if (colonNext && currentWord.equalsIgnoreCase("pruneTrue"))      { processPrune(1); break; }
						if (colonNext && currentWord.equalsIgnoreCase("pruneFalse"))     { processPrune(-1); break; }
						if (colonNext && currentWord.equalsIgnoreCase("isaInterval"))    { processISAInterval(); break; }
						if (colonNext && currentWord.equalsIgnoreCase("range"))          { processTypeRange(  ); break; }
						if (colonNext && currentWord.equalsIgnoreCase("queryPred"))      { processQueryPred(  ); break; }
						if (colonNext && currentWord.equalsIgnoreCase("okIfUnknown"))                    { processDirective(currentWord);  break; }
						if (colonNext && currentWord.equalsIgnoreCase("useStdLogicVariables"))           { processCaseForVariables(true);  break; }
						if (colonNext && currentWord.equalsIgnoreCase("useStdLogicNotation"))            { processCaseForVariables(true);  break; }
						if (colonNext && currentWord.equalsIgnoreCase("usePrologVariables"))             { processCaseForVariables(false); break; }
						if (colonNext && currentWord.equalsIgnoreCase("usePrologNotation"))              { processCaseForVariables(false); break; }
						if (colonNext && currentWord.equalsIgnoreCase("import"))      {
							List<Sentence>  sentencesInOtherFile =                         processAnotherFile(false);
							if (sentencesInOtherFile         == null) { break; }
							listOfSentencesReadOrCreated.addAll(sentencesInOtherFile);
							break;
						}
						if (colonNext && currentWord.equalsIgnoreCase("importLibrary"))      {
							List<Sentence>  sentencesInOtherFile =                         processAnotherFile(true);
							if (sentencesInOtherFile         == null) { break; }
							listOfSentencesReadOrCreated.addAll(sentencesInOtherFile);
							break;
						}
						if (colonNext) { tokenizer.pushBack(); } // Need to push the colon back if it wasn't part of a special instruction.  It can also appear in modes of terms.

						// TODO(@hayesall): I dropped "weight" and "wgt" above, maybe they can be dropped here?
						if (currentWord.equalsIgnoreCase("weight") || currentWord.equalsIgnoreCase("wgt")) {
							nextSentence = processWeight(getNextToken()); break;
						}
						if (!ignoreThisConnective(true, currentWord) && ConnectiveName.isaConnective(currentWord) && !ConnectiveName.isTextualConnective(currentWord)) { // NOT's handled by processFOPC_sentence.
							//Utils.error("Need to handle a PREFIX connective: '" + currentWord + "'.");
							// If here, there must be exactly two arguments.
							ConnectiveName connective = stringHandler.getConnectiveName(currentWord);
							if (!checkAndConsume('(')) { tokenizer.nextToken(); throw new ParsingException("Expecting a left parenthesis, but read '" + reportLastItemRead() + "'."); }
							Sentence arg1 = processFOPC_sentence(0, true);
							if (!checkAndConsume(',')) { tokenizer.nextToken(); throw new ParsingException("Expecting a comma, but read '" + reportLastItemRead() + "'."); }
							Sentence arg2 = processFOPC_sentence(0, true);
							if (!checkAndConsume(')')) { tokenizer.nextToken(); throw new ParsingException("Expecting a right parenthesis, but read  '" + reportLastItemRead() + "'."); }
							nextSentence = stringHandler.getConnectedSentence(arg1, connective, arg2);
							break;
						}
						// The default is to read an FOPC sentence.
						tokenizer.pushBack();
						nextSentence =                                                  processFOPC_sentence(0);
						break;
					case StreamTokenizer.TT_NUMBER:  throw new ParsingException("Should not happen in the parser:  Read this NUMBER: " + tokenizer.nval());  // See comment above as to why this won't be reached.
					case ':':
						if (checkAndConsume('-')) { // At a Prolog-like "instruction to the system" (as opposed to a fact/rule being stated).
							processInstructionToSystem();
							break;
						}
						throw new ParsingException("Lines should not start with ':' unless followed by '-' (i.e., ':-').");
					case '\\':  // Could be starting '\+'
					case '~':
					case '(':
					case '{':
					case '[':
					case '!':
					case '+': // Could have something like '+5 < y'
					case '-': // Or, more likely, '-5 < y'   Could also be a "bare" weight.
						tokenizer.pushBack(); // The FOPC reader can handle these characters.
						nextSentence = processFOPC_sentence(0);
						break;
					case '.': // An empty sentence is OK, plus reading an FOPC sentence never sucks up the closing EOL.
					case ';':
						break;
					case StreamTokenizer.TT_EOL:    throw new ParsingException("Should not read EOL's here."); // EOL is in the "traditional" sense here (e.g., '\n').
					default:                        if (tokenRead == '/') {
						Utils.println("If a file ends with '*/' add a space after the '/' to overcome an apparent bug with StringTokenizer's handling of comments.");
					}
													throw new ParsingException("Read this *unexpected* character: '" + (char)tokenRead + "'."); // TODO - hit this once when the last character was the '/' in a closing quote (i.e., '*/').  Added a space afterwards and all worked fine.
				}
				if (nextSentence != null) {
					if (nextSentence.containsTermAsSentence()) {
						throw new ParsingException("This is not a valid FOPC sentence: '" + nextSentence + ".'  It contains a logical term where a logical sentence should appear.");
					}
					Sentence finalSentence = nextSentence.wrapFreeVariables(); // Add any implicit ForAll.
					listOfSentencesReadOrCreated.add(finalSentence);
				}
				stringHandler.resetAllVariables(); // Clear cache of variables, since old ones (if any) now out of scope.
				tokenRead = tokenizer.nextToken();
			}
		} catch (Exception e) {
			Utils.reportStackTrace(e);
			Utils.error("Unable to successfully parse this file: " + fileNameForErrorReporting + ".\nError message: " + e.getMessage());
		}
		checkDirectoryName(hold_directoryName);

		if (holdVarIndicator != null) { // If previously set, revert to that setting.
			stringHandler.setVariableIndicator(holdVarIndicator);
		} else {
			Utils.warning(STRING_HANDLER_VARIABLE_INDICATOR, "% Since this is the first setting of the notation for variables, will keep:\n%   variableIndicator = " + stringHandler.getVariableIndicator(), 1);
		}

		return listOfSentencesReadOrCreated;
	}

    /* Parses a string into a list of sentences.
     */
    public List<Sentence> parse(String string) {
        return readFOPCstream(string);
    }

    public Clause parseDefiniteClause(String definiteClause) throws ParsingException {

        Clause result = null;

        List<Sentence> sentences;
        
        if (!definiteClause.endsWith(".")) {
            definiteClause = definiteClause + ".";
        }

        sentences = readFOPCstream(definiteClause);

        if ( sentences == null ) {
            throw new ParsingException("parseDefiniteClause generated multiple clauses from: '" + definiteClause + "'.");
        }

        if ( sentences.size() > 1 ) {
            throw new ParsingException("parseDefiniteClause generated multiple clauses from: '" + definiteClause + "'.");
        }

        if ( sentences.size() == 1) {
            Sentence s = sentences.get(0);

            List<Clause> clauses = s.convertToClausalForm();

            if ( clauses.size() > 1 ) {
                throw new ParsingException("parseDefiniteClause generated multiple clauses from: '" + definiteClause + "'.");
            }

            if ( clauses.size() == 1 ) {
                result = clauses.get(0);
            }
        }

        return result;
    }

	private boolean ignoreThisConnective(boolean ignoreNOTs, String str) {
		return ((ignoreNOTs                    &&  ConnectiveName.isaNOT(str)) ||
				(treatAND_OR_NOTasRegularNames && (ConnectiveName.isaAND(str)  || ConnectiveName.isaOR(str)|| ConnectiveName.isaNOT(str))));
	}

	private void processInstructionToSystem() throws IOException {
		tokenizer.nextToken();
		String nextTokenAsString = tokenizer.reportCurrentToken();

		if       (nextTokenAsString.equalsIgnoreCase("discontiguous")) {
		}
		else if (nextTokenAsString.equalsIgnoreCase("dynamic")) {
		}
		else if (nextTokenAsString.equalsIgnoreCase("multifile")) {
		}
		else {
			Utils.warning("% Unknown ':- " + nextTokenAsString + "' command.");
		}
		skipToEOL();
	}

	private void skipToEOL() throws IOException {  // Should this stop at StreamTokenizer.TT_EOL?  Probably not.
		if (atEOL()) { return; }
		tokenizer.nextToken();
		while (!atEOL()) {
			int tokenRead = tokenizer.nextToken();
			if (tokenRead == StreamTokenizer.TT_EOF) { throw new IOException("Unexpected EOF: " + fileName); }
		}
	}

	/*
	 * Allow specification of notation for logical variables.  See comments about "useStdLogicVariables" and "usePrologVariables" above.
	 */
	private void processCaseForVariables(boolean defaultIsUseStdLogic) throws ParsingException, IOException {
		int nextToken = tokenizer.nextToken();

		if (nextToken != StreamTokenizer.TT_WORD) { throw new ParsingException("Expecting a token after " + (defaultIsUseStdLogic ? "useStdLogicVariables" : "usePrologVariables" + ", but read: '") + reportLastItemRead()); }
		if (tokenizer.sval().equalsIgnoreCase("true") || tokenizer.sval().equalsIgnoreCase("yes") || tokenizer.sval().equalsIgnoreCase("1")) {
			if (defaultIsUseStdLogic) { stringHandler.useStdLogicNotation(); } else { stringHandler.usePrologNotation();   }
		}
		else {
			if (defaultIsUseStdLogic) { stringHandler.usePrologNotation();   } else { stringHandler.useStdLogicNotation(); }
		}
		peekEOL(true);
	}

	private Literal processInfixLiteral(Term firstTerm, String inFixOperatorName) throws ParsingException, IOException {
		return processInfixLiteral(firstTerm, inFixOperatorName, false);
	}

	private Literal processInfixLiteral(Term firstTerm, String inFixOperatorName, boolean argumentsMustBeTyped) throws ParsingException, IOException {
		Term secondTerm;
        
        if (inFixOperatorName.equalsIgnoreCase("is")) {
            secondTerm = processIS(argumentsMustBeTyped);
        }
        else {
            secondTerm = processTerm(argumentsMustBeTyped);
        }

		List<Term>    args   = new ArrayList<>(2);
		PredicateName pName  = stringHandler.getPredicateName(inFixOperatorName); pName.printUsingInFixNotation = true;
        args.add(firstTerm);
        args.add(secondTerm);
		return stringHandler.getLiteral(pName, args);
	}

	private Term processIS(boolean argumentsMustBeTyped) throws ParsingException, IOException {
		return processMathExpression(null, argumentsMustBeTyped, false);
	}

	// This version is used if peeking ahead sees a '/' etc, e.g., 'p(x/y/z, 5)' or 'p(f(x)+f(y))'.
	private Term processMathExpression(boolean argumentsMustBeTyped) throws ParsingException, IOException {
		return processMathExpression(null, argumentsMustBeTyped, true);
	}

	private Term processMathExpression(Term initialTerm, boolean argumentsMustBeTyped, boolean insideLeftParen) throws ParsingException, IOException  {
		// Need to process something like "X is Y + Z / Q." where "X is" has been absorbed already.
		// When this is called, have encountered an left parenthesis or am starting a new in-fix expression.

		List<AllOfFOPC> accumulator = new ArrayList<>(4);
		boolean         lookingForTerm = true;
		if (initialTerm != null) {
			accumulator.add(initialTerm);
			lookingForTerm = false;
		}
		while (true) {
			int tokenRead = getNextToken();
			if (processPossibleConnective(tokenRead) != null) {  // A logical connective (e.g., 'and') ends an "X is Y + Z, p(X), ..."
				if (insideLeftParen) { throw new ParsingException("Unexpectedly read '" + reportLastItemRead() + " when inside a left parenthesis in a 'X is ...' expressions."); }

				tokenizer.pushBack(); // Return the connective.
				return convertAccumulatorToTerm(accumulator);
			}
			switch (tokenRead) {
				case '(':
				case '{':
				case '[':
					Term resultLeftParens = processMathExpression(argumentsMustBeTyped); // Parse up the closing right parenthesis.
					accumulator.add(resultLeftParens);
					if (!lookingForTerm) { throw new ParsingException("Encountered two terms in a row: '" + resultLeftParens + "'."); } // Could let this be implicit multiplication?
					lookingForTerm = false;
					break;
				case ')':
				case '}':
				case ']':
					// These are ok since we now allow p(x/y).    if (!insideLeftParen) { throw new ParsingException("Read a right parenthesis unexpectedly."); }
					if (!insideLeftParen) { tokenizer.pushBack(); }
					return convertAccumulatorToTerm(accumulator);
				case '.':
				case ';':
					if (insideLeftParen) { throw new ParsingException("Read an EOL ('" + tokenRead + "') unexpectedly."); }
					tokenizer.pushBack();
					return convertAccumulatorToTerm(accumulator);
				case '+': // These are the only in-fix operators currently known to the system (other than 'is').
					if (accumulator.isEmpty()) { break; } // Discard any leading + signs.
				case '*':
				case '/':
				case '-':
					FunctionName fName = null;
					if (checkAndConsume('*')) { fName = stringHandler.getFunctionName("**"); } // Exponentiation. (Check 'fName == null' here in case another IF is later added.)
					if (fName == null && checkAndConsume('@')) { fName = stringHandler.getFunctionName("/*"); } // Integer division (since '//' can't be used).
					if (fName == null) { fName = stringHandler.getFunctionName(String.valueOf((char) tokenRead)); }
					// OK if '-' is the first item.
					if (lookingForTerm && accumulator.size() > 0) { throw new ParsingException("Encountered two operators in a row: '" + reportLastItemRead() + "'."); }
					accumulator.add(fName);
					lookingForTerm = true;
					break;
				case StreamTokenizer.TT_WORD:
					Term resultWord = processRestOfTerm(tokenRead, argumentsMustBeTyped, true);
					accumulator.add(resultWord);
					if (!lookingForTerm) { throw new ParsingException("Encountered two terms in a row (missing comma?): '" + resultWord + "'.  Accumulator=" + accumulator); }
					lookingForTerm = false;
					break;
				default: throw new ParsingException("Read unexpected character when processing an 'X is ...' expression: '" + reportLastItemRead() + "'.");
			}
		}
	}

	/*
	 * Have a list of the form: "( term operator term ... operator term )"
	 * and have to use precedence rules to convert to a single term.
	 * Algorithm: find the lowest precedence operator and combine it and its
	 * two neighbors (break ties to the left). repeat until one term remains.
	 * @return A term, the root of the abstract syntax tree created by
	 *         parsing the given list.
	 */
	private Term convertAccumulatorToTerm(List<AllOfFOPC> accumulator) throws ParsingException {
		if (accumulator == null || accumulator.isEmpty()) { throw new ParsingException("Have an empty mathematical expression following an instance of 'X is ...'"); }
		while (accumulator.size() > 1) {
			//  First find the lowest-precedence operator.
			int lowestPrecedence  = Integer.MAX_VALUE;
			int countOfLowestItem = -1;
			int counter           =  0;
			for (AllOfFOPC item : accumulator) {
				if (item instanceof FunctionName) {
					int precedence = stringHandler.getOperatorPrecedence((FunctionName) item);

					if (precedence < lowestPrecedence) {
						lowestPrecedence  = precedence;
						countOfLowestItem = counter;
					}
				}
				counter++;
			}
			if (countOfLowestItem < 0) { Utils.error("Something went wrong when grouping the items in a mathematical expression: " + accumulator); }
			// Next combine the lowest-precedence operator and make a term with it and its two neighbors.
			FunctionName        fName    = (FunctionName) accumulator.get(countOfLowestItem);
			if (countOfLowestItem == 0 && fName == stringHandler.getFunctionName("-")) { // If '-' is the FIRST operator, need to handle it specially as an in-fix operator.
				Term            rightArg = (Term)         accumulator.get(countOfLowestItem + 1);
				List<Term>      args     = new ArrayList<>(1);
				args.add(rightArg);
				Function funct = stringHandler.getFunction(fName, args, null);
				accumulator.add(   countOfLowestItem + 2, funct); // Add after the two items combined.
				AllOfFOPC removed1 = accumulator.remove(countOfLowestItem + 1); // Do this in the proper order so shifting doesn't mess up counting.
				AllOfFOPC removed2 = accumulator.remove(countOfLowestItem);
			}
			else {
				if (countOfLowestItem < 1 || countOfLowestItem > accumulator.size() - 2) { Utils.error("Operators cannot be in the first or last positions: " + accumulator); }
				Term            leftArg  = (Term)         accumulator.get(countOfLowestItem - 1);
				Term            rightArg = (Term)         accumulator.get(countOfLowestItem + 1);
				List<Term>      args     = new ArrayList<>(2);
				args.add(leftArg);
				args.add(rightArg);
				Function funct = stringHandler.getFunction(fName, args, null);
				accumulator.add(   countOfLowestItem + 2, funct); // Add after the three items combined.
				AllOfFOPC removed1 = accumulator.remove(countOfLowestItem + 1); // Do this in the proper order so shifting doesn't mess up counting.
				AllOfFOPC removed2 = accumulator.remove(countOfLowestItem);
				AllOfFOPC removed3 = accumulator.remove(countOfLowestItem - 1);
			}
		}
		return (Term) accumulator.get(0);
	}

	private Sentence convertAccumulatorToFOPC(List<AllOfFOPC> accumulator) throws ParsingException {
		if (accumulator == null || accumulator.isEmpty()) {  // OK to have the empty sentence.
			return null;
		}
		while (accumulator.size() > 1) {
			//  First find the lowest-precedence operator.
			int lowestPrecedence  = Integer.MAX_VALUE;
			int countOfLowestItem = -1;
			int counter           =  0;
			for (AllOfFOPC item : accumulator) {
				if (item instanceof ConnectiveName) {
					int precedence = stringHandler.getConnectivePrecedence((ConnectiveName) item);

					if (precedence <= lowestPrecedence) {
						lowestPrecedence = precedence;
						countOfLowestItem = counter;
					}
				}
				counter++;
			}
			if (countOfLowestItem < 0) {
				Utils.error("Something went wrong when grouping the items in a complex FOPC sentence: " + accumulator);
			}
			ConnectiveName  cName    = (ConnectiveName) accumulator.get(countOfLowestItem);
			if (ConnectiveName.isaNOT(cName.name)) { // If 'NOT' or '~' is the connective, need to handle it specially as an in-fix operator.
				Sentence rightArg = (Sentence)accumulator.get(countOfLowestItem + 1);
				Sentence cSent    = stringHandler.getConnectedSentence(cName, rightArg);
				if (cName.name.equalsIgnoreCase("\\+")) { cSent = processNegationByFailure((ConnectedSentence) cSent); }
				accumulator.add(   countOfLowestItem + 2, cSent); // Add after the two items being combined.
				accumulator.remove(countOfLowestItem + 1); // Do this in the proper order so shifting doesn't mess up counting.
				accumulator.remove(countOfLowestItem);
			}
			else { // Next combine the lowest-precedence operator and make a sentence with it and its two neighbors.
				if (countOfLowestItem < 1 || countOfLowestItem > accumulator.size() - 2) { Utils.error("Connectives cannot be in the first or last positions: " + accumulator); }
				Sentence leftArg  = (Sentence)accumulator.get(countOfLowestItem - 1);
				Sentence rightArg = (Sentence)accumulator.get(countOfLowestItem + 1);
				Sentence cSent    = stringHandler.getConnectedSentence(leftArg, cName, rightArg);
				if (cName.name.equalsIgnoreCase("then")) { cSent = processTHEN((ConnectedSentence) cSent); }
				accumulator.add(   countOfLowestItem + 2, cSent); // Add after the three items being combined.
				accumulator.remove(countOfLowestItem + 1); // Do this in the proper order so shifting doesn't mess up counting.
				accumulator.remove(countOfLowestItem);
				accumulator.remove(countOfLowestItem - 1);
			}
		}

		return (Sentence) accumulator.get(0);
	}

	private Literal processTHEN(ConnectedSentence connSent) throws ParsingException {
		// We need to treat the 'connective' THEN specially.  It is of the form 'P then Q else R' where P, Q, and R need to each convert to one clause.  E.g., (p, q then r, s else x, y, z).
		Sentence          sentenceLeft  = connSent.getSentenceA();
		Sentence          sentenceRight = connSent.getSentenceB();
		Clause            clauseP       = convertSimpleConjunctIntoClause(sentenceLeft, connSent);

		PredicateName pName  = stringHandler.standardPredicateNames.then;
		if (sentenceRight instanceof ConnectedSentence && ConnectiveName.isaOR(((ConnectedSentence) sentenceRight).getConnective().name)) {
			ConnectedSentence sentenceRightConnected = (ConnectedSentence) sentenceRight;
			Clause   clauseQ   = convertSimpleConjunctIntoClause(sentenceRightConnected.getSentenceA(), connSent);
			Clause   clauseR   = convertSimpleConjunctIntoClause(sentenceRightConnected.getSentenceB(), connSent);
			// 'P then Q else R' is implemented as 'dummy :- P, !, Q.' and 'dummy :- R' so create these two clause bodies here.
			clauseP.negLiterals.add(createCutLiteral());
			clauseP.negLiterals.addAll(clauseQ.negLiterals);
			clauseP.setBodyContainsCut(true);
			List<Term> args = new ArrayList<>(2);
			args.add(stringHandler.getSentenceAsTerm(clauseP, "thenInner"));
			args.add(stringHandler.getSentenceAsTerm(clauseR, "thenInner"));
			return   stringHandler.getLiteral(pName, args);
		}
		Clause clauseQ = convertSimpleConjunctIntoClause(sentenceRight, connSent);
		List<Term> args = new ArrayList<>(1);
		clauseP.negLiterals.add(createCutLiteral()); // No need to combine the posLiterals since there should not be any.
		clauseP.negLiterals.addAll(clauseQ.negLiterals);
		clauseP.setBodyContainsCut(true);
		args.add(stringHandler.getSentenceAsTerm(clauseP, "then"));
		return stringHandler.getLiteral(pName, args);
	}

	private Literal createCutLiteral() {
		PredicateName pName = stringHandler.standardPredicateNames.cut;
		return stringHandler.getLiteral(pName);
	}

	private Literal processNegationByFailure(ConnectedSentence connSent) throws ParsingException {
		Clause clause = convertSimpleConjunctIntoClause(connSent.getSentenceB(), connSent); // Remember that for unary 'connectives' the body is sentenceB.
        return stringHandler.getNegationByFailure(clause);
	}

	private String isInfixTokenPredicate(int tokenRead) throws ParsingException {
		switch (tokenRead) {  // If changed, check out checkForPredicateNamesThatAreCharacters (for cases where a single-char string is returned).
		case '\\':
			if (checkAndConsume('=')) {
				if (checkAndConsume('=')) { return "\\=="; }
				return "\\=";
			}
			// if (peekThisChar('+')) { return "\\+"; }  / Allow this to be in-fix?
			return null;
		case '=': // By itself, '=' means unify (and '==' means 'equal').
			if (checkAndConsume('>')) {
				tokenizer.pushBack(); // This is a valid operator, albeit a logical connective.
				return null;
			}
			if (checkAndConsume('<')) {
				return "=<"; // This is Prolog's notation for "<=" (which apparently looks too much like an implication).
			}
            if (checkAndConsume('=')) {
				return "=="; // This is Prolog's notation for "==".
			}
			if (checkAndConsume(':')) {
				if (checkAndConsume('=')) { return "=:="; }
				tokenizer.pushBack(2); // Not sure what '=:' would be though ...
				return null;
			}
			if (checkAndConsume('\\')) {
				if (checkAndConsume('=')) { return "=\\="; }
				tokenizer.pushBack(2); // Not sure what '=\' would be though ...
				return null;
			}
			if (checkAndConsume('.')) {
				if (checkAndConsume('.')) { return "=.."; }
				tokenizer.pushBack();
				return "="; // The following period will cause a problem, but leave that for elsewhere.
			}

            return String.valueOf((char) tokenRead);
		case '<':
			if (checkAndConsume('=') || checkAndConsume('-')) {
				if (checkAndConsume('>')) {
					tokenizer.pushBack(2); // This is a valid operator, albeit a logical connective.
					return null;
				}
				tokenizer.pushBack(1);
			}
		case '>':
			if (checkAndConsume('=')) { return (char) tokenRead + "="; }
			return String.valueOf((char) tokenRead);
		case StreamTokenizer.TT_WORD:
			String tokenString = tokenizer.sval();
			if (tokenString.equalsIgnoreCase("is"))   { return "is";  }
			if (tokenString.equalsIgnoreCase("mod"))  { return "mod"; }
			return null;
		default: return null;	}
	}

	/*
	 * Record that a literal describes a 1D, 2D, or 3D interval.  Example:   isaInterval: ageInRange/3.
	 * The EOL ('.' or ';') is optional.
	 *
	 * In the simplest case, the boundaries for a 1D interval are the 1st and 3rd arguments, for 2D they are 1st, 3rd, 4th, and 6th, and for 3D they are 1st, 3rd, 4th, and 6th, 7th, and 9th.
	 *
	 * This can be overwritten by adding the keyword: boundariesAtEnd
	 * - in this case the last 2 (for 1D, last 4 for 2D and last 6 for 3D) are assumed to be the boundaries.
	 *
	 * Also if the number of arguments is not 3x the number of dimensions, then can use one of these keywords:
	 * 			1D
	 * 			2D
	 * 			3D
	 *
	 * @param tokenizer
	 * @throws ParsingException
	 */
	private void processISAInterval() throws ParsingException, IOException {
		// Have already read the 'isaInterval:"
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
		if (tokenRead == StreamTokenizer.TT_WORD) {
			String currentWord = tokenizer.sval();
			PredicateName pName = stringHandler.getPredicateName(currentWord);
			tokenRead = getNextToken();
			if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in an isaInterval specification, but got: '" + reportLastItemRead() + "'."); }
			int arity = readInteger();
			int dimensions = arity / 3; // Integer division is the default.
			getNextToken();
			boolean boundariesAtEnd = false; // The default is the first and the last argument are the boundaries in the 1D case, and in 2D it is 1st, 3rd, 4th, and 6th, while in 3D it is 1st, 3rd, 4th, 6th,7th, and 9th.
			while (!atEOL()) {
				String nextTokenAsString = tokenizer.reportCurrentToken();
				if      (nextTokenAsString.equalsIgnoreCase("boundariesAtEnd")) { boundariesAtEnd = true; }
				else if (nextTokenAsString.equalsIgnoreCase("1D"))              { dimensions      = 1;    }  // If multiple specifications, simply take the last.
				else if (nextTokenAsString.equalsIgnoreCase("2D"))              { dimensions      = 2;    }
				else if (nextTokenAsString.equalsIgnoreCase("3D"))              { dimensions      = 3;    }
				getNextToken();
			}
			switch (dimensions) {
				case 1: pName.setIsaInterval_1D(arity, boundariesAtEnd); stringHandler.needPruner = true; break;
				case 2: pName.setIsaInterval_2D(arity, boundariesAtEnd); stringHandler.needPruner = true; break;
				case 3: pName.setIsaInterval_3D(arity, boundariesAtEnd); stringHandler.needPruner = true; break;
				default: throw new ParsingException("Can only handle 1, 2, or 3D interval specifications (which involve 3, 6, or 9 arguments, respectively), but have read arity =: '" + arity + ".");
			}
			return;
		}
		throw new ParsingException("Expecting the name of a predicate in an 'isaInterval' but read: '" + reportLastItemRead() + "'.");
	}

	// TODO - clean this up
	private int checkForPredicateNamesThatAreCharacters(int tokenRead) throws ParsingException, IOException {
		if (!isaPossibleTermName(tokenRead)) {
			String seeIfInfixPred = isInfixTokenPredicate(tokenRead);
			if (seeIfInfixPred == null) {
				throw new ParsingException("Expecting a predicate name but read: '" + reportLastItemRead() + "'.");
			}
			if ("=".equals(seeIfInfixPred)) {
				return tokenRead;
			}
			tokenizer.pushBack(seeIfInfixPred); // Hopefully no prevToken called here ...
			return getNextToken();
		}
		String seeIfPredNameUsingCharacters = getPredicateOrFunctionName(tokenRead);
		if (seeIfPredNameUsingCharacters != null) {
			if        ("-".equals(seeIfPredNameUsingCharacters)) {
				return tokenRead;
			} else if ("+".equals(seeIfPredNameUsingCharacters)) {
				return tokenRead;
			} else {
				tokenizer.pushBack(seeIfPredNameUsingCharacters); // Hopefully no prevToken called here ...
			}
			return getNextToken();
		}
		return tokenRead;
	}

	/*
	 * Process something like:  relevant: p/2, RELEVANT;
	 * These automatically create 'cost' statements as well.
	 * Read documentation above for all the isVariant supported.
	 */
	private void processRelevant(List<Sentence> listOfSentences) throws ParsingException, IOException {
		// Have already read the 'relevant:"
		Literal headLit = null;
		int tokenRead = getNextToken();
		if (tokenRead == '[') {
			tokenizer.pushBack();
			processRelevantAND(null, listOfSentences, false);
			return;
		}
		tokenRead = checkForPredicateNamesThatAreCharacters(tokenRead);

		if (tokenRead == StreamTokenizer.TT_WORD) {
			String currentWord = tokenizer.sval();

			if (currentWord.equalsIgnoreCase("head")) {
				headLit = readEqualsTypedLiteral();
				checkAndConsume(',');
				tokenRead = getNextToken();
				if (tokenRead == '[') {
					tokenizer.pushBack();
					processRelevantAND(headLit, listOfSentences, false);
					return;
				}
				tokenRead = checkForPredicateNamesThatAreCharacters(tokenRead);  // TODO clean up this duplicated code.
				if (tokenRead == StreamTokenizer.TT_WORD) {
					currentWord = tokenizer.sval();
				} else { throw new ParsingException("Expecting a string token but read " + reportLastItemRead() + "."); }
			}

			if (currentWord.equalsIgnoreCase("AND")) {
				expectAndConsume('(');
				processRelevantAND(headLit, listOfSentences, true);
				return;
			}
			if (currentWord.equalsIgnoreCase("OR")) {
				expectAndConsume('(');
				processRelevantOR(headLit, listOfSentences);
				return;
			}
			if (currentWord.equalsIgnoreCase("NOT")) {
				processRelevantNOT(headLit, listOfSentences);
				return;
			}
			if (headLit != null) { throw new ParsingException("A 'head' literal before a plain literal in a 'relevance' will be ignored: " + headLit); } // Could handle this if it seemed necessary.

			if (checkAndConsume('(')) { // Have a literal, rather than something like 'pred/2'
				tokenizer.pushBack();
				tokenizer.pushBack();
				processRelevantLiteral(listOfSentences);
				return;
			}
			if (checkAndConsume('/')) { // Have something like 'pred/2'
				processRelevantLiteralSpec(currentWord);
				return;
			}
			return;
		}

		throw new ParsingException("Expecting the name of a predicate in a 'relevant' but read: '" + reportLastItemRead() + "'.");
	}

	private void processSupporter() throws ParsingException, IOException {
		// Have already read the 'supportingLiteral:"
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
		if (tokenRead == StreamTokenizer.TT_WORD) {
			String currentWord = tokenizer.sval();
			PredicateName pName = stringHandler.getPredicateName(currentWord);
			tokenRead = getNextToken();
			if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in an 'supportingLiteral' specification, but got: '" + reportLastItemRead() + "'."); }
			int arity = readInteger();
			pName.markAsSupportingPredicate(arity, false);
			return;
		}
		throw new ParsingException("Expecting the name of a predicate in a 'supportingLiteral' but read: '" + reportLastItemRead() + "'.");
	}

	private RelevanceStrength readRelevanceStrength() throws ParsingException, IOException {
		int    tokenRead;
		String currentWord;
		if (peekEOL(true)) {
			return RelevanceStrength.getDefaultRelevanceStrength();
		}
		checkAndConsume(','); // OK if there is a commas separating the items.
		tokenRead = getNextToken();

		if (tokenRead == '@') {  // A leading # indicates the value needs to be looked up in the list of set parameters.
			getNextToken();
			String wordRead = tokenizer.sval();
			String setting  = stringHandler.getParameterSetting(wordRead);
			if (setting == null) { throw new ParsingException(" Read '@" + wordRead + "', but '" + wordRead + "' has not been set."); }
			return RelevanceStrength.getRelevanceStrengthFromString(setting);
		}
		if (tokenRead == StreamTokenizer.TT_WORD) {
			currentWord = tokenizer.sval();
			if (currentWord.equalsIgnoreCase("max") || currentWord.equalsIgnoreCase("maxPerInputVars")) { // No relevance provided.  Use default.
				tokenizer.pushBack();
				return RelevanceStrength.getDefaultRelevanceStrength();
			}
			return RelevanceStrength.getRelevanceStrengthFromString(currentWord);
		}
		throw new ParsingException("Expecting a RelevanceStrength in a 'relevance:' but read: '" + reportLastItemRead() + "'.");
	}

	private List<Term> getArgumentsToAND(boolean needCloseParen) throws ParsingException, IOException {
		if ( checkAndConsumeToken("[")) { // Allow an implicit AND represented as a list of terms.
			if (needCloseParen) { throw new ParsingException("Should not need a closing parenthesis here."); }
			ConsCell list = processList(false, 1, false); // Should suck up the closing ']'.
			if (list == null)   { throw new ParsingException("Should not have list=null here."); }
			return list.convertConsCellToList();
		}
        else if(checkAndConsumeToken("(")) { // Allow an implicit AND represented as a list of terms.
			if (needCloseParen) { throw new ParsingException("Should not need a closing parenthesis here."); }
			ConsCell list = processList(false, 1, false); // Should suck up the closing ']'.
			if (list == null)   { throw new ParsingException("Should not have list=null here."); }
			return list.convertConsCellToList();
		}
        else if(needCloseParen) {
			return processListOfTerms('(', false).getTerms();
		}
        else {
            throw new ParsingException("Expecting a '['");
        }
	}

	// TODO - clean up common code in these four processRelevant*'s.
	private void processRelevantAND(Literal typedHeadLiteral, List<Sentence> listOfSentences, boolean needCloseParen) throws ParsingException, IOException {
        int        max              = Integer.MAX_VALUE;
        int        maxPerInputVars  = Integer.MAX_VALUE;
		boolean    autoNegate       = true;
        List<Term> bodyTerms        = getArgumentsToAND(needCloseParen);
		RelevanceStrength  strength = readRelevanceStrength();

		int tokenRead = (atEOL() ? 0 : getNextToken());
		while (!atEOL()) { // Have some optional arguments since not yet at EOL.
			String currentWord = tokenizer.reportCurrentToken();
			if (tokenRead == ',') {  } // OK if there are some commas separating the items.
			else if (currentWord.equalsIgnoreCase("max")) { // BUG: the user can't use 'max' nor 'maxPerInputVars' as target predicates.  TODO fix
				if (max < Integer.MAX_VALUE) { throw new ParsingException("Have already read max=" + max + " when processing a 'relevant' and have encountered 'max' again."); }
				max             = readEqualsInteger();
			} else if (currentWord.equalsIgnoreCase("maxPerInputVars")) {
				if (maxPerInputVars < Integer.MAX_VALUE) { throw new ParsingException("Have already read maxPerInputVars=" + max + " when processing a 'relevant' and have encountered 'maxPerInputVars' again."); }
				maxPerInputVars = readEqualsInteger();
			} else if (currentWord.equalsIgnoreCase("head")) {
				if (typedHeadLiteral != null) { throw new ParsingException("Have already read a head =" + typedHeadLiteral + " when processing a 'relevant' and have encountered another."); }
				typedHeadLiteral = readEqualsTypedLiteral();
			} else if (currentWord.equalsIgnoreCase("noAutoNegate")) { // Fine if this is read more than once.
				autoNegate = false;
			} else if (currentWord.equalsIgnoreCase("autoNegate"))   { // Fine if this is read more than once.
				autoNegate = true;
			}
			tokenRead = getNextToken();
        }
		if (strength != null && strength.isLessThanNeutral()) { autoNegate = false; }

		List<TypeSpec> typeSpecs    = new ArrayList<>(4);
		List<Term>     terms        = (typedHeadLiteral == null ? bodyTerms : typedHeadLiteral.getArguments());
		PredicateName  newPname     = (typedHeadLiteral == null ? stringHandler.getPredicateNameNumbered("anonymousAND_WI") : typedHeadLiteral.predicateName);
		if (typedHeadLiteral == null) {
			List<Variable> freeVars     = new ArrayList<>(4);
			List<String>   freeVarNames = new ArrayList<>(4);

			stringHandler.getTypedFreeVariablesAndUniquelyName(terms, null, freeVars, freeVarNames, typeSpecs, true);		// These will not maintain the World-State positions since the arguments names are probably not in the file being read.
			typedHeadLiteral = stringHandler.getLiteral(newPname, convertToListOfTerms(freeVars), freeVarNames).clearArgumentNamesInPlace(); // BUGGY if we want to keep argument names ...
		} else {
			typeSpecs = typedHeadLiteral.getTypeSpecs();
		}
		int   arity = typedHeadLiteral.numberArgs();
		Clause newC = stringHandler.getClause(typedHeadLiteral, true);

		newC.negLiterals = new ArrayList<>(1);
		for (Term term : bodyTerms) {
			if        (term instanceof Function) {
				newC.negLiterals.add(( (Function) term).convertToLiteral(stringHandler));
			} else if (term instanceof StringConstant) { // Convert this to a zero-arity literal.
				newC.negLiterals.add( stringHandler.getLiteral( stringHandler.getPredicateName(( (StringConstant) term).getName())));
			} else { throw new Error("Cannot handle this term in processRelevantAND" + term); }
		}

		newPname.addInliner(arity);
		stringHandler.setRelevance(newPname, arity, strength);
		stringHandler.recordModeWithTypes(typedHeadLiteral, stringHandler.getConstantSignatureThisLong(arity), typeSpecs, max, maxPerInputVars);
		if (listOfSentences == null) { throw new ParsingException("Should not have an empty list!"); } // This holds the read-in clauses.  If reset here, the new list will be lost.
		listOfSentences.add(newC);
		stringHandler.resetAllVariables();
		if (autoNegate) {
			Literal nottypedHeadLiteral = createNegatedVersion(typedHeadLiteral);
			processRelevantNOT(listOfSentences, nottypedHeadLiteral, typedHeadLiteral, Objects.requireNonNull(strength).getOneLowerStrengthAvoidingNegativeStrengths(), max, maxPerInputVars, false); // Prevent infinite loops.
		}
	}

	private void processRelevantOR(Literal typedHeadLiteral, List<Sentence> listOfSentences) throws ParsingException, IOException {
        int        max              = Integer.MAX_VALUE;
        int        maxPerInputVars  = Integer.MAX_VALUE;
		boolean    autoNegate       = true;
        List<Term> bodyTerms        = processListOfTerms('(', false).getTerms();
		RelevanceStrength  strength = readRelevanceStrength();

		int tokenRead = (atEOL() ? 0 : getNextToken());
		while (!atEOL()) { // Have some optional arguments since not yet at EOL.
			String currentWord = tokenizer.reportCurrentToken();
			if (tokenRead == ',') {  } // OK if there are some commas separating the items.
			else if (currentWord.equalsIgnoreCase("max")) { // BUG: the user can't use 'max' nor 'maxPerInputVars' as target predicates.  TODO fix
				if (max < Integer.MAX_VALUE) { throw new ParsingException("Have already read max=" + max + " when processing a 'relevant' and have encountered 'max' again."); }
				max              = readEqualsInteger();
			} else if (currentWord.equalsIgnoreCase("maxPerInputVars")) {
				if (maxPerInputVars < Integer.MAX_VALUE) { throw new ParsingException("Have already read maxPerInputVars=" + max + " when processing a 'relevant' and have encountered 'maxPerInputVars' again."); }
				maxPerInputVars  = readEqualsInteger();
			} else if (currentWord.equalsIgnoreCase("head")) {
				if (typedHeadLiteral != null) { throw new ParsingException("Have already read a head =" + typedHeadLiteral + " when processing a 'relevant' and have encountered another."); }
				typedHeadLiteral = readEqualsTypedLiteral();
			} else if (currentWord.equalsIgnoreCase("noAutoNegate")) { // Fine if this is read more than once.
				autoNegate = false;
			} else if (currentWord.equalsIgnoreCase("autoNegate"))   { // Fine if this is read more than once.
				autoNegate = true;
			}
			tokenRead = getNextToken();
        }
		if (strength != null && strength.isLessThanNeutral()) { autoNegate = false; }

		boolean typedHeadLiteralWasNULL = (typedHeadLiteral == null);
		List<TypeSpec> typeSpecs    = new ArrayList<>(4);
        List<Term>     terms        = (typedHeadLiteralWasNULL ? bodyTerms : typedHeadLiteral.getArguments());
        PredicateName  newPname     = (typedHeadLiteralWasNULL? stringHandler.getPredicateNameNumbered("anonymousOR_WI") : typedHeadLiteral.predicateName);

        if (typedHeadLiteral == null) {
			List<Variable> freeVars     = new ArrayList<>(4);
			List<String>   freeVarNames = new ArrayList<>(4);

			stringHandler.getTypedFreeVariablesAndUniquelyName(terms, null, freeVars, freeVarNames, typeSpecs, true);		// These will not maintain the World-State positions since the arguments names are probably not in the file being read.
			typedHeadLiteral = stringHandler.getLiteral(newPname, convertToListOfTerms(freeVars), freeVarNames).clearArgumentNamesInPlace(); // BUGGY if we want to keep argument names ...

		} else {
			typeSpecs = typedHeadLiteral.getTypeSpecs();
		}
		int arity = typedHeadLiteral.numberArgs();

		// Create a P :- Q for each argument to the OR.  P is *not* an in-liner, due to the combinatorics involved.
		// If a term is a LIST such as [Q, R, S] then add P :- Q, R, S.
		// If a term is an AND(P, Q, R), treat the same as it being [Q, R, S].
		for (Term term : bodyTerms) {
			Clause newC = stringHandler.getClause(typedHeadLiteral, true);
			newC.negLiterals = new ArrayList<>(1);
			if        (Function.isaConsCell(term)) {
				List<Term> innerTerms = ((ConsCell) term).convertConsCellToList();
				for (Term inner : innerTerms) {
					newC.negLiterals.add(( (Function) inner).convertToLiteral(stringHandler));
				}
			} else if (term instanceof Function) {
				Function f = (Function) term;
				if (f.functionName == stringHandler.getFunctionName("AND")) {
					if (f.numberArgs() > 0) for (Term inner : f.getArguments()) {
						newC.negLiterals.add(( (Function) inner).convertToLiteral(stringHandler));
					}
				} else {
				newC.negLiterals.add(( (Function) term).convertToLiteral(stringHandler));
				}
			} else if (term instanceof StringConstant) { // Convert this to a zero-arity literal.
				newC.negLiterals.add( stringHandler.getLiteral( stringHandler.getPredicateName(( (StringConstant) term).getName())));
			} else { throw new Error("Cannot handle this term in processRelevantOR" + term); }
			if (listOfSentences == null) { throw new ParsingException("Should not have an empty list!"); }
			listOfSentences.add(newC); // This holds the read-in clauses.
		}
		if (typedHeadLiteralWasNULL) { newPname.markAsSupportingPredicate(arity, false); } // This is NOT inlined, but it is supporting (i.e., it is not a clause-head that is in the BK; instead we generated it).  We need to keep disjuncts around in theories - flattening into clauses could otherwise lead to a combinatorial explosion.
		stringHandler.setRelevance(newPname, arity, strength);
		stringHandler.recordModeWithTypes(typedHeadLiteral, stringHandler.getConstantSignatureThisLong(arity), typeSpecs, max, maxPerInputVars);
		stringHandler.resetAllVariables();
		if (autoNegate) {
			Literal notTypedHeadLiteral = createNegatedVersion(typedHeadLiteral);
			processRelevantNOT(listOfSentences, notTypedHeadLiteral, typedHeadLiteral, Objects.requireNonNull(strength).getOneLowerStrengthAvoidingNegativeStrengths(), max, maxPerInputVars, false); // Prevent infinite loops.
		}
	}

	private void processRelevantNOT(Literal typedHeadLiteral, List<Sentence> listOfSentences) throws ParsingException, IOException {
        int        max              = Integer.MAX_VALUE;
        int        maxPerInputVars  = Integer.MAX_VALUE;
		boolean    autoNegate       = true;
		expectAndConsume('(');
		Literal innerLit = processLiteral(false);
		expectAndConsume(')');
		RelevanceStrength  strength = readRelevanceStrength();

		int tokenRead = (atEOL() ? 0 : getNextToken());
		while (!atEOL()) { // Have some optional arguments since not yet at EOL.
			String currentWord = tokenizer.reportCurrentToken();
			if (tokenRead == ',') {  } // OK if there are some commas separating the items.
			else if (currentWord.equalsIgnoreCase("max")) { // BUG: the user can't use 'max' nor 'maxPerInputVars' as target predicates.  TODO fix
				if (max < Integer.MAX_VALUE) { throw new ParsingException("Have already read max=" + max + " when processing a 'relevant' and have encountered 'max' again."); }
				max             = readEqualsInteger();
			} else if (currentWord.equalsIgnoreCase("maxPerInputVars")) {
				if (maxPerInputVars < Integer.MAX_VALUE) { throw new ParsingException("Have already read maxPerInputVars=" + max + " when processing a 'relevant' and have encountered 'maxPerInputVars' again."); }
				maxPerInputVars = readEqualsInteger();
			} else if (currentWord.equalsIgnoreCase("head")) {
				if (typedHeadLiteral != null) { throw new ParsingException("Have already read a head =" + typedHeadLiteral + " when processing a 'relevant' and have encountered another."); }
				typedHeadLiteral = readEqualsTypedLiteral();
			} else if (currentWord.equalsIgnoreCase("noAutoNegate")) { // Fine if this is read more than once.
				autoNegate = false;
			} else if (currentWord.equalsIgnoreCase("autoNegate"))   { // Fine if this is read more than once.
				autoNegate = true;
			} else { throw new Error("Cannot handle this in processRelevantNOT: " + currentWord); }
			tokenRead = getNextToken();
        }
		if (strength != null && strength.isLessThanNeutral()) { autoNegate = false; }
		processRelevantNOT(listOfSentences, typedHeadLiteral, innerLit, strength, max, maxPerInputVars, autoNegate);
	}

	private void processRelevantNOT(List<Sentence> listOfSentences, Literal typedHeadLiteral, Literal innerLit, RelevanceStrength strength, int max, int maxPerInputVars, boolean createNegatedVersion) throws ParsingException, IOException {
		List<TypeSpec> typeSpecs         = new ArrayList<>(4);
		List<Term>     terms             = (typedHeadLiteral == null ? innerLit.getArguments() : typedHeadLiteral.getArguments());
		PredicateName  newPname          = (typedHeadLiteral == null ? stringHandler.getPredicateNameNumbered(will_notPred_prefix + innerLit.predicateName.name) : typedHeadLiteral.predicateName);

		if (typedHeadLiteral == null) {
			List<Variable> freeVars     = new ArrayList<>(4);
			List<String>   freeVarNames = new ArrayList<>(4);

			stringHandler.getTypedFreeVariablesAndUniquelyName(terms, null, freeVars, freeVarNames, typeSpecs, true);		// These will not maintain the World-State positions since the arguments names are probably not in the file being read.
			typedHeadLiteral = stringHandler.getLiteral(newPname, convertToListOfTerms(freeVars), freeVarNames).clearArgumentNamesInPlace(); // BUGGY if we want to keep argument names ...
		} else {
			typeSpecs = typedHeadLiteral.getTypeSpecs();
		}
		int     arity = typedHeadLiteral.numberArgs();
		Clause  newC  = stringHandler.getClause(typedHeadLiteral, true);
		Literal notP  = stringHandler.wrapInNot(innerLit);

		newC.negLiterals = new ArrayList<>(1);
		newC.negLiterals.add(notP);
		newPname.addInliner(arity);
		stringHandler.setRelevance(newPname, arity, strength);
		stringHandler.recordModeWithTypes(typedHeadLiteral, stringHandler.getConstantSignatureThisLong(arity), typeSpecs, max, maxPerInputVars);
		if (listOfSentences == null) { throw new ParsingException("Should not have an empty list!"); }
		listOfSentences.add(newC); // This holds the read-in clauses.
		stringHandler.resetAllVariables();
		if (createNegatedVersion) { processRelevantLiteral(listOfSentences, innerLit, strength.getOneLowerStrengthAvoidingNegativeStrengths(), max, maxPerInputVars, false); } // Prevent infinite loops.
	}

    private void processRelevantLiteral(List<Sentence> listOfSentences) throws ParsingException, IOException {
        int max = Integer.MAX_VALUE;
        int maxPerInputVars = Integer.MAX_VALUE;
        boolean autoNegate = true;
        Literal innerLit = processLiteral(true);

        int tokenRead = (atEOL() ? 0 : getNextToken());
		tokenizer.reportCurrentToken();
		String currentWord;

        RelevanceStrength strength = readRelevanceStrength();
        while (!atEOL()) { // Have some optional arguments since not yet at EOL.
            currentWord = tokenizer.reportCurrentToken();
            if (tokenRead == ',') {

            } // OK if there are some commas separating the items.
            else if (currentWord.equalsIgnoreCase("max")) { // BUG: the user can't use 'max' nor 'maxPerInputVars' as target predicates.  TODO fix
                if (max < Integer.MAX_VALUE) {
                    throw new ParsingException("Have already read max=" + max + " when processing a mode and have encountered 'max' again.");
                }
                max = readEqualsInteger();
            }
            else if (currentWord.equalsIgnoreCase("maxPerInputVars")) {
                if (maxPerInputVars < Integer.MAX_VALUE) {
                    throw new ParsingException("Have already read maxPerInputVars=" + max + " when processing a mode and have encountered 'maxPerInputVars' again.");
                }
                maxPerInputVars = readEqualsInteger();
            }
            else if (currentWord.equalsIgnoreCase("noAutoNegate")) { // Fine if this is read more than once.
                autoNegate = false;
            }
            else if (currentWord.equalsIgnoreCase("autoNegate")) { // Fine if this is read more than once.
                autoNegate = true;
            }
            else {
                throw new Error("Cannot handle this in processRelevantLiteral: " + currentWord);
            }
            tokenRead = getNextToken();
        }
        if (strength != null && strength.isLessThanNeutral()) {
            autoNegate = false;
        }
		processRelevantLiteral(listOfSentences, innerLit, strength, max, maxPerInputVars, autoNegate);


	}

	private void processRelevantLiteral(List<Sentence> listOfSentences, Literal innerLit, RelevanceStrength  strength, int max, int maxPerInputVars, boolean createNegatedVersion) throws ParsingException, IOException {
		int           arity = innerLit.numberArgs();
		PredicateName pName = innerLit.predicateName;

		stringHandler.setRelevance(pName, arity, strength);

		if (createNegatedVersion) { processRelevantNOT(listOfSentences, null, innerLit, strength, max, maxPerInputVars, false); } // Prevent infinite loops.
	}

	private void processRelevantLiteralSpec(String predicateNameAsString) throws ParsingException, IOException {
		int               arity    = readInteger();
		RelevanceStrength strength = readRelevanceStrength();
		stringHandler.setRelevance(stringHandler.getPredicateName(predicateNameAsString), arity, strength);
		peekEOL(true); // These cannot have additional information since we don't have the arguments.
	}

    private void processLiteralAlias() throws ParsingException, IOException {
        Literal alias = processLiteral(true);

        expectAndConsumeToken("=>");

        Literal example = processLiteral(true);

        stringHandler.addLiteralAlias(alias, example);
    }

	private void processRelevantLiteralNew(List<Sentence> listOfSentences) throws ParsingException, IOException {

        Literal exampleLiteral;

        if ( checkAndConsumeToken("@") ) {
            exampleLiteral = processLiteral(true);
            exampleLiteral = stringHandler.lookupLiteralAlias(exampleLiteral);
        }
        else {
            exampleLiteral = processLiteral(true);
        }

        expectAndConsumeToken(":");

        Literal relevantLiteral = processLiteral(true);

        expectAndConsumeToken(",");

        RelevanceStrength strength = readRelevanceStrength();

        Literal relevanceFact = stringHandler.getLiteral("relevant_literal", exampleLiteral.convertToFunction(stringHandler), relevantLiteral.convertToFunction(stringHandler), stringHandler.getStringConstant(strength.name()));

        listOfSentences.add(relevanceFact);
    }

	private void processNonOperational() throws IOException {
        PredicateNameAndArity pnaa = processPredicateNameAndArity();

        while(!checkToken(".") && !atEOL()) {
            checkAndConsumeToken(",");
            if ( checkAndConsumeToken("operational") ) {
                expectAndConsumeToken("=");
                PredicateName predicateName = processPredicateName();

                pnaa.getPredicateName().addOperationalExpansion(predicateName, pnaa.getArity());
            }
            else {
                throw new ParsingException("Error parsing nonOperational expression:  Unexpected toke '" + tokenizer.reportCurrentToken() +"'.");
            }
        }

    }

    private void processContainsCallables() throws IOException, ParsingException {
        PredicateNameAndArity pnaa = processPredicateNameAndArity();

        pnaa.setContainsCallable();
    }

    /* Returns true  if the next token is tokenToEval and consume it if it is.
     *
     * If the token doesn't match tokenToEval, the token isn't consumed.
     *
     * @param tokenToEval Token to look for.
     * @return True if next token = tokenToEval.  False otherwise.
     */
    private boolean checkAndConsumeToken(String tokenToEval) throws ParsingException, IOException {
        if (atEOL()) {
            return false;
        }

		getNextToken();
        String currentWord = tokenizer.reportCurrentToken();

        if (currentWord.equals(tokenToEval)) {
            return true;
        }
        else {
            tokenizer.pushBack();
            return false;
        }
    }

    /* Returns true if the next token is tokenToEval but does not consume it.
     *
     * @param tokenToEval Token to look for.
     * @return True if next token = tokenToEval.  False otherwise.
     */
    private boolean checkToken(String tokenToEval) throws ParsingException, IOException {
        if (atEOL()) {
            return false;
        }

		getNextToken();
        String currentWord = tokenizer.reportCurrentToken();
        tokenizer.pushBack();

		return currentWord.equals(tokenToEval);
    }

    /* Reads the next token,makes sure it is tokenToEval, and consumes it.
     *
     * @param tokenToEval Expected next token.
     * @throws ParsingException Thrown if the next token is not tokenToEval.
     */
    private void expectAndConsumeToken(String tokenToEval) throws ParsingException, IOException {
        boolean done = false;
        while(!done) {

			if ( atEOL()  ) throw new ParsingException("Unexpected end of file.  Expected '" + tokenToEval + "'." );

			getNextToken();
			String currentWord = tokenizer.reportCurrentToken();

			if (!tokenToEval.startsWith(currentWord)) {
				throw new ParsingException("Unexpected token '" + currentWord + "'.  Expected '" + tokenToEval + "'." );
			}
			else if ( tokenToEval.length() != currentWord.length()) {
				tokenToEval = tokenToEval.substring(currentWord.length());
			}
			else {
				done = true;
			}
        }
    }

    private PredicateNameAndArity processPredicateNameAndArity() throws IOException {
        String predicateName = getPredicateOrFunctionName(tokenizer.nextToken());

        expectAndConsumeToken("/");

        int arity = (int)processNumber(tokenizer.nextToken());

        return new PredicateNameAndArity(stringHandler.getPredicateName(predicateName), arity);
    }

    private PredicateName processPredicateName() throws IOException {
        String predicateName = getPredicateOrFunctionName(tokenizer.nextToken());
        return stringHandler.getPredicateName(predicateName);
    }

	private Literal createNegatedVersion(Literal lit) {
		Literal result = lit.copy(false); // Do not want new variables here (or will need to match up to rest of clause).
		String candidateName = will_notPred_prefix + lit.predicateName.name;
		result.predicateName = stringHandler.getPredicateNameNumbered(candidateName); // Watch for name conflicts.
		if (!result.predicateName.name.equalsIgnoreCase(candidateName)) {
			Utils.warning("Needed to use '" + result.predicateName + "' because '" + candidateName + "' already existed.");
		}
		return result;
	}

	/*
	 * Process something like:  cost: p/2, 1.5;
	 * Such costs can be used when scoring clauses (default cost is 1.0).
	 */
	private void processCost() throws ParsingException, IOException {
		// Have already read the 'cost:"
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());

		if (tokenRead == StreamTokenizer.TT_WORD) {
			String currentWord = tokenizer.sval();
			PredicateName pName = stringHandler.getPredicateName(currentWord);
			tokenRead = getNextToken();
			if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in an 'cost' specification, but got: '" + reportLastItemRead() + "'."); }
			int arity = readInteger();

			checkAndConsume(','); // OK if there is a commas separating the items.

			tokenRead = getNextToken();
			double cost = processNumber(tokenRead);
			pName.setCost(arity, cost, false);
			return;
		}
		throw new ParsingException("Expecting the name of a predicate in a 'cost' but read: '" + reportLastItemRead() + "'.");
	}

	private void processDirective(String directiveName) throws ParsingException, IOException {
		// Have already read something like 'okIfUnknown:" (the colon isn't passed in).
		if (directiveName == null) { throw new ParsingException("Cannot pass in directiveName=null."); } // This is a programmer, rather than user, error.
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
		if (tokenRead == StreamTokenizer.TT_WORD) {
			String currentWord = tokenizer.sval();
			PredicateName pName = stringHandler.getPredicateName(currentWord);
			tokenRead = getNextToken();
			if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a '" + directiveName + "' specification, but got: '" + reportLastItemRead() + "'."); }
			if (checkAndConsume('#')) {
				if      (directiveName.equalsIgnoreCase("okIfUnknown"))                    { pName.setCanBeAbsent(-1); } // -1 means "any arity"
				else if (directiveName.equalsIgnoreCase("dontComplainAboutMultipleTypes")) { pName.setDontComplainAboutMultipleTypes(-1); }
				else { throw new ParsingException("Cannot process directiveName=" + directiveName+ "."); } // This is a programmer, rather than user, error.
			}
			else {
				int arity = readInteger();
				if (directiveName.equalsIgnoreCase("okIfUnknown"))                         { pName.setCanBeAbsent(arity); }
				else if (directiveName.equalsIgnoreCase("dontComplainAboutMultipleTypes")) { pName.setDontComplainAboutMultipleTypes(arity); }
				else { throw new ParsingException("Cannot process directiveName=" + directiveName+ "."); } // This is a programmer, rather than user, error.
			}
			peekEOL(true);
			return;
		}
		throw new ParsingException("Expecting the name of a predicate in a '" + directiveName + "' but read: '" + reportLastItemRead() + "'.");
	}

	/*
	 * Process the specification of a Horn ('definite' actually) clause that
	 * should be precomputed. For example: precompute: p(x) :- q(x, y), r(y).
	 */
	private void processPrecompute(int index) throws ParsingException, IOException {
		String fileNameToUse;
		getNextToken();
		int tokenRead;
		String currentWord = tokenizer.reportCurrentToken();
		
		boolean usingDefaultName = false;
		if ("fileName".equalsIgnoreCase(currentWord)) {
			tokenRead = getNextToken();			
			if (tokenRead != '=') { throw new ParsingException("Expecting an '=' but got: " + reportLastItemRead() + "."); }
			tokenRead = getNextToken();
			boolean quoted = atQuotedString(tokenRead);

			if (tokenRead == StreamTokenizer.TT_WORD || quoted) {
				fileNameToUse = (quoted ? tokenizer.svalQuoted() : tokenizer.sval());
				if (!quoted && checkAndConsume('.')) { // See if there is an extension.
					int lineNumber = tokenizer.lineno();
					tokenRead = getNextToken(false); // How do we distinguish if there is an '.' as a EOL or if it is a delimiter in a file name?  Use the line number as a hack?
					if (tokenRead == StreamTokenizer.TT_EOF || lineNumber != tokenizer.lineno()) {	 // Done.
						throw new ParsingException("Expecting the file name of a file in which to place the precomputed results, but reached EOF.");
					}
					if (tokenRead != StreamTokenizer.TT_WORD) {
						tokenizer.pushBack(2); // The period is apparently an (logical) EOL since something that isn't text follows.
					} else { fileNameToUse += "." + tokenizer.sval(); }
				}
			} else {
				throw new ParsingException("Expecting the file name of a file in which to place the precomputed results, but read:\n '" + reportLastItemRead() + "'.");
			}
			checkAndConsume(','); // Allow an optional comma.
		} else {
			tokenizer.pushBack(1);
			fileNameToUse = "precomputed" + (index > 0 ? index : "");
			usingDefaultName = true;
		}
		
		Sentence sentenceToPrecompute = processFOPC_sentence(0);
		if (sentencesToPrecompute == null) { initializeSentencesToPrecompute(); }
		sentencesToPrecompute[index].add(sentenceToPrecompute);
		setFileNameForSentencesToPrecompute(index, fileNameToUse, usingDefaultName);
	}

	private void initializeSentencesToPrecompute() {
		sentencesToPrecompute = (List<Sentence>[]) new List<?>[getNumberOfPrecomputeFiles()];
		sentencesToPrecomputeFileNameToUse = new String[getNumberOfPrecomputeFiles()];
		for (int i = 0; i < getNumberOfPrecomputeFiles(); i++) { sentencesToPrecompute[i] = new ArrayList<>(4); sentencesToPrecomputeFileNameToUse[i] = null; }
	}

	/*
	 *  prune: prunableLiteral,    // If a literal that unifies with 'ifPresentLiteral' is in already in a clause being learned,
	 *         ifPresentLiteral,   // do not add something that also unifies with 'prunableLiteral' - the commas and the final '.' (or ';') are optional.
	 *         [warnIf(N)]         // The optional third argument says to complain if there are N or more existing rules whose head unifies with 'ifPresentLiteral' since this pruning is based on the assumption that less than N such rules exist (i.e., the 'precompute:' facility assumes N=1).
	 */
	private void processPrune(int truthValue) throws ParsingException, IOException {  // TruthValue: -1 means 'prune because false', 1 means because true, and 0 means unknown.
		Literal prunableLiteral  = processLiteral(false);
		String commaOne = " ";
		if (checkAndConsume(',')) { commaOne = ", "; } // Commas are optional.
		if (peekEOL(false)) { // Have something like "prune: f(x,x)."
			prunableLiteral.predicateName.recordPrune(prunableLiteral,  null, -1, truthValue);
			return;
		}
		Literal ifPresentLiteral = processLiteral(false);
		String commaTwo = " ";
		if (checkAndConsume(',')) { commaTwo = ", "; } // Commas are optional.
		if (!commaTwo.equalsIgnoreCase(" ") || !peekEOL(true)) {
			Literal warnLiteral = processLiteral(false);
			if (warnLiteral != null && warnLiteral.predicateName == stringHandler.getPredicateName("warnIf") && warnLiteral.numberArgs() == 1) {
				  // TODO(?):   Process 'prune: " + prunableLiteral + commaOne + ifPresentLiteral + commaTwo + warnLiteral + "'.");
				  Term term = warnLiteral.getArgument(0);
				  if (term instanceof NumericConstant) {
					  int n = ((NumericConstant) term).value.intValue(); // Use the integer value regardless (enough thrown exceptions already ...).
					  stringHandler.needPruner = true;
					  prunableLiteral.predicateName.recordPrune(prunableLiteral, ifPresentLiteral, n, truthValue);
				  }
				  else { throw new ParsingException("Read '" + warnLiteral + "' after 'prune: " + prunableLiteral + commaOne + ifPresentLiteral + commaTwo + "' and was expecting that the argument to 'warnIf(N)' be a number."); }
			}
			else { throw new ParsingException("Read '" + warnLiteral + "' after 'prune: " + prunableLiteral + commaOne + ifPresentLiteral + commaTwo + "' and was expecting 'warnIf(N)'."); }
			peekEOL(true);
		}
		else {
			stringHandler.needPruner = true;
			prunableLiteral.predicateName.recordPrune(prunableLiteral, ifPresentLiteral, Integer.MAX_VALUE, truthValue);
		}
	}

	private Sentence processWeight(int followingChar) throws ParsingException, IOException {
		boolean openParens = false;
		Sentence sentence;
		switch (followingChar) {
			case '(':
			case '{':
			case '[':
				openParens = true;
			case ':':
			case '=':
				double   wgt      = readWeight();
				if (openParens) {
					int nextToken = getNextToken();
					if (nextToken != ')' && nextToken != '}' && nextToken != ']') { // If the parenthesis isn't closed, assume of the form: '(wgt FOPC)'
						checkAndConsume(',');  // A comma after the number is optional.
						sentence = processFOPC_sentence(1);
					}
					else {
						checkAndConsume(',');
						sentence = processFOPC_sentence(0);
					}
				}
				else {
					    checkAndConsume(',');
					    sentence = processFOPC_sentence(0);
				}
				sentence.setWeightOnSentence(wgt);
				return sentence;
			default: throw new ParsingException("After 'weight' or 'wgt' expected one of {':', '=', '(', '{'} but read: '" + reportLastItemRead() + "'.");
		}
	}

	private double readWeight() throws ParsingException, IOException {
		int tokenRead = getNextToken();
		double result = processNumber(tokenRead);
		if (Utils.isaNumber(result)) { // If here, cannot read as an integer (nor as a double).
			return result;
		}
		throw new ParsingException("Was trying to read a number but failed on: '" + reportLastItemRead() + "'.");
	}

	private boolean atInfinity() {
		String currentWord = tokenizer.reportCurrentToken();
		boolean result = (currentWord.equalsIgnoreCase("inf") || currentWord.equalsIgnoreCase("infinity"));

		if (result && checkAndConsume('(')) { // Allow inf() to be a predicate.
			tokenizer.pushBack();
			return false;
		}
		return result;
	}

	private double processNumber(int tokenRead) throws ParsingException, IOException {
		int countOfBackupsNeeded = 0;
		int negate               = 1;
		if (tokenRead == '@') {  // A leading @ indicates the value needs to be looked up in the list of set parameters.
			getNextToken();
			String wordRead = tokenizer.sval();
			String setting  = stringHandler.getParameterSetting(wordRead);
			if (setting     == null) { throw new ParsingException(" Read '@" + wordRead + "', but '" + wordRead + "' has not been set."); }
			return Double.parseDouble(setting);
		} else if (tokenRead == '-')  { // Have a minus sign.
			negate    = -1;
			countOfBackupsNeeded++;
			getNextToken();
			if (atInfinity()) { return Double.NEGATIVE_INFINITY; }
		} else if (tokenRead == '+')  { // Allow a plus sign.
			countOfBackupsNeeded++;
			getNextToken();
			if (atInfinity()) { return Double.POSITIVE_INFINITY; }
		}

		if (tokenizer.ttype() != StreamTokenizer.TT_WORD) {
			tokenizer.pushBack(countOfBackupsNeeded); // Return to where the processNumber() started.
			return Double.NaN;
		}

		String wordRead = tokenizer.sval();
		if (atInfinity()) { return Double.POSITIVE_INFINITY; }
		Long integerConstant = null;
        char firstCharacter = wordRead.charAt(0);
        if ( firstCharacter >= '0' && firstCharacter <= '9') {
            try {  // See if the word read can be viewed as an integer.
                integerConstant = Long.valueOf(wordRead);  // Notice: due to bug mentioned above, we need to handle decimal points ourselves.
                countOfBackupsNeeded = 0; // If integer read w/o problem, then the reads above were fine.
                if (checkAndConsume('.')) {
                    countOfBackupsNeeded++; // For the decimal point.
                    countOfBackupsNeeded++;
                    int nextToken = getNextToken(); // If so, look at the next word.
                    if (nextToken != StreamTokenizer.TT_WORD) { throw new ParsingException("Period is not decimal point."); }
                    String wordRead2 = tokenizer.sval();
                    try {
                        String wordRead3 = "";
                        char lastChar  = wordRead2.charAt(wordRead2.length() - 1);
                        if (lastChar == 'e' || lastChar == 'E') { // If last character is 'e' or 'E' then maybe have scientific notation.
                            countOfBackupsNeeded++;
                            nextToken = getNextToken();
                            switch (nextToken) {
                                case '+':
                                    countOfBackupsNeeded++;
                                    nextToken = getNextToken();
                                    if (nextToken != StreamTokenizer.TT_WORD) { tokenizer.pushBack(countOfBackupsNeeded); throw new ParsingException("Period is not decimal point."); }
                                    wordRead3 = "+" + tokenizer.sval(); break; // Could leave out the "+" but leave it in since the user did ...
                                case '-':
                                    countOfBackupsNeeded++;
                                    nextToken = getNextToken();
                                    if (nextToken != StreamTokenizer.TT_WORD) { tokenizer.pushBack(countOfBackupsNeeded); throw new ParsingException("Period is not decimal point."); }
                                    wordRead3 = "-" + tokenizer.sval(); break;
                                default: throw new NumberFormatException(); // If of the form '2e3' will read all in one fell swoop, so only need to deal with '+' or '-' being "token breakers."
                            }
                        }
                        String doubleAsString = wordRead + "." + wordRead2 + wordRead3;
                        return negate * Double.parseDouble(doubleAsString);
                    }
                    catch (NumberFormatException e) {
                        tokenizer.pushBack(countOfBackupsNeeded); // Push back the word after the decimal point and return the decimal point.
                        return negate * integerConstant; // Then simply return the integer read.
                    }
                }
                return negate * integerConstant;
            }
            catch (NumberFormatException e) { // If here, cannot read as an integer (nor as a double).
                tokenizer.pushBack(countOfBackupsNeeded); // Return to where the processNumber() started.
                return Double.NaN;
            }
            catch (IOException e) { // Tried to read a '.' as a decimal point, whereas it is an EOL followed by an EOF.
                if (e.getMessage().startsWith("Unexpected EOF")) {
                    tokenizer.pushBack(countOfBackupsNeeded); // Push back the EOF.
                    return negate * integerConstant;
                }
                throw new ParsingException("Unexpectedly reached an I/O exception: " + e.getMessage());
            }
            catch (Exception e) { // Tried to read a '.' as a decimal point, whereas it is an EOL.
                if (e.getMessage().startsWith("Period is not decimal point")) {
                    tokenizer.pushBack(countOfBackupsNeeded); // Push back the decimal point, which is an EOL here.  Needed to read PAST the decimal point to make this decision, so need to return TWO tokens here.
                    return negate * integerConstant;
                }
                throw new ParsingException("Unexpected exception dealing with a period: " + e.getMessage());
            }
        }
		tokenizer.pushBack(countOfBackupsNeeded); // Return to where the processNumber() started.
		return Double.NaN;
	}

	private Set<String> loadedLibraries = new HashSet<>(4);

	private List<Sentence> loadThisLibrary(FileParser newParser, String libName) throws ParsingException, IOException {
		if (loadedLibraries.contains(libName)) { return null; } // Already loaded.
		List<Sentence> result;
		loadedLibraries.add(libName);  // TODO - should we store URLs instead?
		URL libraryURL = getClass().getResource("/edu/wisc/cs/will/FOPC_MLN_ILP_Parser/" + libName + ".fopcLibrary");
		if (libraryURL == null) { throw new ParsingException("Unknown library: " + libName); }
		InputStream inStream  = new NamedInputStream(new BufferedInputStream(libraryURL.openStream()), libName + ".fopcLibrary");
		result = newParser.readFOPCstream(null, inStream);
		inStream.close();
		return result;
	}

	/*
	 * Parse the file named after this 'import:' directive. For example:
	 * import: text. The EOL ('.' or ';') at the end is optional.
	 */
	private List<Sentence> processAnotherFile(boolean isaLibraryFile) throws ParsingException, IOException {
		// Have already read the "import:" or "importLibrary:"
		int     nextToken = getNextToken();
		boolean quoted    = atQuotedString(nextToken);
		if (nextToken == StreamTokenizer.TT_WORD || quoted) {
			String newFileName = (quoted ? tokenizer.svalQuoted() : tokenizer.sval());
			if (!quoted && checkAndConsume('.')) { // See if there is an extension.
				int lineNumber = tokenizer.lineno();
				nextToken = getNextToken(true); // How do we distinguish if there is an '.' as a EOL or if it is a delimiter in a file name?  Use the line number as a hack?
				if (nextToken != StreamTokenizer.TT_EOF) { // If EOF, all done.
					if (lineNumber != tokenizer.lineno()) {
						tokenizer.pushBack(); // The period is apparently an (logical) EOL since something that isn't text follows.  Pushback that something.
					} else { newFileName += "." + tokenizer.sval(); }
				}
			}

			if (newFileName.charAt(0) == '@') { newFileName = stringHandler.getParameterSetting(newFileName.substring(1)); }
			newFileName = Utils.replaceWildCards(
					       Objects.requireNonNull(newFileName).replace("IMPORT_VAR1", Utils.removeAnyOuterQuotes(stringHandler.import_assignmentToTempVar1)));
			newFileName =  newFileName.replace("IMPORT_VAR2", Utils.removeAnyOuterQuotes(stringHandler.import_assignmentToTempVar2));
			newFileName =  newFileName.replace("IMPORT_VAR3", Utils.removeAnyOuterQuotes(stringHandler.import_assignmentToTempVar3));
			newFileName =  newFileName.replace("PRECOMP",     Utils.removeAnyOuterQuotes(stringHandler.PRECOMP));
			newFileName =  newFileName.replace("TASK",        Utils.removeAnyOuterQuotes(stringHandler.TASK));
			
			if (!isaLibraryFile && !newFileName.contains(".")) { newFileName += stringHandler.precompute_file_postfix; } //only add extension _after_ doing substitutions

			return loadThisFile(isaLibraryFile, newFileName);
		}
		throw new ParsingException("Expecting the file name of a file to import, but read: '" + reportLastItemRead() + "'.");
	}
	
	private void checkForDefinedImportAndPrecomputeVars() {	// Simply check them all.  TODO - clean up.
		// Precomputes  NOTE: all the parameters checked here must contain "precompute" or "import" or they wont be reached.
		String vStr;
		vStr = stringHandler.getParameterSetting("precomputePrefix");
		if (vStr != null) {                       stringHandler.precompute_file_prefix  = vStr; }
		vStr = stringHandler.getParameterSetting("precomputePostfix");
		if (vStr != null) {                       stringHandler.precompute_file_postfix = vStr; }
		vStr = stringHandler.getParameterSetting("numberOf_precomputes"); // Need this to match: contains("precompute")
		if (vStr != null) {                       setNumberOfPrecomputeFiles(Integer.parseInt(vStr)); }
		vStr = stringHandler.getParameterSetting("precomputeVar1"); // Will replace instances of PRECOMPUTE_VAR1 in files names for precompute outputs.
		if (vStr != null) {                       stringHandler.precompute_assignmentToTempVar1 = Matcher.quoteReplacement(vStr); }
		vStr = stringHandler.getParameterSetting("precomputeVar2");
		if (vStr != null) {                       stringHandler.precompute_assignmentToTempVar2 = Matcher.quoteReplacement(vStr); }
		vStr = stringHandler.getParameterSetting("precomputeVar3");
		if (vStr != null) {                       stringHandler.precompute_assignmentToTempVar3 = Matcher.quoteReplacement(vStr); }	

		// Imports
		vStr = stringHandler.getParameterSetting("importVar1"); // Will replace instances of IMPORT_VAR1 in files names for imported files.
		if (vStr != null) {                       stringHandler.import_assignmentToTempVar1 = Matcher.quoteReplacement(vStr); }
		vStr = stringHandler.getParameterSetting("importVar2");
		if (vStr != null) {                       stringHandler.import_assignmentToTempVar2 = Matcher.quoteReplacement(vStr); }
		vStr = stringHandler.getParameterSetting("importVar3");
		if (vStr != null) {                       stringHandler.import_assignmentToTempVar3 = Matcher.quoteReplacement(vStr); }
		
	}

	private List<Sentence> loadThisFile(boolean isaLibraryFile, String newFileNameRaw) throws ParsingException, IOException {
		String   newFileName = Utils.replaceWildCards(newFileNameRaw);
		FileParser newParser = new FileParser(stringHandler); // Needs to use the same string handler.
		newParser.dontPrintUnlessImportant = dontPrintUnlessImportant;
		if (loadedLibraries != null) { newParser.loadedLibraries.addAll(loadedLibraries); } // Need to know what was already loaded.
        if ( isaLibraryFile ) {
			if (!Utils.isMessageTypeEnabled(PARSER_VERBOSE_LIBRARY_LOADING)) {
				stringHandler.haveLoadedThisFile(newFileName, false);
			}
		}
		List<Sentence> result;
		if (isaLibraryFile) {
			// Don't load a file more than once.
			if (stringHandler.haveLoadedThisFile(newFileName, true)) {
				return null;
			}
			result = loadThisLibrary(newParser, newFileName);
		} else {
			String file2load = Utils.createFileNameString(directoryName, newFileName);
			if (stringHandler.haveLoadedThisFile(file2load, true)) {
				return null;
			}
			result = newParser.readFOPCfile(file2load, false);
		}
		if (newParser.sentencesToPrecompute != null) {
			if (sentencesToPrecompute == null) { initializeSentencesToPrecompute(); }
			for (int i = 0; i < getNumberOfPrecomputeFiles(); i++) {
				List<Sentence> sents = newParser.getSentencesToPrecompute(i);
				if (Utils.getSizeSafely(sents) > 0) { 
					sentencesToPrecompute[i].addAll(sents);
					String newName = newParser.getFileNameForSentencesToPrecompute(i);
					if (newName == null) { Utils.waitHere(" newName = null"); }
					setFileNameForSentencesToPrecompute(i, newName, Objects.requireNonNull(newName).startsWith("precomputed"));
				}
			}
		}
		if (Utils.getSizeSafely(newParser.literalsToThreshold) > 0) {
			if (literalsToThreshold == null) { literalsToThreshold = new HashSet<>(4 + newParser.literalsToThreshold.size()); }
			literalsToThreshold.addAll(newParser.literalsToThreshold);
		}
		if (Utils.getSizeSafely(newParser.loadedLibraries) > 0) {
			if (loadedLibraries == null) { loadedLibraries = new HashSet<>(4 + newParser.loadedLibraries.size()); }
			loadedLibraries.addAll(newParser.loadedLibraries);
		}

		return result;
	}

	// Read two strings and store.
	private void processSetParameter() throws ParsingException, IOException {
		int    tokenRead = getNextToken();
		String parameterName   = getPossiblyQuotedString(tokenRead);

		checkAndConsume('=');
		tokenRead             = getNextToken();
		double resultAsNumber = processNumber(tokenRead);
		if (Utils.isaNumber(resultAsNumber)) {
			if (Math.floor(resultAsNumber) == resultAsNumber) { // See if really an integer.
				stringHandler.recordSetParameter(parameterName, Integer.toString((int) resultAsNumber));
			} else {
				stringHandler.recordSetParameter(parameterName, Double.toString(       resultAsNumber));
			}
		} else {
			String parameterValue = getPossiblyQuotedString(tokenRead);
			stringHandler.recordSetParameter(parameterName, parameterValue);

			// Handle parser strings here.
			if        (parameterName.equalsIgnoreCase("parsingWithNamedArguments")) {
				// Indicates parsing IL ("interlingua") for the BL (Bootstrap Learning) project.
			} else if (parameterName.equalsIgnoreCase("maxWarnings")) {
				maxWarnings               = Integer.parseInt(parameterValue);
			} else if (parameterName.equalsIgnoreCase("variablesStartWithQuestionMarks")) {
				if (Boolean.parseBoolean(parameterValue)) { stringHandler.setVariablesStartWithQuestionMarks(); }
				else                                 { stringHandler.usingPrologNotation(); }
			} else if (parameterName.equalsIgnoreCase("stringsAreCaseSensitive")) {
				stringHandler.setStringsAreCaseSensitive(Boolean.parseBoolean(parameterValue));
			}
            else if (parameterName.equals("duplicateRuleAction")) {
                VariantClauseAction action = VariantClauseAction.fromString(parameterValue);
                if (action == null) {
                    Utils.warning("Illegal value for parameter " + parameterName + ".  Must be one of " + Arrays.toString(VariantClauseAction.values()));
                }
                else {
                    stringHandler.variantRuleHandling = action;
                }
            }
            else if (parameterName.equals("duplicateFactAction")) {
                VariantClauseAction action = VariantClauseAction.fromString(parameterValue);
                if (action == null) {
                    Utils.warning("Illegal value for parameter " + parameterName + ".  Must be one of " + Arrays.toString(VariantClauseAction.values()));
                }
                else {
                    stringHandler.variantFactHandling = action;
                }
            }
		}
		peekEOL(true);
		if (parameterName.contains("precompute") || parameterName.contains("import")) { checkForDefinedImportAndPrecomputeVars(); }
	}

	/*
	 * Process the specification of the range of a type, e.g. 'teenage = 13,
	 * ..., 19.' and 'size = {small, medium, large};' Braces are optional.
	 * The EOL ('.' or ';') is optional IF the braces are present. Note that
	 * DOUBLES currently cannot be types (if they were to be allowed, would
	 * need to require {}'s so the EOL use of ' could be differentiated from
	 * a decimal point.
	 */
	private void processTypeRange() throws ParsingException, IOException {  // TODO handle doubles here but only if in braces.
		int typeNameCode = getNextToken();
		if (typeNameCode != StreamTokenizer.TT_WORD) { Utils.error("Expecting the name of a type, but got: " + reportLastItemRead() + "."); }
		String typeName = tokenizer.sval();
		int tokenRead = getNextToken();
		if (tokenRead != '=') { Utils.error("Expecting '=' but got: " + reportLastItemRead() + "."); }
		boolean needClosingBrace  = false;
		boolean containsDotDotDot = false;
		List<Constant> constants = new ArrayList<>(4);
		tokenRead = getNextToken();
		if (tokenRead == '{') { needClosingBrace = true; tokenRead = getNextToken(); }

		while (tokenRead != '.' && tokenRead != ';' && tokenRead != '}') {
			String constantAsString = tokenizer.sval();
			if (isAllDigits(constantAsString)) {
				constants.add(stringHandler.getNumericConstant(Integer.parseInt(constantAsString)));
			}
			else {
				constants.add(stringHandler.getStringConstant(constantAsString));
			}
			checkForComma();
			tokenRead = getNextToken();
			if (tokenRead == '.') { // See if this is '...'
				if (checkAndConsume('.') && checkAndConsume('.')) {
					if (constants.isEmpty() || !(constants.get(constants.size() - 1) instanceof NumericConstant)) {
						throw new ParsingException("The '...' shorthand needs to follow an integer.  You provided: '" + constants.get(constants.size() - 1) + "'.");
					}
					constants.add(stringHandler.getStringConstant("...")); // Note: multiple '...'s are possible, and they can go "uphill" (e.g., "1, ..., 10") or "down hill" (e.g., "10, ..., 1") - however this code doesn't check for overall sequences that are monotonic, so "1, ..., 10, 90, ..., 11" is valid (thouhg maybe it shoudl not be?).
					containsDotDotDot = true;
					if (!checkAndConsume(',')) { throw new ParsingException("Expecting a comma after '...' in the specification of a range."); }
					tokenRead = getNextToken();
				}
			}
		}
		if (needClosingBrace) {
			if (tokenRead != '}') { throw new ParsingException("Since an open brace ('{') was read, expecting a closing one in the specification of a type range."); }
			peekEOL(true); // Suck up an optional EOL.
		}

		if (containsDotDotDot) {
			List<Constant> expandedConstants = new ArrayList<>(2 * constants.size());
			int previous = Integer.MIN_VALUE;
			int size     = constants.size();
			for (int i = 0; i < size; i++) {
				Constant c = constants.get(i);
				if (c instanceof NumericConstant) {
					previous = ((NumericConstant) c).value.intValue();
					expandedConstants.add(c); // Duplicates are checked elsewhere - don't want to drop them here since that might mess up the use of '...' - e.g., "1, 2, 10, 15, ... 10".
				}
				else if (c instanceof StringConstant && c.equals(stringHandler.getStringConstant("..."))) { // getName().equalsIgnoreCase("...")) {
					if (i == size - 1) { throw new ParsingException("The '...' in a range must be followed by a number."); }
					Constant nextConstant = constants.get(i + 1);
					if (!(nextConstant instanceof NumericConstant))  { throw new ParsingException("The '...' in a range must be followed by an integer.  You provided: '" + nextConstant + "'."); }
					int next = ((NumericConstant) nextConstant).value.intValue();

					if (Math.abs(next - previous) > 2000) { throw new ParsingException("Do you really want to expand from " + previous + " to " + next + "?  If so, you'll need to edit and recompile processTypeRange()."); }
					if (next >= previous) {
						for (int k = previous + 1; k < next; k++) {
							expandedConstants.add(stringHandler.getNumericConstant(k));
						}
					}
					else {
						for (int k = previous - 1; k > next; k--) {
							expandedConstants.add(stringHandler.getNumericConstant(k));
						}
					}
				}
				else { throw new ParsingException("When '...' is present, all types must be number.  You provided: '" + c + "'."); }
			}
			stringHandler.recordPossibleTypes(typeName, expandedConstants);
		}
		else {
			stringHandler.recordPossibleTypes(typeName, constants);
		}
	}

	/* Process a mode specification.  There needs to be an EOL at the end ('.' or ';') due to the optional arguments.
	 *  If the optional arguments are used, they can be separated by commas, but this isn't necessary.
	 *
	 *     mode:       typed_literal           // This states the types of the arguments in this literal.  Types are + (an 'input' variable; MUST be present earlier in the clause), - (an 'output' variable; need not already be present in the clause), and # (a constant; need not already be present).    A variable can be followed by '!k' or $k' - the former means "this predicate will be true for EXACTLY k possible values for this argument, where the latter is similar but for "AT MOST K."
	 *  			   [target=pred/numbArgs]  // Optionally [not yet implemented] can say that the above mode only applies when learning this target.  A sample is 'parentOf/2' (the literal whose predicate name is 'parentOf' and which has two arguments).
	 *  			   [max=#]                 // Optionally say that typed_literal can appear in a learned clauses at most # (some integer) times.
	 *  			   [maxPerInputVars=#]     // Optionally indicate that PER SETTING to the 'input' (i.e. '+') variables, can occur at most this many times (an idea taken from Aleph).
	 */
	private void processMode(List<Sentence> listOfSentences) throws ParsingException, IOException {  // TODO if token not a known optional argument could pushback() w/o needing an EOL, but be more restrictive for now.
		Literal       typedHeadLiteral = processLiteral(true);
		int           tokenRead    = getNextToken();
		PredicateName targetPred   = null;
		int           arity        = -1; // '-1' means not specified.
		int           max          = Integer.MAX_VALUE;
		int        maxPerInputVars = Integer.MAX_VALUE;

		while (!atEOL()) { // Have some optional arguments since not yet at EOL.
			String currentWord = tokenizer.reportCurrentToken();
			if (tokenRead == ',') {

			}
			else if (currentWord.equalsIgnoreCase("max")) {
				// BUG: the user can't use 'max' nor 'maxPerInputVars' as target predicates.  TODO fix
				if (max < Integer.MAX_VALUE) { throw new ParsingException("Have already read max=" + max + " when processing a mode and have encountered 'max' again."); }
				max             = readEqualsInteger();
			}
			else if (currentWord.equalsIgnoreCase("maxPerInputVars")) {
				if (maxPerInputVars < Integer.MAX_VALUE) { throw new ParsingException("Have already read maxPerInputVars=" + max + " when processing a mode and have encountered 'maxPerInputVars' again."); }
				maxPerInputVars = readEqualsInteger();
			}
			else if (currentWord.equalsIgnoreCase("target")) {
				Utils.warning("The use of the 'target' option in the specification of modes has not yet been implemented.  So this mode will apply to all targets.");
				if (targetPred != null) { throw new ParsingException("Have already read targetPred=" + targetPred + " and have now read '" + currentWord + " when processing a mode."); }
				tokenRead    = getNextToken();
				if (tokenRead != '=') { throw new ParsingException("Expecting to read '=' (after 'target'), but instead read: '" + reportLastItemRead() + "'."); }
				currentWord = getNextString();
				targetPred = stringHandler.getPredicateName(currentWord);
				tokenRead = getNextToken();
				if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a mode specification but got: '" + reportLastItemRead() + "'."); }
				arity = readInteger();
			}
			else {
				throw new ParsingException("Parsing a mode - " + typedHeadLiteral + " - and instead of reading 'target=' or 'max=' or 'maxPerInputVars=', unexpectedly read: '" + reportLastItemRead() + "'.");
			}
			tokenRead = getNextToken();
		}

		if (typedHeadLiteral.getArguments() != null) {
			for (Term term : typedHeadLiteral.getArguments()) {
				if (term instanceof Function) {
					continue;
				}
				if (term.getTypeSpec() != null) { continue; }
				throw new ParsingException("All arguments in mode specifications must be typed.  There is no type for '" + term + "' in '" + typedHeadLiteral + "'.");
			}
		}
		stringHandler.recordMode(typedHeadLiteral, max, maxPerInputVars, false);
		

        listOfSentences.add(stringHandler.getClause(stringHandler.getLiteral("mode", typedHeadLiteral.convertToFunction(stringHandler)), true));

		// Do NOT skipToEOL() here since that is what ended the while loop.
	}

	private void processFunctionAsPred() throws ParsingException, IOException {
		checkForPredicateNamesThatAreCharacters(getNextToken());
		int tokenRead;
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a " + FunctionAsPredType.numeric + "FunctionAsPred specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

		tokenRead = getNextToken();
		if (tokenRead == ',') {
			getNextToken();
		} // OK if there are some commas separating the items.
		currentWord = tokenizer.reportCurrentToken();
		tokenRead    = getNextToken();
		if (tokenRead != '=') { throw new ParsingException("Expecting to read '=' (after 'arg'), but instead read: '"  + reportLastItemRead() + "'."); }
		int position = readInteger();
		if (position < 1 || position > arity) { throw new ParsingException("Expecting to read an integer between 1 and " + arity + ", but instead read '" + position + "."); }

		predicate.addFunctionAsPred(FunctionAsPredType.numeric, arity, position);
		peekEOL(true); // Suck up an optional EOL.
	}

	private void processBridger() throws ParsingException, IOException {
		checkForPredicateNamesThatAreCharacters(getNextToken());
		int tokenRead;
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a bridger specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

		predicate.addBridger(arity);
		peekEOL(true); // Suck up an optional EOL.
	}

	private void processTemporary() throws ParsingException, IOException {
		checkForPredicateNamesThatAreCharacters(getNextToken());
		int tokenRead;
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a temporary specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

		predicate.addTemporary(arity);
		peekEOL(true); // Suck up an optional EOL.
	}

	private void processInline() throws ParsingException, IOException {
		checkForPredicateNamesThatAreCharacters(getNextToken());
		int           tokenRead;
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate   = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in an inline specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

		predicate.addInliner(arity);
		peekEOL(true); // Suck up an optional EOL.
	}

	private void processQueryPred() throws ParsingException, IOException {
		checkForPredicateNamesThatAreCharacters(getNextToken());
		int           tokenRead;
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate   = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a query-predicate specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

		predicate.addQueryPred(arity);
		peekEOL(true); // Suck up an optional EOL.
	}

	private int getNextToken() throws IOException {
		return getNextToken(false);
	}

	private int getNextToken(boolean okIfEOF) throws IOException {
		int tokenRead = tokenizer.nextToken();

		if (tokenRead == StreamTokenizer.TT_EOF && !okIfEOF) { throw new IOException("Unexpected EOF: " + fileName); }
		return tokenRead;
	}

	/*
	 * Read the next token and return it as a string. If the next token is
	 * not a string, throw an exception.
	 */
	private String getNextString() throws ParsingException, IOException {
		int tokenRead = getNextToken();
		if (tokenRead != StreamTokenizer.TT_WORD) { throw new ParsingException("Expected to read a token, but read: '" + reportLastItemRead() + "'."); }
		return tokenizer.sval();
	}

	private int readEqualsInteger() throws ParsingException, IOException {
		int tokenRead = getNextToken();
		if (tokenRead != '=') { throw new ParsingException("Expecting an '=' but got: " + reportLastItemRead() + "."); }
		return readInteger();
	}

	private Literal readEqualsTypedLiteral() throws ParsingException, IOException {
		int tokenRead = getNextToken();
		if (tokenRead != '=') { throw new ParsingException("Expecting an '=' but got: " + reportLastItemRead() + "."); }
		return processLiteral(true);
	}

	private int readInteger() throws ParsingException, IOException {
		int   tokenRead = getNextToken();
		boolean negated = false;
		if (tokenRead == '-') {
			negated   = true;
			tokenRead = getNextToken();
		}
		if (tokenRead == '@') {  // A leading # indicates the value needs to be looked up in the list of set parameters.
			getNextToken();
			String wordRead = tokenizer.sval();
			String setting  = stringHandler.getParameterSetting(wordRead);
			if (setting      == null) { Utils.error(" Read '@" + wordRead + "', but '" + wordRead + "' has not been set."); }
			return Integer.parseInt(Objects.requireNonNull(setting));
		}
		if (tokenRead != StreamTokenizer.TT_WORD || !isAllDigits(tokenizer.sval())) {
			String lastItem = reportLastItemRead();
			tokenizer.pushBack();
			if (negated) { tokenizer.pushBack(); } // Get back to state when readInteger() called in case the caller wants to field the exception.
			throw new ParsingException("Expecting an integer but got: '" + lastItem + "'.");
		}
		int value = Integer.parseInt(tokenizer.sval());
		if (negated) { return -value; }
		return value;
	}

	/*
     * See if this character is the next one in the stream. If not, throw an
     * exception using this provided message (if the message = null,
     * generate one instead).
     */
	private void expectAndConsume(char charValue) throws ParsingException, IOException {
		int tokenRead = getNextToken();
		if (tokenRead == (int)charValue) { return; }
		throw new ParsingException("Expecting the character '" + charValue + "' but read '" + reportLastItemRead() + "'.");
	}

	/* See if this character is the next one in the stream. If so, "chew it
     * up" and return 'true.' Otherwise push it back and return 'false.'
     */
	private boolean checkAndConsume(char charValue) {
		int tokenRead;
		try {
			tokenRead = getNextToken();
		}
		catch (IOException e) {
			return false; // If at EOF, no need to throw an exception.  Just say nothing to peek at.  TODO - make sure this cant lead to an infinite loop of peek's.
		}
		if (tokenRead == (int)charValue) { return true; }
		tokenizer.pushBack();
		return false;
	}

	/*
         * See if the current token is EOL ('.' or ';').
         *
         * @return Whether the current token in the tokenizer is an end-of-line
         *         marker.
         */
	private boolean atEOL() {
		return (tokenizer.ttype() == '.' || tokenizer.ttype() == ';');
	}

	/*
	 * See if next token is an EOL character ('.' or ';').
	 */
	private boolean peekEOL(boolean okIfEOF) throws ParsingException, IOException {
		int token = tokenizer.nextToken(); // Suck up the EOL if it is next.
		if (!okIfEOF && token == StreamTokenizer.TT_EOF) { throw new IOException("Unexpected EOF."); }
		if (token == '.' || token == ';') { return true; }
		tokenizer.pushBack();
		return false;
	}

	private void checkForComma() throws ParsingException, IOException {
		if (checkAndConsume(',')) { return; }
		if (checkAndConsume('}')) { tokenizer.pushBack(); return; }
		if (checkAndConsume(']')) { tokenizer.pushBack(); return; }
		if (peekEOL(true))     { return; }
		getNextToken();
		throw new ParsingException("Was looking for a comma"
							+ ("")
							+ (" or a right brace or bracket")
							+ (" or an EOL character ('.' or ';')")
							+ " when " + "processing a type range" + ", but read: '" + reportLastItemRead() + "'.");
	}

	private boolean isAllDigits(String integerString) {
		// 'parseInt' gets called twice since this is only a boolean, but no big deal to read integer strings twice.
		try { Integer.parseInt(integerString); return true;  }
		catch (NumberFormatException e)     {  return false; }
	}

	private String reportLastItemRead() {
		int tokenRead = tokenizer.ttype();
		if (tokenRead == StreamTokenizer.TT_EOF)  { return "EOF"; }
		if (tokenRead == StreamTokenizer.TT_WORD) { return tokenizer.sval(); }
		return String.valueOf((char) tokenRead);  // Want the character not its integer representation.
	}

	private boolean isaPossibleTermName(int tokenRead) {
		switch (tokenRead) {
			case '+':                     return (tokenizer.prevToken() == '\\');
			case '\\':                    return true; // Might be \+().
			case '-':                     return true; // Added by JWS Jan 2010.
			case StreamTokenizer.TT_WORD: return true;
			default:                      return false;
		}
	}

    private boolean checkForOperator() throws ParsingException, IOException {
        return checkToken("-") || checkToken("*") || checkToken("/") || checkToken("+");
    }

	private String getPredicateOrFunctionName() throws ParsingException {
		return getPredicateOrFunctionName(tokenizer.ttype());
	}
	private String getPredicateOrFunctionName(int tokenRead) throws ParsingException {
		switch (tokenRead) {  // If changed, check out checkForPredicateNamesThatAreCharacters (for cases where a single-char string is returned).
			case StreamTokenizer.TT_WORD:                   return tokenizer.sval();
		//	case ':':  if (tokenizer.prevToken() == '-')  { return ":-"; } // Support ':-' as a predicate.
			case '-':                                       return "-";
			case '+':  if (tokenizer.prevToken() == '\\') { return "\\+"; }
					   return "+";
			case '=':  if (tokenizer.prevToken() == '\\') {
							if (checkAndConsume('='))     { return "\\=="; }
					   }
					   break;
			case '\\': if (checkAndConsume('+'))          { return "\\+";  }
			  		   if (checkAndConsume('='))  {
							if (checkAndConsume('='))     { return "\\=="; }
							                                return "\\=";
			 		   }
		}
		throw new ParsingException("Expecting a predicate name but read: '" + reportLastItemRead() + "'.");
	}

    private String checkAndConsumeArgumentName() throws IOException {

        String possibleName;

        int token = getNextToken();
        if ( token == StreamTokenizer.TT_WORD) {
            possibleName = tokenizer.reportCurrentToken();
            if ( checkAndConsumeToken("=") ) {
                return possibleName;
            }
        }
        tokenizer.pushBack();

        return null;
    }

	private Literal processLiteral(boolean argumentsMustBeTyped) throws ParsingException, IOException {
		int tokenRead        = getNextToken();
		int leftParenCounter = 0;
		while (tokenRead == '(' || tokenRead == '{' || tokenRead == '[') {
			leftParenCounter++;
			tokenRead = getNextToken();
		}

		tokenRead = checkForPredicateNamesThatAreCharacters(tokenRead);
		Term possibleTerm     = processRestOfTerm(tokenRead, false); // WHY????? argumentsMustBeTyped);
		tokenRead             = getNextToken(true);

		if (tokenRead == StreamTokenizer.TT_EOF) { return convertTermToLiteral(possibleTerm); }
		String peekAtNextWord = isInfixTokenPredicate(tokenRead);
		Literal inFixLiteral  = null;
		if (peekAtNextWord != null) { // Handle 'is' and <, >, >=, <=, ==, etc.
			inFixLiteral = processInfixLiteral(possibleTerm, peekAtNextWord, argumentsMustBeTyped);
			tokenRead    = getNextToken(); // Needed for the check for left parentheses.
		}
		while (leftParenCounter > 0) { // Suck up any closing parentheses.
			if (tokenRead != ')' && tokenRead != '}' && tokenRead != ']') { throw new ParsingException("Expecting " + leftParenCounter + " more right parentheses, but read: '" + tokenizer.reportCurrentToken() + "'."); }
			leftParenCounter--;
			tokenRead = getNextToken(true); // Always read one too many, then push back below.
		}
		if (tokenRead != StreamTokenizer.TT_EOF) { tokenizer.pushBack(); }
		if (inFixLiteral != null) { return inFixLiteral; }
		return convertTermToLiteral(possibleTerm);
	}

    private NamedTermList processListOfTerms(char openingBracket, boolean argumentsMustBeTyped) throws ParsingException, IOException {

        List<Term> terms = new ArrayList<>();
        List<String> names = null;

        Term t;
        String name;

        boolean done = false;

        String closingBracketChar = Character.toString(getClosingBracket(openingBracket));

        // We check immediate for a closing bracket to
        // support literals written as:  x() although
        // this is illegal in prolog.
        if (checkAndConsumeToken(closingBracketChar)) {
            done = true;
        }

        while (!done) {
            // Look for a name?
            name = checkAndConsumeArgumentName();
            t = processTerm(argumentsMustBeTyped);

            terms.add(t);

            if (names != null || name != null) {
                if (names == null) {
                    names = new ArrayList<>();
                }
                // Have to add even the null names just
                // in case they are necessary.
                names.add(name);
            }

            if (checkAndConsumeToken(closingBracketChar)) {
                done = true;
            }
            else if (!checkToken(",")) {
                getNextToken();
                throw new ParsingException("Unexpected token '" + tokenizer.reportCurrentToken() + "'.  Expected ',' or '" + closingBracketChar + "'." );
            }
            else {
                expectAndConsumeToken(",");
            }
        }

        return new NamedTermList(terms, names);
    }

    /* Reads a list of Terms from the stream.
     *
     * Assumes that the initial '(' has already been read and that the terminating ')' will be
     * consumed.
     */
    private ConsCell processConsCellList(boolean argumentsMustBeTyped) throws ParsingException, IOException {

        ConsCell head = null;
        ConsCell tail = null;

        Term t;

		boolean done = false;

        // We check immediate for a closing bracket to
        // support literals written as:  x() although
        // this is illegal in prolog.
        if (checkAndConsumeToken("]")) {
            head = stringHandler.getNil();
            done = true;
        }

        while (!done) {
            // Look for a name?
			checkAndConsumeArgumentName();
            t = processTerm(argumentsMustBeTyped);

            ConsCell cell = stringHandler.getConsCell(t, stringHandler.getNil(), null);
            if ( head == null ) {
                head = cell;
                tail = head;
            }
            else {
                tail.setCdr(cell);
                tail = cell;
            }

            if (checkAndConsumeToken("]")) {
                done = true;
            }
            else if ( checkAndConsumeToken("|") ) {
				checkAndConsumeArgumentName();
                t = processTerm(argumentsMustBeTyped);
                tail.setCdr(t);

                expectAndConsumeToken("]");

                done = true;
            }
            else if (!checkToken(",")) {
                getNextToken();
                throw new ParsingException("Unexpected token '" + tokenizer.reportCurrentToken() + "'.  Expected ',', '|', or ']'." );
            }
            else {
                expectAndConsumeToken(",");
            }
        }

        return head;
    }

    private char getClosingBracket(char openingBracketChar) {
        switch (openingBracketChar) {
                case '(':
                    return ')';
                case '{':
                    return '}';
                case '[':
                    return ']';
            default:
                return 0;
            }
    }

	/*
	 * Is the current token an indicator of a type specification? E.g., see TypeSpec.isaModeSpec for the full list.
	 */
	private boolean atTypeSpec() throws IOException {
		int tokenRead = tokenizer.ttype();
		if (tokenRead == '+' || tokenRead == '-') {
			if (tokenizer.prevToken() == '\\') { return false; } // Currently at the ISO standard, but semi-weirdly named, predicate '\+'.
			// If '+' or '-' need to see if the next item is a string of digits.
			int nextToken  = getNextToken();
			if (nextToken == StreamTokenizer.TT_WORD && isAllDigits(tokenizer.sval())) {  // This '+' or '-' is a sign in front of some digits.
				tokenizer.pushBack();
				return false;
			}
			if (nextToken == StreamTokenizer.TT_WORD && atInfinity()) { // Have +inf or -inf, which is not a type spec for type 'inf'.
				tokenizer.pushBack();
				return false;
			}
			tokenizer.pushBack();
			return true;
		}
		return TypeSpec.isaModeSpec((char) tokenRead);
	}

	private TypeSpec getTypeSpec(int tokenRead, StreamTokenizerJWS tokenizer) throws ParsingException, IOException {
		char modeAsChar = (char)tokenRead;
		int nextTokenRead = getNextToken();
		if (nextTokenRead != StreamTokenizer.TT_WORD) { throw new ParsingException("Expecting a type in a typed term (e.g., 'human' in '+human:John'), but instead got: '" + reportLastItemRead() + "'."); }
		return new TypeSpec(modeAsChar, tokenizer.sval(), stringHandler);
	}

	// At one time this was being considered for sharing as a utility, which is why it is a static.
	// But HandleFOPCstrings.getNumericConstant handles converting to int's when appropriate.
	private static NumericConstant convertToNumericConstant(HandleFOPCstrings stringHandler, TypeSpec typeSpec, double value) {
		return stringHandler.getNumericConstant(typeSpec, value);
	}

   // Terms can be wrapped in parentheses.
    private Term processTerm(boolean argumentsMustBeTyped) throws ParsingException, IOException {
        int tokenRead = getNextToken();
        switch (tokenRead) {
            case '(': // Handle parentheses.
                NamedTermList terms = processListOfTerms('(', argumentsMustBeTyped);
                List<Literal> literals = new ArrayList<>();
                for (Term term : terms.getTerms()) {
                    literals.add(term.asLiteral());
                }
                return stringHandler.getSentenceAsTerm(stringHandler.getClause(literals, null), "");
            case '{':
                return processTerm(argumentsMustBeTyped, 1);
            case '[': // Process a list.
                return processConsCellList(argumentsMustBeTyped);
            case '\\': // Could be \+().
            case '\'':
            case '"':
            case '-':
            case '+':
            case '=':
            case '#': // Have to include the possible type specs here...
            case '&': // Have to include the possible type specs here...
            case '*': // Have to include the possible type specs here...
            case '^': // Have to include the possible type specs here...
            case ':': // Have to include the possible type specs here...
            case '$': // Have to include the possible type specs here...
            case '@': // Have to include the possible type specs here...
            case '`': // Have to include the possible type specs here...
            case '>': // Have to include the possible type specs here...
            case StreamTokenizer.TT_WORD:
                Term result = processRestOfTerm(tokenRead, argumentsMustBeTyped);
                if ( checkForOperator() ) {
                    result = processMathExpression(result, argumentsMustBeTyped, false);
                }
                return result;
            default:
            	if (TypeSpec.isaModeSpec((char) tokenRead)) {
                    result = processRestOfTerm(tokenRead, argumentsMustBeTyped);
                    if ( checkForOperator() ) {
                        result = processMathExpression(result, argumentsMustBeTyped, false);
                    }
                    return result;            		
            	}
                throw new ParsingException("Reading a term and expected a left parenthesis, a minus or plus sign (etc), or a token, but instead read: '" + reportLastItemRead() + "'.");
        }
    }

	private Term processTerm(Term termSoFar, int leftParensCount) throws ParsingException, IOException {
		if (leftParensCount < 0) { throw new ParsingException("Have too many right parentheses after " + termSoFar); }
		int tokenRead = getNextToken();
		switch (tokenRead) {
			case '(':
			case '{':
			case '[':
				return processTerm(termSoFar, (leftParensCount + 1));
			case ')':
			case '}':
			case ']':
				if (leftParensCount == 0) { return termSoFar; }
				return processTerm(termSoFar, (leftParensCount - 1));
			case StreamTokenizer.TT_WORD:
			default: throw new ParsingException("Expecting a parentheses, but read unexpected character: '" + reportLastItemRead() + "'.");
		}
	}

	private Term processTerm(boolean argumentsMustBeTyped, int leftParensCount) throws ParsingException, IOException {
		if (leftParensCount < 0) { throw new ParsingException("Have too many right parentheses."); }
		int tokenRead = getNextToken();
		switch (tokenRead) {
			case '(':
			case '{':
				return processTerm(argumentsMustBeTyped, (leftParensCount + 1));
			case '\\': // Could be \+().
			case StreamTokenizer.TT_WORD:
				Term result = processRestOfTerm(tokenRead, argumentsMustBeTyped);
				if (leftParensCount == 0) { return result; }
				return processTerm(result, leftParensCount);
			default: throw new ParsingException("Expecting a literal, but read unexpected character: '" + reportLastItemRead() + "'.");
		}
	}

	/**
	 * A typeSpec can be followed with a !k or $k.  The former means the predicate "wrapping" this argument is true for EXACTLY k settings of this argument.  The latter is similar, except it the predicate is true for AT MOST k settings.
	 */
	private void checkForLimitOnNumberOfTrueSettings(TypeSpec typeSpec) throws ParsingException {
		if (typeSpec == null) { return; }
		if (checkAndConsume('!')) {
			try {
				int counter = readInteger();
				if (counter <= 0) { throw new ParsingException("Expecting to read a positive integer here, but read: " + counter); }
				typeSpec.truthCounts = counter;
			}
			catch (Exception e) {
				typeSpec.truthCounts = 1; // k=1 can be left implicit.
			}
		}
		else if (checkAndConsume('$')) {
			try {
				int counter = readInteger();
				if (counter <= 0) { throw new ParsingException("Expecting to read a positive integer here, but read: " + counter); }
				typeSpec.truthCounts = -counter;
			}
			catch (Exception e) {
				typeSpec.truthCounts = -1; // k=1 can be left implicit.
			}
		}
	}

	/*
	 * Read the REST of a term. The first token read is provided. If
	 * argumentsMustBeTyped=true, any arguments must be typed (e.g.,
	 * human:John).
	 */
	private Term processRestOfTerm(int tokenRead, boolean argumentsMustBeTyped) throws ParsingException, IOException {
		return processRestOfTerm(tokenRead, argumentsMustBeTyped, false);
	}
	private Term processRestOfTerm(int tokenRead, boolean argumentsMustBeTyped, boolean calledFromInsideMathExpression) throws ParsingException, IOException {
		int      negate    = 1;
		TypeSpec typeSpec  = null;
		boolean  skippedOverPlusSign = false;

		if (argumentsMustBeTyped || atTypeSpec()) { // Also look for OPTIONAL typed terms.
			typeSpec  = getTypeSpec(tokenRead, tokenizer);
			if (!checkAndConsume(':')) { // Just a type specification here, so done with the term.
				Term result = stringHandler.getAnonymousTerm(typeSpec);
				checkForLimitOnNumberOfTrueSettings(typeSpec);
				return result;
			}
			tokenRead = getNextToken();
		}
		if (atInfinity()) { return convertToNumericConstant(stringHandler, typeSpec, Double.POSITIVE_INFINITY); }
		if (atQuotedString(tokenRead)) {
			Term sc;
			// This actually also handles doubles, and even negation signs.
			// Hack to deal with other code that puts quote marks around numbers.  If set true, we lose the ability to distinguish between, say, the int 7 and the string "7".
			sc = stringHandler.getStringConstant(typeSpec, (char)tokenRead + tokenizer.svalQuoted() + (char)tokenRead, !stringHandler.keepQuoteMarks);
			return sc;
		}

		if (tokenRead == '-')  { // Have a minus sign.  Since this is a logical expression, can only be negating a number.
			negate    = -1;
			tokenRead = getNextToken();
			if (atInfinity()) { return convertToNumericConstant(stringHandler, typeSpec, Double.NEGATIVE_INFINITY); }
		}
		if (tokenRead == '+' && tokenizer.prevToken() != '\\') {  // Just a plus sign that can be ignored (note: we confirmed it isn't the built-in "\+" predicate).
			tokenRead = getNextToken();
			if (atInfinity()) { return convertToNumericConstant(stringHandler, typeSpec, Double.POSITIVE_INFINITY); }
			skippedOverPlusSign = true;
		}
		if (!isaPossibleTermName(tokenRead)) { throw new ParsingException("Expecting a term or literal name but read: '" + reportLastItemRead() + "'."); }

		// See if the next word read can be viewed as an integer or double.
		double resultAsNumber = processNumber(tokenRead);
		if (Utils.isaNumber(resultAsNumber)) {
			return convertToNumericConstant(stringHandler, typeSpec, negate * resultAsNumber);
		}
		String wordRead = getPredicateOrFunctionName(tokenRead);
		if (negate == -1)        { throw new ParsingException("Read an unexpected '-' when parsing a term."); }
		if (skippedOverPlusSign) { throw new ParsingException("Read an unexpected '+' when parsing a term."); }
		if (checkAndConsume('(')) { // See if this is a function.
			FunctionName fName = stringHandler.getFunctionName(wordRead);
			List<Term>   arguments;
			List<String> names = null;
			// ONCE is really more of a connective than a predicate, but since it is the only prefix-based connective, treat it here.
			if (wordRead.equalsIgnoreCase("once")) { // A once() needs to have an argument that is an FOPC clause.
				Sentence sent = processFOPC_sentence(1); // No need to require once()'s that only have one argument, which was a common source of errors in Prolog anyway.
				Clause clause = convertSimpleConjunctIntoClause(sent, fName);
				arguments     = new ArrayList<>(  1);
				arguments.add(stringHandler.getSentenceAsTerm(clause, "once"));
			} else if (wordRead.equalsIgnoreCase("call")) {
				Term termForCall = processTerm(argumentsMustBeTyped); // This can be a variable here, but at evaluation time it needs to be a function, which will be converted to a literal and evaluated.
				if (!checkAndConsume(')') && !checkAndConsume('}') && !checkAndConsume(']')) { throw new ParsingException("Expecting a right parenthesis to close this " + wordRead + "()."); }
				arguments     = new ArrayList<>(  1);
				arguments.add(termForCall);
			} else if (wordRead.equalsIgnoreCase("findAll") || wordRead.equalsIgnoreCase("all")   ||
				       wordRead.equalsIgnoreCase("bagOf")   || wordRead.equalsIgnoreCase("setOf")) { // A findAll(), etc. needs to have an SECOND argument that is an FOPC clause.
				Term termForFindall     = processTerm(argumentsMustBeTyped);
				if (!checkAndConsume(',')) { throw new ParsingException("Expecting a comma after '" + termForFindall + "' in a " + wordRead + "()."); }
				Sentence sentenceForFindAll = processFOPC_sentence(0, true);
				if (!checkAndConsume(',')) { throw new ParsingException("Expecting a comma after '" + termForFindall + "' and '" + sentenceForFindAll + "' in a " + wordRead + "()."); }
				Term listForFindAll     = processTerm(argumentsMustBeTyped);
				if (!checkAndConsume(')') && !checkAndConsume('}') && !checkAndConsume(']')) { throw new ParsingException("Expecting a right parenthesis to close this " + wordRead + "()."); }
				Sentence implicitImplication = stringHandler.getConnectedSentence(sentenceForFindAll, stringHandler.getConnectiveName("->"), stringHandler.getTermAsLiteral(termForFindall)); //stringHandler.getLiteral(stringHandler.getPredicateName("implictHead")));
				List<Clause> clauses = implicitImplication.convertToClausalForm();
				if (clauses.size() != 1) { throw new ParsingException("The body of a findAll(), etc. needs to be a simple clause.  You provided: " + sentenceForFindAll); }
				Clause clause = clauses.get(0);
				if (clause.posLiterals == null) { Utils.error("Renamed posList = null in " + implicitImplication + " and " + clause); }
				TermAsLiteral renamedHead =  (TermAsLiteral) clause.posLiterals.get(0);
				if (renamedHead == null) { Utils.error("Renamed head = null in " + implicitImplication + " and " + clause); }

				Term termForFindall2 = Objects.requireNonNull(renamedHead).term; // Need to get this so variable renaming is consistent.
				if (!clause.isDefiniteClause()) { throw new ParsingException("The body of a findAll(), etc. needs to be a conjunction ('and') of literals.  You provided: " + sentenceForFindAll); }
				clause.posLiterals = null; // No need to keep the "implictHeadForFindAll" around.  The resolution theorem prover "knows" it is implicitly there.
				arguments = new ArrayList<>(  3);
				arguments.add(termForFindall2);
				arguments.add(stringHandler.getSentenceAsTerm(clause, wordRead));
				arguments.add(listForFindAll);
			}
			else if (wordRead.equalsIgnoreCase("countProofs") || wordRead.equalsIgnoreCase("countUniqueBindings")) { // A countProofs() needs to have an FIRST argument that is an FOPC clause.
					Sentence sentenceForCounter = processFOPC_sentence(0, true);
					if (!checkAndConsume(',')) { throw new ParsingException("Expecting a comma '" + sentenceForCounter + "' in a " + wordRead + "()."); }
					Term listForCounter     = processTerm(argumentsMustBeTyped);
					if (!checkAndConsume(')') && !checkAndConsume('}') && !checkAndConsume(']')) { throw new ParsingException("Expecting a right parenthesis to close this " + wordRead + "().  Recall countProofs(clause, N) and countUniqueBindingsclause, N) only have two arguments."); }
					Sentence implicitImplication = stringHandler.getConnectedSentence(sentenceForCounter, stringHandler.getConnectiveName("->"), stringHandler.getLiteral(stringHandler.getPredicateName("implictHead")));
					List<Clause> clauses = implicitImplication.convertToClausalForm();
					if (clauses.size() != 1) { throw new ParsingException("The body of a countProofs() or countUniqueBindings() needs to be a simple clause.  You provided: " + sentenceForCounter); }
					Clause clause = clauses.get(0);
					if (!clause.isDefiniteClause()) { throw new ParsingException("The body of a Counter(), etc. needs to be a conjunction ('and') of literals.  You provided: " + sentenceForCounter); }
					clause.posLiterals = null; // No need to keep the "implictHeadForCounter" around.  The resolution theorem prover "knows" it is implicitly there.
					arguments = new ArrayList<>(2);
					arguments.add(stringHandler.getSentenceAsTerm(clause, wordRead));
					arguments.add(listForCounter);
			}
			else {
				 NamedTermList namedTermList = processListOfTerms('(', argumentsMustBeTyped); // This should suck up the closing parenthesis.
				 arguments = namedTermList.getTerms();
				 names     = namedTermList.getNames();
			}
			checkForLimitOnNumberOfTrueSettings(typeSpec); // Look for a training !k or $k.
			return stringHandler.getFunction(fName, arguments, names, typeSpec);
		}
		else if (!calledFromInsideMathExpression && peekIfAtInfixMathSymbol()) {
			tokenizer.pushBack();
			Term initialTerm = stringHandler.getVariableOrConstant(typeSpec, wordRead);
			Term mathExpression = processMathExpression(initialTerm, argumentsMustBeTyped, false);
			checkForLimitOnNumberOfTrueSettings(typeSpec);
			return mathExpression;
		}
		checkForLimitOnNumberOfTrueSettings(typeSpec);
		return stringHandler.getVariableOrConstant(typeSpec, wordRead);  // If the next character isn't an open parenthesis, then have a constant or a variable.
	}

	private boolean peekIfAtInfixMathSymbol() throws IOException {
		int tokenRead = getNextToken();
		switch (tokenRead) {
			case '+':
			case '-':
			case '*':
			case '/': return true;
		}
		tokenizer.pushBack();
		return false;
	}

	private Clause convertSimpleConjunctIntoClause(Sentence sent, AllOfFOPC caller) throws ParsingException {
		Sentence implicitImplication = stringHandler.getConnectedSentence(sent, stringHandler.getConnectiveName("->"), stringHandler.getLiteral(stringHandler.getPredicateName("implictHead")));
		List<Clause> clauses = implicitImplication.convertToClausalForm();
		return convertlistOfSentencesIntoClause(clauses, sent, caller);
	}
	private Clause convertlistOfSentencesIntoClause(List<Clause> clauses, Sentence sent, AllOfFOPC caller) throws ParsingException {
		if (clauses.size() != 1) { throw new ParsingException("The body of a '" + caller + "' needs to be a simple clause.  You provided: " + sent); }
		Clause clause = clauses.get(0);
		      if (!clause.isDefiniteClause()) {
            throw new ParsingException("The body of a '" + caller + "' needs to be a conjunction ('and') of literals.  You provided: " + sent);
        }
        clause.posLiterals = null; // No need to keep the "implictHead" around.  The resolution theorem prover "knows" it is implicitly there.
		return clause;
	}

	/*
	 * 	[]                      = nil
	 *  [TermA]                 = consCell(TermA, nil);
	 *  [TermA | TermB]         = consCell(TermA, TermB)
	 *  [TermA, TermB]          = consCell(TermA, consCell(TermB, nil))
	 *  [TermA, TermB | Term C] = consCell(TermA, consCell(TermB, TermC))
	 *
	 */
	private ConsCell processList(boolean argumentsMustBeTyped, int leftParensCount, boolean closeWithRightParen) throws ParsingException, IOException {
		// When called, one or more OPENs of list (i.e., '[') have been encountered.
		if (leftParensCount < 0) { throw new ParsingException("Have too many closing ]'s in a list."); }
		int tokenRead = getNextToken();
		switch (tokenRead) {
			case '[': // Need to process a new list, then cons it on the front of the rest of the list.
				ConsCell firstPart = processList(argumentsMustBeTyped, 1, false);
				Term    secondPart = processInsideConsCell(argumentsMustBeTyped, leftParensCount, false);
				return stringHandler.getConsCell(firstPart, secondPart, null);
			case ']': // Can "pop" the stack.
				if (closeWithRightParen) { throw new ParsingException("Expecting a ')', but read: '" + reportLastItemRead() + "'."); }
				if (leftParensCount == 1) { return stringHandler.getNil(); }
				return processList(argumentsMustBeTyped, (leftParensCount - 1), false);
		    default:
				try { // Read the first term.
					Term  first = processRestOfTerm(tokenRead, argumentsMustBeTyped);
					// Read the rest of this list.
					Term  rest  = processInsideConsCell(argumentsMustBeTyped, 1, closeWithRightParen);
					// Make a cons cell.
					ConsCell firstCons;
                    if (rest == null) {
                        firstCons = stringHandler.getConsCell(first, null);
                    }
                    else {
                        firstCons = stringHandler.getConsCell(first, rest, null);
                    }
					if (leftParensCount == 1) { return firstCons; } // If only one level deep, done.
					// If not done, process the rest and cons the first item on the front.
					Term term = processInsideConsCell(argumentsMustBeTyped, (leftParensCount - 1), closeWithRightParen);
					return stringHandler.getConsCell(firstCons, term,  null);
                } catch (ParsingException e) {
                    throw e;
				} catch (Exception e) {
					throw new ParsingException("Expecting a term or a '[' or a ']', but read: '" + reportLastItemRead() + "'\nand received this exception: " + e);
				}
		}
	}

	/*
	 * p([ [a], [[[b]]], [c | d] ]). Have read the first item in a cons
	 * cell, e.g., 'a' in '[a, ...]' or in '[a | b]' or in '[a]'
	 */
	private Term processInsideConsCell(boolean argumentsMustBeTyped, int leftParensCount, boolean closeWithRightParen) throws ParsingException, IOException {
		int tokenRead = getNextToken();
		switch (tokenRead) {
			case ',':
				return processList(argumentsMustBeTyped, leftParensCount, closeWithRightParen);
			case '|':
				Term term = processTerm(argumentsMustBeTyped);
				// Need to suck up the closing bracket.  Complain if not found.
				if (!checkAndConsume(']')) {
					throw new ParsingException("Expecting a ']' after a '| term' in a list, but read: '" + reportLastItemRead() + "'.");
				}
				if (leftParensCount == 1) { return term; }
				Term rest = processInsideConsCell(argumentsMustBeTyped, (leftParensCount - 1), closeWithRightParen);
				return stringHandler.getConsCell(term, rest, null);
			case ']':
				if (closeWithRightParen) { throw new ParsingException("Expecting a ')', but read: '" + reportLastItemRead() + "'."); }
				if (leftParensCount == 1) { return stringHandler.getNil(); }
				return processInsideConsCell(argumentsMustBeTyped, (leftParensCount - 1), false);
			default: throw new ParsingException("Processing inside a list and expecting a '|', ',' or ']', but read: '" + reportLastItemRead() + "'.");
		}
	}

	private boolean atQuotedString(int token) {
		return token == '"' || (FileParser.allowSingleQuotes && token == '\'');
	}

	/*
	 * If reading a string, possibly quoted, return it.  If not a string, complain if requested; otherwise return null.
	 */
	private String getPossiblyQuotedString(int tokenRead) throws ParsingException {
		if (atQuotedString(tokenRead)) {
			return (char)tokenRead + tokenizer.svalQuoted() + (char)tokenRead;
		}
		try {
			double result = processNumber(tokenRead);
			if (!Double.isNaN(result)) { return Double.toString(result); }
		} catch (Exception ignored) {
		}

		if (tokenRead != StreamTokenizer.TT_WORD) {
			throw new ParsingException("Expecting the name of a type, but got: " + reportLastItemRead() + ".");
		}
		return tokenizer.sval();
	}

	/*
	 * Read the variables of a quantifier. If only one, it need not be
	 * wrapped in parentheses.
	 */
	private List<Variable> readListOfVariables() throws ParsingException, IOException {
		int tokenRead = getNextToken();
		switch (tokenRead) {
			case '(':
			case '{':
			case '[':
                List<Term>    terms = processListOfTerms((char)tokenRead, false).getTerms();
                List<Variable> vars = new ArrayList<>(terms.size());
                for (Term t : terms) {
                    if (t instanceof Variable) { vars.add((Variable) t); }
                    else { throw new ParsingException("Expecting a list of VARIABLEs, but read this non-variable: '" + t + "' in " + terms + "."); }
                }
                return vars;
			case StreamTokenizer.TT_WORD: // Allow ONE variable to appear w/o parentheses.
				Term term = stringHandler.getVariableOrConstant(tokenizer.sval(), true); // These are NEW variables since they are those of a quantifier.
				if (term instanceof Variable) {
					List<Variable> result = new ArrayList<>(1);
					result.add((Variable) term);
					return result;
				}
				throw new ParsingException("Expecting a variable (for a quantifier), but read: '" + term + "'.");
			default:
                throw new ParsingException("Expecting a variable or a left parenthesis, but read: '" + reportLastItemRead() + "'.");
		}
	}

	// Note that NOT is also handled here.
    private ConnectiveName processPossibleConnective(int tokenRead) throws ParsingException, IOException {
    	switch (tokenRead) {
			case StreamTokenizer.TT_WORD:
				String candidate = tokenizer.sval();
				if (ConnectiveName.isaConnective(candidate)) {
					if (ignoreThisConnective(false, candidate)) { return null; }
					return stringHandler.getConnectiveName(candidate);
				}
				return null;
			case '^':
			case '&':
			case ',':
			case '~': if (treatAND_OR_NOTasRegularNames) { return null; }
					  return stringHandler.getConnectiveName(String.valueOf((char)tokenRead));
			case '-':
				tokenRead = getNextToken();
				if (tokenRead == '>') { return stringHandler.getConnectiveName("->"); }
				tokenizer.pushBack();
				return null;
				//throw new ParsingException("Expecting the connective '->' but read: '-" + reportLastItemRead() + "'.");
			case '=':
				tokenRead = getNextToken();
				if (tokenRead == '>') { return stringHandler.getConnectiveName("=>"); }
				tokenizer.pushBack();
				return null;
				//throw new ParsingException("Expecting the connective '=>' but read: '-" + reportLastItemRead() + "'.");
			case ':':
				tokenRead = getNextToken();
				if (tokenRead == '=') { return stringHandler.getConnectiveName(":="); }
				if (tokenRead == '-') { return stringHandler.getConnectiveName(":-"); }
				tokenizer.pushBack();
				return null;
				//throw new ParsingException("Expecting the connective ':-' or ':=' but read: ':" + reportLastItemRead() + "'.");
			case '<':
				tokenRead      = getNextToken();
				if (tokenRead != '-' && tokenRead != '=') {
					tokenizer.pushBack();
					return null;
				}
				int tokenRead2 = getNextToken();
				if (tokenRead == '-' && tokenRead2 == '>') { return stringHandler.getConnectiveName("<->"); }
				if (tokenRead == '=' && tokenRead2 == '>') { return stringHandler.getConnectiveName("<=>"); }
				tokenizer.pushBack();
				tokenizer.pushBack();
				return null;
				// throw new ParsingException("Expecting the connective '<->' or '<=>' but read: ':" + tmp + reportLastItemRead() + "'.");
			case '\\':
				tokenRead = getNextToken();
				if (tokenRead == '+') { return stringHandler.getConnectiveName("\\+"); }
				tokenizer.pushBack();
				return null;
			default: return null;
		}
	}

	/*
	 * Read an FOPC sentence.
	 */
    private Sentence processFOPC_sentence(int insideLeftParenCount) throws ParsingException, IOException {
    	return  processFOPC_sentence(insideLeftParenCount, false);
    }

	private Sentence processFOPC_sentence(int insideLeftParenCount, boolean commaEndsSentence) throws ParsingException, IOException {
		List<AllOfFOPC> accumulator = new ArrayList<>(4);
		boolean         lookingForConnective = false;
		while (true) { // PFS = processFOPC_sentence
			int tokenRead = getNextToken();
			if (commaEndsSentence && insideLeftParenCount == 0 && tokenRead == ',') { // Sometimes want to read ONE argument as a sentence - e.g., the 2nd argument to findAll.
				Sentence resultComma = convertAccumulatorToFOPC(accumulator);
				tokenizer.pushBack();
				return resultComma;
			}
			ConnectiveName connective = processPossibleConnective(tokenRead);
			if (connective != null) { // OK to have NOT or '~' be the first item and OK to have any number of NOT's in a row.
    			if (!lookingForConnective && accumulator.size() > 0 && !ConnectiveName.isaNOT(connective.name)) { throw new ParsingException("Encountered two logical connectives in a row: '" + accumulator.get(accumulator.size() - 1) + "' and '" + connective + "'."); }
            	if (accumulator.isEmpty() && !ConnectiveName.isaNOT(connective.name)) {  throw new ParsingException("Encountered '" + connective + "' as the FIRST connective."); }
            	accumulator.add(connective);
    			lookingForConnective = false;
            }
            else {
            	// First see if dealing with an in-fix predicate.
            	String peekAtNextWord = isInfixTokenPredicate(tokenRead);
            	if (peekAtNextWord != null) {
            		AllOfFOPC lastItemAdded = accumulator.get(accumulator.size() - 1);
            		accumulator.remove(accumulator.size() - 1);
            		if (lastItemAdded instanceof TermAsSentence) {
            			Sentence sInFix = processInfixLiteral(((TermAsSentence) lastItemAdded).term, peekAtNextWord);
            			accumulator.add(sInFix);
    				}
            		else { throw new ParsingException("Cannot handle '" + peekAtNextWord + "' after '" + lastItemAdded + "'."); }
            	}
            	else {
            		switch (tokenRead) {
            			case '(':
            			case '{':
            			case '[':
            				Sentence resultLeftParens = processFOPC_sentence(insideLeftParenCount + 1); // Parse up to the closing right parenthesis.
							accumulator.add(resultLeftParens);
							break;
            			case ')':
            			case '}':
            			case ']':
            				if (insideLeftParenCount == 0) {
            					tokenizer.pushBack(); // Push this back.  This right parenthesis closes an outer call.
            				}
							return convertAccumulatorToFOPC(accumulator);
            			case '.':
            			case ';':
            				tokenizer.pushBack(); // Push this back.  It might be used to close several quantifiers.  If doing a top-level call, that call can such this up.
							return convertAccumulatorToFOPC(accumulator);
            			case '!': // Prolog's 'cut'.
            				PredicateName pName = stringHandler.standardPredicateNames.cut;
            				Literal lit = stringHandler.getLiteral(pName);
            				accumulator.add(lit);
            				break;
            			case '+': // Could have something like '+5 < y'
            			case '-': // Or, more likely, '-5 < y'  Or this could be a "bare" weight on a sentence.
            			case '\\': // Might be \+().
            			case StreamTokenizer.TT_WORD:
            				Sentence s = processFOPC_sentenceFromThisToken(insideLeftParenCount);
            				accumulator.add(s);
            				break;
            			case ':':
            				throw new ParsingException("Unexpectedly read ':'.  The previous token might be a misspelling of a keyword.  Have accumulated these tokens: " + accumulator);
            			default:
                            throw new ParsingException("Expecting a part of an FOPC sentence, but read the unexpected character: '" + reportLastItemRead() + "'.");
            		}
            		if (lookingForConnective) { throw new ParsingException("Encountered two FOPC sentences in a row: '" + accumulator.get(accumulator.size() - 2) + "' and '" + accumulator.get(accumulator.size() - 1) + "'."); }
            	}
            	lookingForConnective = true;
            }
		}
	}

	private Sentence processFOPC_sentenceFromThisToken(int insideLeftParenCount) throws ParsingException, IOException {
		String currentWord = getPredicateOrFunctionName(); // This will only be called if reading a string (which might be representing a number).
		// Quantifiers are scoped to go to the next EOL unless parenthesis limit the scope.
		if (currentWord.equalsIgnoreCase("ForAll")) {
			List<Variable> variables = readListOfVariables();
			Sentence       body; // We'll end this either when parentheses are matched or EOL is hit.
			if (checkAndConsume('(') || checkAndConsume('{')) {
				body = processFOPC_sentence(0); // We'll end this when a right parenthesis is encountered.
				if (!checkAndConsume(')') && !checkAndConsume('}') && !checkAndConsume(']')) { throw new ParsingException("Expecting to find a right parenthesis closing: '" + currentWord + " " + variables + " " + body + "'."); }
			}
			else {
				body = processFOPC_sentence(0);
			}
			UniversalSentence uSent = stringHandler.getUniversalSentence(variables, body);
			stringHandler.unstackTheseVariables(variables);
			return uSent;
		}
		else if (currentWord.equalsIgnoreCase("ThereExists") || currentWord.equalsIgnoreCase("Exists") || currentWord.equalsIgnoreCase("Exist")) { // Note: 'Exist' allowed since that is what Alchemy uses.
			List<Variable> variables = readListOfVariables();
			Sentence       body;
			if (checkAndConsume('(') || checkAndConsume('{')) {
				body = processFOPC_sentence(0); // We'll end this when a right parenthesis is encountered.
				if (!checkAndConsume(')') && !checkAndConsume('}') && !checkAndConsume(']')) { throw new ParsingException("Expecting to find a right parenthesis closing: '" + currentWord + " " + variables + " " + body + "'."); }
			}
			else {
				body = processFOPC_sentence(0);
			}
			ExistentialSentence eSent = stringHandler.getExistentialSentence(variables, body);
			stringHandler.unstackTheseVariables(variables);
			return eSent;
		}
        else {
            // See if this is an in-fix literal.
            Term possibleTerm = processRestOfTerm(tokenizer.ttype(), false);
            int tokenRead = getNextToken();
            String peekAtNextWord = isInfixTokenPredicate(tokenRead);
            if (peekAtNextWord != null) { // Handle 'is' and { <, >, >=, <=, == }.
                return processInfixLiteral(possibleTerm, peekAtNextWord);
            }
            tokenizer.pushBack(); // Undo the getNextToken() that checked for an infix predicate.

            if (possibleTerm instanceof NumericConstant) { // If reading a number and not in an in-fix (e.g., '5 <= 6') then interpret as a weighted sentence.
                Sentence sent;
                if (insideLeftParenCount > 0) {
                    if (insideLeftParenCount > 1) { throw new ParsingException("Possibly too many left parentheses before a weight."); }
                    if (checkAndConsume(')') || checkAndConsume('}') || checkAndConsume(']')) { // The parentheses wrap the number.
                        checkAndConsume(','); // Allow an optional comma after the number.
                        sent = processFOPC_sentence(0);
                    } else {
                        checkAndConsume(','); // Allow an optional comma after the number.
                        sent = processFOPC_sentence(insideLeftParenCount); // The parentheses wrap something like this: '(weight FOPC)'
                    }
                } else {
                       checkAndConsume(','); // Allow an optional comma after the number.
                       sent = processFOPC_sentence(0); // No parentheses involved.
                }
                sent.setWeightOnSentence(((NumericConstant) possibleTerm).value.doubleValue());
                return sent;
            } else {
                return convertTermToLiteral(possibleTerm);
            }
        }
	}

	private Literal convertTermToLiteral(Term term) throws ParsingException {
		if (term instanceof Function) {
			PredicateName pName = stringHandler.getPredicateName(((Function) term).functionName.name);
			Function      f     = (Function) term;
			return stringHandler.getLiteral(pName, f.getArguments(), f.getArgumentNames());
		}
        else if (term instanceof StringConstant) {  // This is an argument-less predicate.
			PredicateName pName = stringHandler.getPredicateName(((StringConstant) term).getName());
			return stringHandler.getLiteral(pName);
		}
        else if (term instanceof Variable) {  // This is an argument-less predicate.
			PredicateName pName = stringHandler.standardPredicateNames.implicit_call;
			return stringHandler.getLiteral(pName, Collections.singletonList(term));
		}
        else if ( term instanceof LiteralAsTerm ) {
            LiteralAsTerm lat = (LiteralAsTerm)term;
            return lat.itemBeingWrapped;
        }
		throw new ParsingException("Encountered '" + term + "' (" + term.getClass() + "), but was expecting a LITERAL");
	}

	private List<Term> convertToListOfTerms(Collection<Variable> collection) {
		if (collection == null) { return null; }
		List<Term> results = new ArrayList<>(collection.size());
		results.addAll(collection);
		return results;
	}

	private void setNumberOfPrecomputeFiles(int numberOfPrecomputeFiles) {
		FileParser.numberOfPrecomputeFiles = numberOfPrecomputeFiles;
	}

	public int getNumberOfPrecomputeFiles() {
		return numberOfPrecomputeFiles;
	}
}
