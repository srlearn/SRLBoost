package edu.wisc.cs.will.FOPC_MLN_ILP_Parser;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings.VarIndicator;
import edu.wisc.cs.will.Utils.NamedInputStream;
import edu.wisc.cs.will.Utils.NamedReader;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileInputStream;

import java.io.*;
import java.util.*;

import static edu.wisc.cs.will.Utils.MessageType.STRING_HANDLER_VARIABLE_INDICATOR;


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

 *   bridger:        predName/numbArgs              // A special-case determinate, where the role of this predicate is to enable the addition of some other predicate(s).
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
 *   The following all take predicateName/arity (and an optional EOL ['.' or ';']).
 *
 *      okIfUnknown:                                // It is OK if during theorem proving this predicate is undefined.  Helps catch typos.  If numberArgs='#' then applies to all versions of predName.  The EOL ('.' or ';') is optional.
 *
 * Everything else is interpreted as an FOPC sentence (using the strings "ForAll" and "ThereExists" ["Exists" is also OK, but "All" is NOT since it is a built-in Prolog predicate] and
 * the standard logical connectives of {'and', 'or', '^', '&', 'v', '->', ':-', etc.).
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

	private              int maxWarnings  = 100; // This can be reset via 'setParameter maxWarnings = 10'

	public final HandleFOPCstrings  stringHandler;
	private StreamTokenizerJWS tokenizer;
	private String             directoryName      = null;
	private String             prefix             = null;
	private String             fileName           = null;

	private final boolean treatAND_OR_NOTasRegularNames = false; // If true, treat AND and OR as function or predicate names.  (Used for IL parsing, for example.)


	public FileParser(HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
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
						if (colonNext && currentWord.equalsIgnoreCase("mode"))           { processMode(listOfSentencesReadOrCreated); break; }
						if (colonNext && currentWord.equalsIgnoreCase("bridger"))        { processBridger();     break; }
						if (colonNext && currentWord.equalsIgnoreCase("range"))          { processTypeRange(  ); break; }
						if (colonNext && currentWord.equalsIgnoreCase("queryPred"))      { processQueryPred(  ); break; }
						if (colonNext && currentWord.equalsIgnoreCase("okIfUnknown"))                    { processDirective(currentWord);  break; }
						if (colonNext && currentWord.equalsIgnoreCase("usePrologVariables"))             { processCaseForVariables(false); break; }
						if (colonNext && currentWord.equalsIgnoreCase("import"))      {
							List<Sentence>  sentencesInOtherFile =                         processAnotherFile();
							if (sentencesInOtherFile         == null) { break; }
							listOfSentencesReadOrCreated.addAll(sentencesInOtherFile);
							break;
						}
						if (colonNext) { tokenizer.pushBack(); } // Need to push the colon back if it wasn't part of a special instruction.  It can also appear in modes of terms.

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

		Utils.warning("% Unknown ':- " + nextTokenAsString + "' command.");

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

		secondTerm = processTerm(argumentsMustBeTyped);

		List<Term>    args   = new ArrayList<>(2);
		PredicateName pName  = stringHandler.getPredicateName(inFixOperatorName); pName.printUsingInFixNotation = true;
        args.add(firstTerm);
        args.add(secondTerm);
		return stringHandler.getLiteral(pName, args);
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
			if (countOfLowestItem < 1 || countOfLowestItem > accumulator.size() - 2) {
				Utils.error("Connectives cannot be in the first or last positions: " + accumulator);
			}
			Sentence leftArg  = (Sentence)accumulator.get(countOfLowestItem - 1);
			Sentence rightArg = (Sentence)accumulator.get(countOfLowestItem + 1);
			Sentence cSent    = stringHandler.getConnectedSentence(leftArg, cName, rightArg);
			accumulator.add(   countOfLowestItem + 2, cSent); // Add after the three items being combined.
			accumulator.remove(countOfLowestItem + 1); // Do this in the proper order so shifting doesn't mess up counting.
			accumulator.remove(countOfLowestItem);
			accumulator.remove(countOfLowestItem - 1);
		}

		return (Sentence) accumulator.get(0);
	}

	private String isInfixTokenPredicate(int tokenRead) throws ParsingException {
		// TODO(hayesall): Should always return `null`
		// If changed, check out checkForPredicateNamesThatAreCharacters (for cases where a single-char string is returned).
		if (tokenRead == StreamTokenizer.TT_WORD) {
			String tokenString = tokenizer.sval();
			return null;
		}
		return null;
	}

	// TODO - clean this up
	private int checkForPredicateNamesThatAreCharacters(int tokenRead) throws ParsingException, IOException {
		if (!isaPossibleTermName(tokenRead)) {
			String seeIfInfixPred = isInfixTokenPredicate(tokenRead);
			seeIfInfixPred = null;
			throw new ParsingException("Expecting a predicate name but read: '" + reportLastItemRead() + "'.");
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

	private boolean atInfinity() {
		String currentWord = tokenizer.reportCurrentToken();
		boolean result = (currentWord.equalsIgnoreCase("inf") || currentWord.equalsIgnoreCase("infinity"));

		if (result && checkAndConsume('(')) { // Allow inf() to be a predicate.
			tokenizer.pushBack();
			return false;
		}
		return result;
	}

	private double processNumber(int tokenRead) throws ParsingException {

		int countOfBackupsNeeded = 0;

		int negate               = 1;

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
                                default:
									// If of the form '2e3' will read all in one fell swoop, so only need to deal with '+' or '-' being "token breakers."
									throw new NumberFormatException();
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

	/*
	 * Parse the file named after this 'import:' directive. For example:
	 * import: text. The EOL ('.' or ';') at the end is optional.
	 */
	private List<Sentence> processAnotherFile() throws ParsingException, IOException {
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
			
			if (!newFileName.contains(".")) { newFileName += stringHandler.precompute_file_postfix; } //only add extension _after_ doing substitutions

			return loadThisFile(newFileName);
		}
		throw new ParsingException("Expecting the file name of a file to import, but read: '" + reportLastItemRead() + "'.");
	}
	
	private void checkForDefinedImportAndPrecomputeVars() {	// Simply check them all.  TODO - clean up.
	}

	private List<Sentence> loadThisFile(String newFileNameRaw) throws ParsingException, IOException {
		String   newFileName = Utils.replaceWildCards(newFileNameRaw);
		FileParser newParser = new FileParser(stringHandler); // Needs to use the same string handler.
		newParser.dontPrintUnlessImportant = dontPrintUnlessImportant;
		List<Sentence> result;

		String file2load = Utils.createFileNameString(directoryName, newFileName);
		if (stringHandler.haveLoadedThisFile(file2load, true)) {
			return null;
		}
		result = newParser.readFOPCfile(file2load, false);

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
		}
		peekEOL(true);
		if (parameterName.contains("import")) { checkForDefinedImportAndPrecomputeVars(); }
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
					if (!checkAndConsume(',')) { throw new ParsingException("Expecting a comma after '...' in the specification of a range."); }
					tokenRead = getNextToken();
				}
			}
		}
		if (needClosingBrace) {
			if (tokenRead != '}') { throw new ParsingException("Since an open brace ('{') was read, expecting a closing one in the specification of a type range."); }
			peekEOL(true); // Suck up an optional EOL.
		}

		stringHandler.recordPossibleTypes(typeName, constants);

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
		peekAtNextWord = null;
		Literal inFixLiteral  = null;
		while (leftParenCounter > 0) { // Suck up any closing parentheses.
			if (tokenRead != ')' && tokenRead != '}' && tokenRead != ']') { throw new ParsingException("Expecting " + leftParenCounter + " more right parentheses, but read: '" + tokenizer.reportCurrentToken() + "'."); }
			leftParenCounter--;
			tokenRead = getNextToken(true); // Always read one too many, then push back below.
		}
		if (tokenRead != StreamTokenizer.TT_EOF) { tokenizer.pushBack(); }
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
            case '{':
            case '[':
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
                }
                return result;
            default:
            	if (TypeSpec.isaModeSpec((char) tokenRead)) {
                    result = processRestOfTerm(tokenRead, argumentsMustBeTyped);
                    if ( checkForOperator() ) {
                    }
                    return result;            		
            	}
                throw new ParsingException("Reading a term and expected a left parenthesis, a minus or plus sign (etc), or a token, but instead read: '" + reportLastItemRead() + "'.");
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
			List<Term>   arguments = null;
			List<String> names = null;
			// ONCE is really more of a connective than a predicate, but since it is the only prefix-based connective, treat it here.
			if (wordRead.equalsIgnoreCase("findAll") || wordRead.equalsIgnoreCase("all")   ||
				       wordRead.equalsIgnoreCase("bagOf")   || wordRead.equalsIgnoreCase("setOf")) { // A findAll(), etc. needs to have an SECOND argument that is an FOPC clause.
			}
			else if (wordRead.equalsIgnoreCase("countProofs") || wordRead.equalsIgnoreCase("countUniqueBindings")) { // A countProofs() needs to have an FIRST argument that is an FOPC clause.
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
				peekAtNextWord = null;
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
				lookingForConnective = true;
            }
		}
	}

	private Sentence processFOPC_sentenceFromThisToken(int insideLeftParenCount) throws ParsingException, IOException {
		String currentWord = getPredicateOrFunctionName(); // This will only be called if reading a string (which might be representing a number).
		// Quantifiers are scoped to go to the next EOL unless parenthesis limit the scope.

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

	public int getNumberOfPrecomputeFiles() {
		// Allows user to set it to a higher number but doesn't penalize all runs where there are fewer precomputes
		// It is mildly risky to make this a static, but acceptable.
		return 125;
	}
}
