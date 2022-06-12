package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.ILP.ChildrenClausesGenerator;
import edu.wisc.cs.will.ILP.InlineManager;
import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;
import java.util.*;

/*
 * @author shavlik
 *
 * A 'theory' is a collection of first-order predicate calculus sentences, represented (for us) in clausal form.
 * 
 */
public class Theory extends AllOfFOPC implements Serializable, Iterable<Sentence> {

	// TODO(hayesall): This deals with quite a few of the terms I've been factoring out:
	//		inline, temporary, prune, support

	private InlineManager              inlineHandler       = null;

	public void setInlineHandler(InlineManager inlineHandler) {
		this.inlineHandler = inlineHandler;
	}

	private List<Clause>               clauses;
	private List<Clause>               supportClauses;  // These clauses are needed to support evaluation of the theory.  Let's keep these in a list, in case the order matters.
	private Collection<Sentence>       sentences;       // The original sentences.  Note: one sentence can become many clauses, so not a one-to-one match (could do so if needed).
	private List<Clause>               originalClauses; // Before dealing with IN-LINES.
	private List<Clause>               unsimplifiedClauses        = null; // Before simplification is called.
	private List<Clause>               unsimplifiedSupportClauses = null;
	private boolean                    somethingSimplified        = false; // See if the simplified version is different.	
	
	final transient public HandleFOPCstrings stringHandler;

	private PrettyPrinterOptions prettyPrinterOptions = null;
	
	public Theory(HandleFOPCstrings stringHandler) {
		this.clauses              = null;
		this.stringHandler        = stringHandler;
	}

	public Theory(HandleFOPCstrings stringHandler, Collection<? extends Sentence> standardSentences) {
		this(stringHandler, standardSentences, null);
	}
	public Theory(HandleFOPCstrings stringHandler, Collection<? extends Sentence> standardSentences, InlineManager inlineHandler) {
		this(stringHandler);
		this.inlineHandler = inlineHandler;
		if (standardSentences == null) { sentences = null;  clauses = null; }
		else { addTheseSentences(standardSentences, inlineHandler);	}
		
		originalClauses = clauses;
	}

	// This assumes any desired inlining etc. has already been done.
	public Theory simplify() {
		collectAnyRemainingInliners();
    	if (unsimplifiedClauses != null) { Utils.warning("Have already simplified the clauses.");  return this; }
    	unsimplifiedClauses        = clauses;
    	unsimplifiedSupportClauses = supportClauses;
    	clauses        = simplify(unsimplifiedClauses);
    	supportClauses = simplify(unsimplifiedSupportClauses);
    	return this;
    }

	private List<Clause> simplify(List<Clause> theseClauses) {
    	if (theseClauses == null) { return null; }
    	List<Clause> results = new ArrayList<>(4);
    	somethingSimplified  = false;
		// I am not sure why this is outside the clause FOR loop, but that is the way it was when simplifyListOfLiterals's code was pulled out (to allow recursion), and so I left it that way (7/30/10).
		for (Clause cRaw : theseClauses) {
			List<Literal> newNegLits = simplifyListOfLiterals(cRaw.negLiterals);
			Clause newC = stringHandler.getClause(cRaw.posLiterals, newNegLits, cRaw.getExtraLabel());
    		results.add(newC);
    	}
    	return results;
    }
    
    // It is possible some in-liners are still in a theory (eg, due to some bug).
    // So if a theory is to 'stand alone' in a new task, we need to keep the definitions of these in-liners.
    private boolean haveCollectedRemainingInLiners = false;
    private final Set<Clause> collectedSupporters = new HashSet<>(4);
    private void collectAnyRemainingInliners() {
    	if (haveCollectedRemainingInLiners) {
			return;
		}
    	collectedSupporters.clear();
    	help_collectAnyRemainingInliners(clauses);
    	help_collectAnyRemainingInliners(supportClauses);
    	if (!collectedSupporters.isEmpty()) {
    		supportClauses.addAll(collectedSupporters);
    	   	collectedSupporters.clear();
    	}
    	haveCollectedRemainingInLiners = true;    	
    }
    
    private void help_collectAnyRemainingInliners(List<Clause> theseClauses) {
    	if (theseClauses == null) {
			return;
		}
		for (Clause cRaw : theseClauses) {
			if (cRaw.negLiterals != null) {
				for (Literal lit : cRaw.negLiterals) {
					help_collectAnyRemainingInliners(lit);
				}
			}
    	}
    }

	private void help_collectAnyRemainingInliners(Literal lit) {
		if (lit.getArity() > 0) {
			for (Term ignored : lit.getArguments()) {
				help_collectAnyRemainingInliners();
			}
		}
    }
    
    private void help_collectAnyRemainingInliners() {
		// TODO(hayesall): Deprecate all of this.
	}
    
    private List<Literal> simplifyListOfLiterals(List<Literal> inputList) {
    	if (inputList == null) { return null; }
		List<Literal> newNegLits     = new ArrayList<>(inputList.size());
		for (Literal nLit : inputList) {
			boolean saveIt = true;

			if (canPrune()) {
				continue;
			}

			// TODO(hayesall): Check for side effects and remove.
			nLit.numberArgs();
			nLit.numberArgs();
			nLit.numberArgs();

			for (Literal savedLit : newNegLits) {
				if (savedLit.equals(nLit)) {
					saveIt = false;
					break;
				}
			}
			
			if (saveIt) {
				newNegLits.add(nLit);
			} else {
				somethingSimplified = true;
			}
		}

		if (newNegLits.size() < 1) { newNegLits.add(stringHandler.trueLiteral); } // Could propagate this 'true' but it is an unlikely case and so don't bother.
		return newNegLits;
    }

	///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	private StringConstant[] constantsToUse = null; // These are used to replace variables when matching for pruning.

	private boolean canPrune() {
		if (constantsToUse == null) {
    		constantsToUse = new StringConstant[ChildrenClausesGenerator.numberofConstantsToCreate];
    		for (int i = 0; i < ChildrenClausesGenerator.numberofConstantsToCreate; i++) { // Task is not yet assigned when instance created, so need an extra call.  Plus good to all a resetting of all instance variables.
    			constantsToUse[i] = stringHandler.getStringConstant("WillConst" + (i + 1));  // Need something that is unlikely to also appear in a clause "of its own right."  Also, recall that these count from ONE.
    		}
    		
    	}
		return false;

	}

	private void addTheseSentences(Collection<? extends Sentence> standardSentences, InlineManager checkForInlinersAndSupportingClauses) {
		if (standardSentences == null) { return; }
		if (clauses   == null) { clauses   = new ArrayList<>(standardSentences.size()); }
		if (sentences == null) { sentences = new ArrayList<>(standardSentences);      }
		else                   { sentences.addAll(standardSentences); }
		for (Sentence s : standardSentences) {
			boolean hold = stringHandler.prettyPrintClauses;
			stringHandler.prettyPrintClauses = false;
			List<Clause> theseClauses = s.convertToClausalForm();
			stringHandler.prettyPrintClauses = hold;
			addAllMainClauses(theseClauses, checkForInlinersAndSupportingClauses);
		}
	}

	final void addAllMainClauses(List<? extends Clause> clausesToAdd, InlineManager checkForInlinersAndSupportingClauses) {
		for (Clause c : clausesToAdd) {
			addMainClause(c, checkForInlinersAndSupportingClauses);
		}	
	}

	public void addMainClause(Clause clause, InlineManager checkForInlinersAndSupportingClauses) {
		if (clause == null) { return; }
		if (clauses         == null) { clauses         = new ArrayList<>(4); }
		if (originalClauses == null) { originalClauses = new ArrayList<>(4); }
		originalClauses.add(clause);
		if (checkForInlinersAndSupportingClauses != null) {
			List<Clause> doubleResults = checkForInlinersAndSupportingClauses.handleInlinerAndSupportingClauses(clause);
			if (doubleResults == null) { Utils.error("Should not get a NULL here using: " + clause); }
			clauses.add(doubleResults.remove(0));
			for (Clause sc : doubleResults) { addSupportingClause(sc); }
		} else {
			clauses.add(clause);
		}
	}

	private void addSupportingClause(Clause clause) {
		if (clause == null) { return; }
		if (supportClauses == null) { supportClauses = new ArrayList<>(4); }
		
        boolean found = false;
        
        for (Clause aSupportClause : supportClauses) {
            if ( clause.isEquivalentUptoVariableRenaming(aSupportClause) ){
                found = true;
                break;
            }
        }

        if (!found) supportClauses.add(clause);
	}

    public List<Clause> getClauses() {
        return clauses;
    }

	public List<Clause> getSupportClauses() {
		return supportClauses;
	}
	void setSupportClauses(List<Clause> supportClauses) {
		this.supportClauses = supportClauses;
	}

	void setClauses(List<Clause> clauses) {
		this.clauses= null;  
		addAllMainClauses(clauses, inlineHandler);
	}

	public String toPrettyString() {
		return toPrettyString("", Integer.MIN_VALUE, null);
	}
	protected String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		StringBuilder str = new StringBuilder(newLineStarter); // No weights on theories - instead they are on sentences.
		if (Utils.getSizeSafely(clauses) < 1) {
			if (Utils.getSizeSafely(supportClauses) > 0) { Utils.error("There are SUPPORTING clauses, but no regular clauses!  Supporters: " + supportClauses); }
			return "% There are no clauses in this theory.";
		}
		boolean firstTime = true;
		int counter = 1;
		for (Clause clause : clauses) {	
			if (firstTime) { firstTime = false; str.append("\n% ").append(newLineStarter).append("Clauses:\n\n"); }
			str.append(newLineStarter).append(printClause(clause, newLineStarter)).append(" // Clause #").append(counter++).append(".\n\n");
		}
		firstTime = true;
		counter   = 1;
		if (Utils.getSizeSafely(supportClauses) > 0) for (Clause clause : supportClauses) {	
			if (firstTime) { firstTime = false; str.append("\n% ").append(newLineStarter).append("Supporting Clauses:\n\n"); }
			str.append(newLineStarter).append(printClause(clause, newLineStarter)).append(" // Supporting Clause #").append(counter++).append(".\n\n");
		}
		firstTime = true;
		counter   = 1;
		boolean haveSimplified = somethingSimplified && (Utils.getSizeSafely(unsimplifiedClauses) +  Utils.getSizeSafely(unsimplifiedSupportClauses) > 0);
		if (haveSimplified) { str.append("\n/* Before Simplification:\n"); }
		else { return str.toString(); }
		if (Utils.getSizeSafely(unsimplifiedClauses) > 0) for (Clause clause : unsimplifiedClauses) {
			if (firstTime) { firstTime = false; str.append("\n% ").append(newLineStarter).append("Unsimplified Clauses:\n\n"); }
			str.append(newLineStarter).append(printClause(clause, newLineStarter)).append(" // Clause #").append(counter++).append(".\n\n");
		}	
		firstTime = true;
		counter   = 1;	
		if (Utils.getSizeSafely(unsimplifiedSupportClauses) > 0) for (Clause clause : unsimplifiedSupportClauses) {	
			if (firstTime) { firstTime = false; str.append("\n% ").append(newLineStarter).append("Unsimplified Supporting Clauses:\n\n"); }
			str.append(newLineStarter).append(printClause(clause, newLineStarter)).append(" // Supporting Clause #").append(counter++).append(".\n\n");
		}
		str.append("\n*/");
		return str.toString();
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return toPrettyString("", precedenceOfCaller, bindingList);
	}


    private String printClause(Clause clause, String newLineStarter) {
        return PrettyPrinter.print(clause, "", newLineStarter, getPrettyPrinterOptions(), null);

    }

    private PrettyPrinterOptions getPrettyPrinterOptions() {
        if ( prettyPrinterOptions == null ) {
            prettyPrinterOptions = new PrettyPrinterOptions();
            prettyPrinterOptions.setMaximumLiteralsPerLine(1);
            prettyPrinterOptions.setAlignParathesis();
            prettyPrinterOptions.setRenameVariables(true);
            prettyPrinterOptions.setNewLineAfterOpenParathesis();
            prettyPrinterOptions.setMaximumIndentationAfterImplication(5);
            prettyPrinterOptions.setNewLineAfterImplication(true);
        }

        return prettyPrinterOptions;
    }

	@Override
    public Theory applyTheta(Map<Variable, Term> bindings) {
    	// TODO Auto-generated method stub
		// TODO(@hayesall): `applyTheta` in `FOPC.Theory` raises an error.
    	Utils.error("Theory applyTheta");
    	return this;
    }

    @Override
    public Iterator<Sentence> iterator() {
        return sentences.iterator();
    }


    @Override
    public String toString() {
		return toPrettyString("", 0, null);
    }

	@Override
    public int countVarOccurrencesInFOPC(Variable v) {
    	return 2; // TODO - might want to do a real count, but for now we don't want to make any of these variable anonymous anyway.
    }

}
