package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.ILP.ChildrenClausesGenerator;
import edu.wisc.cs.will.ILP.InlineManager;
import edu.wisc.cs.will.Utils.MapOfLists;
import edu.wisc.cs.will.Utils.Utils;

import java.io.IOException;
import java.io.Serializable;
import java.util.*;

/*
 * @author shavlik
 *
 * A 'theory' is a collection of first-order predicate calculus sentences, represented (for us) in clausal form.
 * 
 */
public class Theory extends AllOfFOPC implements Serializable, Iterable<Sentence> {

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
	
	transient public HandleFOPCstrings stringHandler;

	private PredicateName sameAsPname;
	private PredicateName sameAsPnameIL;
	private PredicateName differentPname;
	private PredicateName differentPnameIL;
	private PredicateName numberPname;
	private PredicateName interNumbPname;
	private PredicateName interSymPname;
	private PredicateName interListPname;
	private PredicateName interCompoPname;
	private PredicateName diff_interNumbPname;
	private PredicateName diff_interSymPname;
	private PredicateName diff_interListPname;
	private PredicateName diff_interCompoPname;
	private PredicateName notPname;
	private FunctionName  notFname;

    private PrettyPrinterOptions prettyPrinterOptions = null;
	
	public Theory(HandleFOPCstrings stringHandler) {
		this.clauses              = null;
		this.stringHandler        = stringHandler;
		collectNeededNames();
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

	private void collectNeededNames() {
    	sameAsPname      = stringHandler.getPredicateName("sameAs");
    	sameAsPnameIL    = stringHandler.getPredicateName("sameAsIL"); // NOTE: this is some leakage of the BL project into WILL.
    	differentPname   = stringHandler.getPredicateName("different");
    	differentPnameIL = stringHandler.getPredicateName("differentIL"); // NOTE: this is some leakage of the BL project into WILL.
    	numberPname      = stringHandler.standardPredicateNames.number;
    	interNumbPname   = stringHandler.getPredicateName("isaInterestingNumber");
    	interSymPname    = stringHandler.getPredicateName("isaInterestingSymbol");
    	interListPname   = stringHandler.getPredicateName("isaInterestingList");
    	interCompoPname  = stringHandler.getPredicateName("isaInterestingComposite"); // NOTE: this is some leakage of the BL project into WILL.
    	diff_interNumbPname  = stringHandler.getPredicateName("isaDifferentInterestingNumber");
    	diff_interSymPname   = stringHandler.getPredicateName("isaDifferentInterestingSymbol");
    	diff_interListPname  = stringHandler.getPredicateName("isaDifferentInterestingList");
    	diff_interCompoPname = stringHandler.getPredicateName("isaDifferentInterestingComposite"); // NOTE: this is some leakage of the BL project into WILL.
    	notPname             = stringHandler.standardPredicateNames.negationByFailure;
    	notFname             = stringHandler.standardPredicateNames.negationByFailureAsFunction;
    }

	// This assumes any desired inlining etc. has already been done.
	public Theory simplify() {
		collectAnyRemainingInliners();  // if (Utils.getSizeSafely(clauses) > 0) Utils.waitHere("check collectAnyRemainingInliners printouts above, if any");
    	if (unsimplifiedClauses != null) { Utils.warning("Have already simplified the clauses.");  return this; }
    	unsimplifiedClauses        = clauses;
    	unsimplifiedSupportClauses = supportClauses;
    	clauses        = simplify(unsimplifiedClauses);
    	supportClauses = simplify(unsimplifiedSupportClauses);
    	return this;
    }
    
	private List<Variable> newNegListVars = null;
    private List<Clause> simplify(List<Clause> theseClauses) {
    	if (theseClauses == null) { return null; }
    	List<Clause> results = new ArrayList<>(4);
    	somethingSimplified  = false;
    	newNegListVars       = null; // I am not sure why this is outside the clause FOR loop, but that is the way it was when simplifyListOfLiterals's code was pulled out (to allow recursion), and so I left it that way (7/30/10).
    	for (Clause cRaw : theseClauses) {
    		Clause c = useDeterminateLiteralsToUnifyVariables(cRaw);
    		List<Literal> newNegLits = simplifyListOfLiterals(c.negLiterals);

			Clause newC = stringHandler.getClause(c.posLiterals, newNegLits, c.getExtraLabel());
    		results.add(newC);
    	}
    	return results;
    }
    
    // It is possible some in-liners are still in a theory (eg, due to some bug).
    // So if a theory is to 'stand alone' in a new task, we need to keep the definitions of these in-liners.
    private boolean haveCollectedRemainingInLiners = false;
    private final Set<Clause> collectedSupporters = new HashSet<>(4);
    private void collectAnyRemainingInliners() {
    	if (haveCollectedRemainingInLiners) { return; }
    	collectedSupporters.clear();
    	help_collectAnyRemainingInliners(clauses,        1);
    	help_collectAnyRemainingInliners(supportClauses, 1);
    	if (!collectedSupporters.isEmpty()) {
    		supportClauses.addAll(collectedSupporters);
    	   	collectedSupporters.clear();
    	}
    	haveCollectedRemainingInLiners = true;    	
    }
    
    private void help_collectAnyRemainingInliners(List<Clause> theseClauses, int depth) {
    	if (theseClauses == null) { return; }
    	if (depth > 20) { for (Clause cRaw : theseClauses) { Utils.println("help_collectAnyRemainingInliners: " + cRaw); } Utils.error("depth = " + depth); }
    	for (Clause cRaw : theseClauses) {
			if (cRaw.negLiterals != null) for (Literal lit : cRaw.negLiterals) { help_collectAnyRemainingInliners(lit, depth + 1); }
    	}
    }
    
    private void help_collectAnyRemainingInliners(Clause cRaw, int depth) {
    	if (cRaw == null) { return; }
    	if (depth > 20) { Utils.error("cRaw = " + cRaw + " depth = " + depth); }
    	if (cRaw.negLiterals != null) for (Literal lit : cRaw.negLiterals) { help_collectAnyRemainingInliners(lit, depth + 1); }
    }
    	
    private void help_collectAnyRemainingInliners(Literal lit, int depth) {
		PredicateName pName = lit.predicateName;
		if (depth > 20) {  Utils.error("help_collectAnyRemainingInliners: lit = '" + lit + "' depth = " + depth); }

		if (pName.isaInlined(lit.getArity()) && inlineHandler == null)  { 
			Utils.warning("An in-line handler should have been associated with this theory ...  Needed for: " + lit);
		}  
		
		if (pName.isaInlined(lit.getArity()) && inlineHandler != null) {
			  				
			Iterable<Clause> definingClauses = inlineHandler.getHornClauseKnowledgeBase().getPossibleMatchingBackgroundKnowledge(lit, new BindingList());
			
			// ACTUALLY I THINK IT IS OK TO HAVE ANY NUMBER, SINCE WE'RE KEEPING THEM ALL:
			if (definingClauses != null) for (Clause inlinedDefn : definingClauses) { 
			
				List<Clause> inlinedDefnInList = new ArrayList<>(1);
				inlinedDefnInList.add(inlinedDefn);
				// TODO(?): this recursive step needs to be cleaned up.  Eg, here might not need to make a support clause but could inline the body.
				help_collectAnyRemainingInliners(inlinedDefnInList, depth + 1); // Need to make sure the inliner's body contains nothing that needs to be in-lined.
				Utils.println("%  Theory.help_collectAnyRemainingInliners(lit): add this clause" + inlinedDefn); 
				collectedSupporters.add(inlinedDefn);
			}
		}
		if (lit.getArity() > 0) for (Term term : lit.getArguments()) { help_collectAnyRemainingInliners(term, depth + 1); }
    }
    
    private void help_collectAnyRemainingInliners(Term term, int depth) {
		if (depth > 20) {  Utils.error("help_collectAnyRemainingInliners: term = '" + term + "' depth = " + depth); }

    	if (term instanceof LiteralAsTerm) {
    		LiteralAsTerm lat = (LiteralAsTerm) term;
    		help_collectAnyRemainingInliners(lat.itemBeingWrapped, depth + 1);    		
    	} else if (term instanceof SentenceAsTerm) {
    		SentenceAsTerm sat = (SentenceAsTerm) term;
    		help_collectAnyRemainingInliners(sat.asClause(), depth);    		
    	} else if (term instanceof ListAsTerm) {
    		ListAsTerm lat = (ListAsTerm) term;
    		List<Term> terms = lat.objects;
    		for (Term latTerm : terms) { help_collectAnyRemainingInliners(latTerm, depth + 1); }    		
    	} else if (term instanceof ObjectAsTerm) {
    		ObjectAsTerm oat = (ObjectAsTerm) term;
    		Utils.waitHere("ObjectAsTerm? " + oat);    	// Probably OK to simply NOT recur into this.	
    	} else if (term instanceof Function) {
    		Function f = (Function) term;
    		help_collectAnyRemainingInliners(f.convertToLiteral(stringHandler), depth + 1);
    	
    		if (f.getArity() > 0) for (Term termInner : f.getArguments()) { help_collectAnyRemainingInliners(termInner, depth + 1); }
    	}
    }
    
    private List<Literal> simplifyListOfLiterals(List<Literal> inputList) {
    	if (inputList == null) { return null; }
		List<Literal> newNegLits     = new ArrayList<>(inputList.size());
    	List<Literal> newNegLitsHold = null;
		for (Literal nLit : inputList) {
			boolean saveIt = true;

			if (nLit.predicateName == notPname && nLit.numberArgs() == 1) { // See if we have not(not(something)) and convert to 'something'.
				Term arg = nLit.getArgument(0);

				if (arg instanceof Function) {
					Function f = (Function) arg;
					if (f.functionName == notFname) {
						if (f.numberArgs() != 1) {
							Utils.error("Have a double negation: '" + f + "'  but with more than one argument.");
						}
						Term argNotNot = f.getArgument(0);
						if (argNotNot instanceof SentenceAsTerm) {
							SentenceAsTerm satNotNot = (SentenceAsTerm) argNotNot;
							List<Clause> clausesNotNot    = satNotNot.sentence.convertToClausalForm();
							List<Clause> simplifiedNotNot = simplify(clausesNotNot);
							if (simplifiedNotNot != null) for (Clause cNotNot : simplifiedNotNot) {
								if (Utils.getSizeSafely(cNotNot.posLiterals) == 0 && cNotNot.negLiterals != null) {
									newNegLits.addAll(cNotNot.negLiterals);
									saveIt = false; continue;
								}
								Utils.waitHere("Have a double negation: '" + f + "'  that needs to be handled.");
								// Could just let it go?
							}
						} else if (argNotNot instanceof Function) {
							Literal lit =  ((Function) argNotNot).convertToLiteral(stringHandler);
							newNegLits.add(lit);
							continue;
						} else {
							Utils.waitHere("Have a double negation: '" + f + "'  that needs to be handled."); // Do we need to handle other types of XYZasTerm?
							// Could just let it go?
						}
					}
				}
			}
			
			if (canPrune(nLit, newNegLits)) {
				continue;
			}
			
			if (nLit.predicateName == numberPname && nLit.numberArgs() == 1 && nLit.getArgument(0) instanceof NumericConstant) {
				continue;
			}
			
			// These are only used at learning time to introduce some constants into the hypothesis space.
			if (nLit.numberArgs() == 1 && (nLit.predicateName == interNumbPname || nLit.predicateName == interSymPname || nLit.predicateName == interListPname || nLit.predicateName == interCompoPname)) {
				continue;
			}
			
			// For the binary case, we need to use a sameAs/2.  We don't want to replace, at least for numbers, since we want to support partial matches.
			if (nLit.numberArgs() == 2 && (nLit.predicateName == interNumbPname || nLit.predicateName == interSymPname || nLit.predicateName == interListPname || nLit.predicateName == interCompoPname)) {
				Literal nLitSameAs = nLit.copy(false);
				nLitSameAs.predicateName = (nLit.predicateName == interCompoPname ? sameAsPnameIL : sameAsPname);
				newNegLits.add(nLitSameAs);
				continue;
			}
			
			// Different's need to be treated in a more complicated manner, since we cannot bind a variable with them (whereas in sameAs/2 we can).
			if (nLit.numberArgs() == 2 && (nLit.predicateName == diff_interNumbPname || nLit.predicateName == diff_interSymPname || nLit.predicateName == diff_interListPname || nLit.predicateName == diff_interCompoPname)) {
				Literal nLitDifferent = nLit.copy(false);
				nLitDifferent.predicateName = (nLit.predicateName == diff_interCompoPname ? differentPnameIL : differentPname);
				Term arg2 = nLit.getArgument(1); // NOTE: this code assumes the creators of these put the variable in the second argument.
				if (arg2 instanceof Variable) {
					if (newNegLitsHold == null) {
						newNegLitsHold = new ArrayList<>( 1);
						newNegListVars = new ArrayList<>(1);
					}
					newNegLitsHold.add(nLitDifferent);
					newNegListVars.add((Variable) arg2); // The clause has to FIRST bind this variable before different/2 can be called.
				}
				continue;
			}
			
			if (saveIt) for (Literal savedLit : newNegLits) {
				if (savedLit.equals(nLit, false)) {
					saveIt = false; break;
				}
			}
			
			if (saveIt) { newNegLits.add(nLit); } else { somethingSimplified = true; }
		}

		if (newNegLitsHold != null) {
			newNegLits.addAll(newNegLitsHold); // Could put these in the 'right' spot, but for now just stick on at the end.
		}
		if (newNegLits.size() < 1) { newNegLits.add(stringHandler.trueLiteral); } // Could propagate this 'true' but it is an unlikely case and so don't bother.
		return newNegLits;
    }
    
    private Clause useDeterminateLiteralsToUnifyVariables(Clause c) {
    	if (c == null || Utils.getSizeSafely(c.negLiterals) < 1) { return c; }
    	Map<PredicateName,List<Literal>> samePredicates = new HashMap<>(4);
    	// First group literals by predicateName
		return c;
	}

	///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	private StringConstant[] constantsToUse = null; // These are used to replace variables when matching for pruning.
    private BindingList      cachedBindingListForPruning; // Used if any pruning is being considered.
    private Clause           numberedBodyForPruning;      // Also used when pruning.
    
    private boolean canPrune(Literal lit, List<Literal> body) {
    	
    	PredicateName pName = lit.predicateName;
    	if (pName == stringHandler.standardPredicateNames.lt || pName == stringHandler.standardPredicateNames.lte) {
    		Term arg0 = lit.getArgument(0);
    		Term arg1 = lit.getArgument(1);
    		
    		if (arg0 instanceof NumericConstant) {
				NumericConstant nc = (NumericConstant) arg0;
				if (nc.value.doubleValue() == Double.NEGATIVE_INFINITY) { return true; }
    		}
    		if (arg1 instanceof NumericConstant) {
				NumericConstant nc = (NumericConstant) arg1;
				if (nc.value.doubleValue() == Double.POSITIVE_INFINITY) { return true; }
    		}
    	}
    	if (pName == stringHandler.standardPredicateNames.gt || pName == stringHandler.standardPredicateNames.gte) {
    		Term arg0 = lit.getArgument(0);
    		Term arg1 = lit.getArgument(1);
    		
    		if (arg0 instanceof NumericConstant) {
				NumericConstant nc = (NumericConstant) arg0;
				if (nc.value.doubleValue() == Double.POSITIVE_INFINITY) { return true; }
    		}
    		if (arg1 instanceof NumericConstant) {
				NumericConstant nc = (NumericConstant) arg1;
				if (nc.value.doubleValue() == Double.NEGATIVE_INFINITY) { return true; }
    		}
    	}
    	
    	if (constantsToUse == null) {
    		constantsToUse = new StringConstant[ChildrenClausesGenerator.numberofConstantsToCreate];
    		for (int i = 0; i < ChildrenClausesGenerator.numberofConstantsToCreate; i++) { // Task is not yet assigned when instance created, so need an extra call.  Plus good to all a resetting of all instance variables.
    			constantsToUse[i] = stringHandler.getStringConstant("WillConst" + (i + 1));  // Need something that is unlikely to also appear in a clause "of its own right."  Also, recall that these count from ONE.
    		}
    		
    	}
		MapOfLists<PredicateNameAndArity,Pruner> allPruners = lit.predicateName.getPruners(lit.getArity());
    	if (allPruners == null) { return false; }
    	
    	putPartialBodyInFormForPruning(lit, body);
    	Literal     initNumberedLit = (cachedBindingListForPruning == null ? lit             : lit.applyTheta(cachedBindingListForPruning.theta));
		BindingList newBL           = bindVarsToUniqueConstants(initNumberedLit);
		Literal     fixedLit        = initNumberedLit.applyTheta(newBL.theta);

		// See if NULL is one of the pruners (NULL means nothing in the body needs to match).
		List<Pruner>  prunersMatchingNULL = allPruners.getValues(null);
		if (prunersMatchingNULL != null) for (Pruner p : prunersMatchingNULL) {
			if (p.truthValue != 0 && p.isaMatch(fixedLit, null)) {
				if (p.truthValue < 0) { 
					Utils.warning("% Have a literal that is said to evaluate to FALSE!\n lit = " + lit + "'\n% pruner: " + p); 
					return false; // Don't prune these since then they'd be treated as TRUE.  Could add 'false' but seems good to see the offending literal.
				}
				Utils.println("% CAN PRUNE '" + lit + "' [" + fixedLit + "] because of pruner: " + p);
				return true; 
			}
		}

		if (body == null) { return false; }

		List<Literal> numberedClauseBody = numberedBodyForPruning.negLiterals;	
		int parentBodyLength = numberedClauseBody.size();
		for (int bodyCounter = 0; bodyCounter < parentBodyLength; bodyCounter++) {
			Literal       numberedBodyLit = numberedClauseBody.get(bodyCounter);
			List<Pruner>  matchingPruners = allPruners.getValues(numberedBodyLit.getPredicateNameAndArity());
			if (matchingPruners != null) for (Pruner p : matchingPruners) {
				if (p.truthValue != 0 && p.isaMatch(fixedLit, numberedBodyLit)) { 
					if (p.truthValue < 0) { Utils.warning("% Have a literal in clause that is said to evaluate to FALSE!\n lit = " + lit + "\n%   pruner: " + p + "\n%   clause body: " + body); continue; }
					Utils.println("% Can prune '" + lit + "' because of exiting literal '" + body.get(bodyCounter) + "' [" + numberedBodyLit + "] and pruner: " + p);
					return true; 
				}
    		}
    	}
    	return false;
    }

    private void putPartialBodyInFormForPruning(Literal lit, List<Literal> body) {
		List<Literal>  pos = new ArrayList<>(1); pos.add(lit);
		Clause      clause = stringHandler.getClause(pos, body);
		clause.collectFreeVariables(null);
		BindingList     bl = clause.copyAndReplaceVariablesWithNumbers(constantsToUse);
		cachedBindingListForPruning = bl;
		numberedBodyForPruning      = (bl == null ? clause : clause.applyTheta(bl.theta));
	}

	private BindingList bindVarsToUniqueConstants(Literal lit) {
		BindingList          result      = new BindingList();
		Collection<Variable> newVars     = lit.collectFreeVariables(null);		
		if (newVars != null) {
			int currentPositionInConstants = (cachedBindingListForPruning == null ? 0 : cachedBindingListForPruning.theta.size());
			for (Variable newVar : newVars) { 
				result.addBinding(newVar, constantsToUse[currentPositionInConstants++]); // If we get an error here, look at Clause.copyAndReplaceVariablesWithNumbers (seems unlikely we'll ever have more than 100 unique variables in a clause ...).
			}
		}
		return result;
	}

	private void addTheseSentences(Collection<? extends Sentence> standardSentences, InlineManager checkForInlinersAndSupportingClauses) {
		if (standardSentences == null) { return; }
		if (clauses   == null) { clauses   = new ArrayList<>(standardSentences.size()); }
		if (sentences == null) { sentences = new ArrayList<>(standardSentences);      }
		else                   { sentences.addAll(standardSentences); }
		for (Sentence s : standardSentences) {
			Boolean hold = stringHandler.prettyPrintClauses;
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
        BindingList bl = null;
        if ( renameVariablesWhenPrinting ) {
            bl = new BindingList();
        }
		return toPrettyString("", Integer.MIN_VALUE, bl);
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

	public void addPreAndPostfixToTemporaryNames(String prefixForSupportClause, String postfixForSupportClause) {
		if (clauses != null) for (Clause c : clauses) { // These are the main clauses.  Don't rename them (shouldn't happen since should not be in renameTheseSupportingPredicates), but check their bodies.
			for (int i = 0; i < c.getLength(); i++) {
				Literal lit = c.getIthLiteral(i);
				if (lit.predicateName == stringHandler.standardPredicateNames.negationByFailure) {
					renameNegationByFailure(lit, prefixForSupportClause, postfixForSupportClause);
				} else { 
					renameLiteralIfTemporary(lit, prefixForSupportClause, postfixForSupportClause);
				}
			}
		}
		if (supportClauses != null) for (Clause c : supportClauses) { // These are the supporting clauses.  Rename them, plus check their bodies.
			for (int i = 0; i < c.getLength(); i++) {
				Literal lit = c.getIthLiteral(i);
				if (lit.predicateName == stringHandler.standardPredicateNames.negationByFailure) {
					renameNegationByFailure(lit, prefixForSupportClause, postfixForSupportClause);
				} else {
					renameLiteralIfTemporary(lit, prefixForSupportClause, postfixForSupportClause);
				} //else { Utils.println("% THIS IS NOT A TEMPORARY NAME AND SO NO PRE/POST-FIX ADDED: " + lit.predicateName); }
			}
		}		
	}
	
	private void renameNegationByFailure(Literal negationByFailure, String prefixForSupportClause, String postfixForSupportClause) {

        Clause contents = negationByFailure.getStringHandler().getNegationByFailureContents(negationByFailure);

        for (Literal contentsLiteral : contents.getPositiveLiterals()) {
            renameLiteralIfTemporary(contentsLiteral, prefixForSupportClause, postfixForSupportClause);
        }
	}
		
	// This should all be done IN-PLACE.
	private void renameLiteralIfTemporary(Literal lit, String prefixForSupportClause, String postfixForSupportClause) {
		if (lit.predicateName.isaTemporaryName(lit.numberArgs())) {
			lit.predicateName = stringHandler.getPredicateName(prefixForSupportClause + lit.predicateName + postfixForSupportClause);
		}
		renameFunctionsIfTemporary(lit.getArguments(), prefixForSupportClause, postfixForSupportClause);
	}
	private void renameFunctionsIfTemporary(List<Term> arguments, String prefixForSupportClause, String postfixForSupportClause) {
		if (arguments != null) for (Term t : arguments) if (t instanceof Function) {
			Function      f            = (Function) t;
			PredicateName pNameVersion = stringHandler.getPredicateName(f.functionName.name);
			
			// Need to recur inside functions.
			renameFunctionsIfTemporary(f.getArguments(), prefixForSupportClause, postfixForSupportClause);
			// And need to change the function name as well, IF it is a temporary name.
			if (pNameVersion.isaTemporaryName(f.numberArgs())) {
				f.functionName = stringHandler.getFunctionName(prefixForSupportClause + f.functionName + postfixForSupportClause);
			}
		}
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
        BindingList bl = null;
        if ( renameVariablesWhenPrinting ) {
            bl = new BindingList();
        }

        return toPrettyString("", 0, bl);
    }

   /* Methods for reading a Object cached to disk.
    */
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        if (!(in instanceof FOPCInputStream)) {
            throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject input stream must support FOPCObjectInputStream interface");
        }
        in.defaultReadObject();

        FOPCInputStream fOPCInputStream = (FOPCInputStream) in;

        this.stringHandler = fOPCInputStream.getStringHandler();
    }

    @Override
    public int countVarOccurrencesInFOPC(Variable v) {
    	return 2; // TODO - might want to do a real count, but for now we don't want to make any of these variable anonymous anyway.
    }

}
