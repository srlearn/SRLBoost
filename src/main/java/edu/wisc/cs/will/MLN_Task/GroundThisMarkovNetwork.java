package edu.wisc.cs.will.MLN_Task;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.LiteralComparator;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.Utils.CrossProductViaContinuation;
import edu.wisc.cs.will.Utils.Utils;

/**
 * "Semantic" differences in Lazy Inference (compared to normal inference):
 * 
 * 		lazy does not RANDOMIZE all the literals at the start (since there could be too many)
 * 
 * 		lazyMCSAT does not RANDOMIZE all non-selected literals (since there could be too many)
 * 			- but it does randomize all materialized gLits, which include the QUERY literals (since
 * 				this is needed in order to properly estimate their marginal probabilities)
 * 
 * Explicitly ground all 'small' clauses (if sum too large?) - call this set A
 * Collect all clauses that need to be treated lazily - call this set B
 * 
 * 
 * HANDLE LAZY BLOCKS ...
 * 
 * 
 *
 * UW Lazy Notes (finally got around to writing them)
 * -------------
 * 
 *  currently do not make QUERY literals lazy (we assume there arent too many of these)
 *  
 *  use 'marked' instead of 'active' since 'active' has another meaning in SAT
 *  
 *  Smart Randomization (using 1-neighbors)
 *  	initialize all those variables in the same clauses as marked variables
 *  
 *  Collecting a RANDOM GROUND LITERAL without enumerating them all
 *  	pick a literal proportional to the # of groundings it has
 *  	uniformly choose constants for the arguments in this literal
 *  
 *  for MCSAT, explicitly collect all CLAUSE GROUNDINGS NOT SATISFIED
 *  
 *  
 *  if a lazy clause has not been selected for K somethings, discard it
 *  
 *   have to note at parent this clause has been de-materialized!  <------------------
 *   addToGroundClauseIndex <------ dont use for LAZY's
 *   
		if (i < numberOfLazyGroundLiterals) {
			return allLazyGroundLiterals.get(i); 
 * 
 *
 *  
 * SIMPLIFY INFERENCE IF THE QUERY IS SIMPLER THAN THE REDUCED FROG NETWORK!
 * 
 * BUG: facts in BK file dont get properly handled for MLN stuff!
 * 
 * if doing WGT LEARNING need to keep individual
 * 
 * 
 * set a flag in ILP saying MLN being used, or (better) factor out common stuff
 * 
 * AGGREGATE COMMON CLAUSES
 * 	- use 'canonical form' here
 * 	- parents will be wrong (use special marker for "AggParent")
 *  - first merge SINGLETONS and see how much saved, dont forget sign * 
 * 
 *  
 * when getting a grounding GET ALL COPIES!
 * 
 * use queryPred when read from files ...
 * 
 * if MCSAT sets are small fractions of all, then use PUSH after all?
 * 
 * HOW BEST TO CHOOSE FOR DUP GROUNDINGS!
 * 
 * 
 * when in SampleSAT, can we avoid creating ALL explicitly?
 * (and if we DONT, then why not use the non-lazy SampleSAT?)
 * 
 * We are finding the prob a lit is true averaged over all worlds that (quasi) satisfy the given BK
 * 
 * LazySampleSAT same as regular!
 * 
 * isInCurrentActiveClauseList
 * 
 * should use isSatisfiedCached() in non-lazy, make sure flips update clauses, dont explicitly connect, let the ground clause stuff do that
 * 
 * do more printouts more non-lazy
 * 
 * merge the lazy/non-lazy inference classes
 * 
 * is there some way to expand ALL ground clauses from 'small' reduced clauses?
 * 		could expand and never gc
 * 		but better would be to have a LIST OF PERM gndClauses and another of Lazy!
 * 		(always do everything over both!)
 * 		add smallest to FIXED until reaching some threshold
 * 
 * 
 * if too many queries, then rep their counts as a SPARSE vector!
 * 
 * 
 * GroundClauses and GroundLiterals point to each other; when erasing, should clear these or no GC will happen!
 * 
 * What gets cleaned up between samples?
 * 
 * BE SURE TO CHECK FOR MORE GROUND CLAUSES WHEN A LITERAL IS "TENURED"
 * Record which clause groundings have been tenured.
 * Record when a clause has exhausted all of its groundings
 * 
 * periodically clear the cache of ground literals of then rebuild all those currently active
 * 
 * when can we GARBAGE COLLECT
 * 	- literals that have their default value
 *  - clauses that (a) are true and (b) have no saved literals
 *  NOTE: if we remove a literal, we need to remove it from the list of created ground literals
 * 
 * 
 * NEED FASTER seeIfBestCost - have two arrays for all the gLits?
 * 
 * WHEN POPPING THE STACK, DO WE WANT TO KEEP THE STATE OF *ALL* THE CLAUSES AND LITERALS?
 *   - seems we need to bring in the other clauses that contain literals turned ON!
 *   
 *   NEED TO STORE STATE FOR SAMPLESAT
 * 
 * DECIDE ON THE SA TEMP BASED ON SCORE
 * 
 * TO WRITE
 *    updateLazyDataStructures - needed?
 *    
 *    do more efficient way of flipping other literals in active clauses!
 * 
 * NEED TO FIX BLOCKS
 * 
 * NEED TO HAVE WGT-LEARNING USE LAZY INFERENCE!
 * 
 * 	fix non-lazy push/pop?
 * 
 * Notes: 'arity' in comments in this file really means 'number of unique variables [in a literal].'
 * 			Be sure to NOT copy literals nor clauses here, since used as key's into hash tables.
 *  
 * SEARCH FOR: JWSJWSJWS
 * 
 * See the following for an alternate approach:
 *   H. Poon, P. Domingos, and M. Sumner,
 *   A General Method for Reducing the Complexity of Relational Inference and its Application to MCMC
 *   AAAI-08 http://www.cs.washington.edu/homes/pedrod/papers/aaai08c.pdf
 *   
 *   TODO - add in http://en.wikipedia.org/wiki/Unit_propagation (into MS-SAT?)
 *   
 *   		possible to do exact inference on some clauses?  just return all their items if few!
 *      
 *      	once grounded out, need to account for the 'lost' groundings (TRUEs and FALSEs)
 *      		- eg, wgt learning needs this to be correct (are there only TRUEs?  if not, then probably ok)
 *      
 *   		NEED TO DEAL WITH BLOCKS - test better?
 *   		NEED TO HANDLE FUNCTIONS IN LITERALS (here or in MLN_Task)
 *   		when to store FALSEs instead of TRUEs?  never?
 *   TODO TODO
 *   
 *   
 *   need to create ALL query literals before doing inference ...
 *   
 *   if too big, then do not do all final groundings.  Instead auto use 'lazy'
 *   
 *   	should not do full cross product unless small!
 *   	- instead, count size, then walk through the KNOWN values (counting 'unknowns' according to CWA)   
 *   	   
 *     could cache    predicateName/constants for 1-arity predicates, or maybe for all predicates
 *     					but this is order dependent after the first one
 *   
 *   	Allow the network to grow to included additional clauses
 *   		- and/or figure out how N clauses interact ...
 *   	SHOULD CLEVERLY HANDLE  p(x,y) and ~p(y,z) ??
 *  


 * 
 * @author shavlik
 *
 */
public class GroundThisMarkovNetwork {
	public static final int      debugLevel   = 1;//Integer.MIN_VALUE;

	public  MLN_Task             task;
	Object             markerInUse = null;  // Can mark ground clauses with their 'owners,' for cases where only a subset of the groundings currently are of interest.

	private boolean              postponeSavingGroundLiterals  = true;  // If true, will not archive ground literals until they need to be saved (a space-time tradeoff, when set to 'true' saves space at a cost of more new'ing).
	private double               maxNumberClauseGroundings           = 1e8; // This is a PER CLAUSE value.  Should be less than Integer.MAX_VALUE since it is compared to a *.size() calculation.
	private Collection<Clause>   allClauses;
	private Map<Clause,Integer>  clauseToIndex;
	private Map<Clause,Double>   countOfTRUEs; // Counts can be large, so use Double's.
	private Map<Clause,Double>   countOfFALSEs;
	private Map<Clause,Double>   countOfSatisfiableGndClauses;
	private Map<Clause,Double>   largestSizeOfStoredGroundings;
	private Map<Clause,Double>   largestCrossProductCreated;
	Set<Clause>          stillTooLargeAfterReduction; // Collect those clauses that have too many groundings.
	double               totalNumberOfGroundingsRemaining = -1; // Sum over all clauses.

	private Map<PredicateName,Map<Term,List<List<Term>>>> allPosEvidenceIndexed; // Hash by predicate name and first argument for faster lookup. 
	private Map<PredicateName,Map<Term,List<List<Term>>>> allNegEvidenceIndexed; // Terms used here so no need to cast Literal arguments to Constants.
	private Map<PredicateName,Map<Term,List<List<Term>>>> allQueriesIndexed;
	private Map<PredicateName,Map<Term,List<List<Term>>>> allHiddensIndexed;
	private Map<PredicateName,Set<Integer>>               allPosEvidencePredNames; // Hashed so faster lookups than with PredicateNameArityPair's.
	private Map<PredicateName,Set<Integer>>               allNegEvidencePredNames;
	private Map<PredicateName,Set<Integer>>               allQueryPredNames;
	private Map<PredicateName,Set<Integer>>               allHiddenPredNames;
	
	// What to do if some constants of a given type don't appear at all?
	//	if CWA=true AND clause has at least one negative literal, then clause is true by CWA
	//  else if CWA=true and clause has no negative literals, then clause is false for all of these (and no need to count).
	//  if CWA=false then clause is false and no need to count.
	private Map<Clause,Map<Literal,List<Integer>>> firstVariableAppearance; // If lit=p(1,x,x,y,x,2,y,z) then this should be {0, 1, -1, 3, -1, 0, -3, 8} where 0 means 'constant,' a positive number N means "first occurrence of a variable in position N (counting from 1), and -N means "subsequent appearance of variable that first appeared in position N." 
	
	private Map<Clause,Set<Literal>>                literalsToKeep;        // Should not be duplicates here.
	private Map<Clause,Set<Literal>>                literalsStillToReduce; // These are the literals that still need to be reduced.
	private Map<Clause,Set<Literal>>                literalsRejectedForReduction; // These are the literals that did not have a high-enough reduction (and hence would have increased the storage size too much).
	private Map<Clause,Set<Variable>>               accountedForVariables; // These variables in the clauses have been accounted for (in a final cleanup phase) and should not impact the size of the set of groundings.
	private Map<Clause,Map<Literal,List<Variable>>> freeVarsMap; // Need to be a list, since we want to maintain order.

	private Map<Clause,Set<Literal>> literalAlwaysInPosEvidence; // When a literal matches pName/arity information, store in these for convenient access.
	private Map<Clause,Set<Literal>> literalAlwaysInNegEvidence;
	private Map<Clause,Set<Literal>> literalAlwaysInQuery;
	private Map<Clause,Set<Literal>> literalAlwaysHidden;
	private Map<Clause,Set<Literal>> literalsContainingConstants;

	// This group is what is needed for inference (TODO see if any more - or could be less).
	private Map<Clause,Map<Variable,VariableIndexPair>>    aggregatorMap;
	private Map<Clause,Map<Variable,Set<Term>>>        varsToConstantsMap; // OK to use SET here since no duplicate constants.
	private Map<Clause,Map<AggVar,List<List<Term>>>>   aggVarsToAggregatedConstantsMap; // Need to NOT remove duplicates since this might be a reduction from a longer list of variables, and we need to not lose counts (e,g., [a,b,c] and [a,b,d] might reduce to [[a,b], [a,b]]).  So cannot use SETs.  The variables here are AGGREGATED variables.
	private Map<Clause,Map<Literal,CacheLiteralGrounding>> litsToConstantsMap; // Cache all of the groundings of this literal.
	private Map<Clause,Set<Variable>>                      variablesInClause;  // Want a SET here since we do not want any duplicates.
	private Map<Clause,Set<Variable>>                      variablesRemainingInClause;  // After reduction, record which variables still remain.
	private Map<Clause,Double>                             multiplierPerSatisfiedClause; //Each satisfied state represents this many groundings (used when some variable(s) cannot satisfy the clause, but we still need to count all the combinations).

	private Map<Clause,Integer>                          cycle_when_solved; // Record when a clause was fully reduced.  Two pieces of information are stored.  A number like 12007 (12000 + 7) means that on the 12th overall 'trial' it was solved on the 7th iteration. 
	
	private BindingList bl  = new BindingList(); // Save some memory usage by reusing this.
	private Literal     trueLit;
	private Literal     falseLit;
	private int         numberOfClausesToAnalyze;
	private Set<Clause> doneWithThisClause;
	private Term        variableInFactMarker;

	private Set<PredicateName>    factsWithVariables;
	private Set<PredicateName>    procedurallyDefinedPredicatesInUse;
	private Unifier               unifier;
	
	private Set<Term>                 dummySingletonSetOfConstants = new HashSet<>(4); // Needed as a place holder for aggregated variables.
	private Map<Clause,Long>              totalLiteralGroundingsConsidered;
	private Map<Clause,Map<Literal,Long>> totalLiteralGroundingsConsideredThisLiteral;
	private int[]                         emptyIntList = new int[0];

	// These are used AFTER reduction (unless doing LAZY inference).
	private ArrayList<GroundLiteral>      allGroundLiterals         = null; // Depending on the query being asked
	private ArrayList<GroundClause>       allGroundClauses          = null;
	private ArrayList<GroundLiteral>      allGroundLiteralsOrig     = null; // We specify ArrayList because we want speedy, random access.  Do NOT remove duplicates here, since the same reduced clause can arise from different original clauses.
	private ArrayList<GroundClause>       allGroundClausesOrig      = null;
	private Map<Clause,Set<GroundClause>> allGroundClausesPerClause = null;

	// Keep a CANONICAL collection of ground clauses.
	Map<Integer,List<GroundClause>> hashOfGroundClauses = new HashMap<>(4);

	GroundThisMarkovNetwork(MLN_Task task, Collection<Clause> allClauses) {
		this.task       = task;
		// Each clause will be COPIED.  In one copy, reduction is on the TRUEs; on the other reduction is on the FALSEs.
		this.allClauses = new ArrayList<>(allClauses); // Play it safe and get a fresh copy.  Plus, this way we can be sure it is an array list (assuming that matters somewhere ...).
		this.unifier    = task.unifier;  // Since can be called a lot, create a direct pointer.
		clauseToIndex   = new HashMap<>(4);
		int counter = 0;
		for (Clause clause : allClauses) { clauseToIndex.put(clause, ++counter); } // NOTE: if we sort later, to work on clauses according to their #groundings, these counts will change!
		dummySingletonSetOfConstants.add(task.stringHandler.getStringConstant("PlaceHolderConstant"));
		trueLit                 = task.stringHandler.trueLiteral;
		falseLit                = task.stringHandler.falseLiteral;
		variableInFactMarker    = task.stringHandler.getStringConstant("VarInThisFact");
		allQueriesIndexed       = new HashMap<>(4);
		allPosEvidenceIndexed   = new HashMap<>(4);
		allNegEvidenceIndexed   = new HashMap<>(4);
		allHiddensIndexed       = new HashMap<>(4);
		allQueryPredNames       = new HashMap<>(4);
		allPosEvidencePredNames = new HashMap<>(4);
		allNegEvidencePredNames = new HashMap<>(4);
		allHiddenPredNames      = new HashMap<>(4);
		hashSetOfFacts(task.getQueryLiterals(),        allQueriesIndexed);
		hashSetOfFacts(task.getPosEvidenceLiterals(),  allPosEvidenceIndexed);
		hashSetOfFacts(task.getNegEvidenceLiterals(),  allNegEvidenceIndexed);
		hashSetOfFacts(task.getHiddenLiterals(),       allHiddensIndexed);
		hashPredNames( task.getQueryPredNames(),       allQueryPredNames);
		hashPredNames( task.getPosEvidencePredNames(), allPosEvidencePredNames);
		hashPredNames( task.getNegEvidencePredNames(), allNegEvidencePredNames);
		hashPredNames( task.getHiddenPredNames(),      allHiddenPredNames);
		// Record which clauses throw an error for needing too many cpu cycles or storage.

		numberOfClausesToAnalyze      = allClauses.size();
		doneWithThisClause            = new HashSet<>(4);  // Do NOT reset this when restarting since once DONE, no need to continue
		countOfTRUEs                  = new HashMap<>(4);
		countOfFALSEs                 = new HashMap<>(4);
		countOfSatisfiableGndClauses  = new HashMap<>(4);
		multiplierPerSatisfiedClause  = new HashMap<>(4);
		largestSizeOfStoredGroundings = new HashMap<>(4);
		largestCrossProductCreated    = new HashMap<>(4);
		literalsToKeep                = new HashMap<>(4);
		literalsStillToReduce         = new HashMap<>(4);
		literalsRejectedForReduction  = new HashMap<>(4);
		variablesInClause             = new HashMap<>(4);
		variablesRemainingInClause    = new HashMap<>(4);
		accountedForVariables         = new HashMap<>(4);
		literalAlwaysInQuery          = new HashMap<>(4);
		literalAlwaysHidden           = new HashMap<>(4);
		literalAlwaysInPosEvidence    = new HashMap<>(4);
		literalAlwaysInNegEvidence    = new HashMap<>(4);
		literalsContainingConstants   = new HashMap<>(4);
		varsToConstantsMap            = new HashMap<>(4);
		freeVarsMap                   = new HashMap<>(4);
		litsToConstantsMap            = new HashMap<>(4);
		aggregatorMap                 = new HashMap<>(4);
		aggVarsToAggregatedConstantsMap             = new HashMap<>(4);
		totalLiteralGroundingsConsidered            = new HashMap<>(4);
		totalLiteralGroundingsConsideredThisLiteral = new HashMap<>(4);
		firstVariableAppearance                     = new HashMap<>(4);

		// Other versions of this literal (in ANY clause) can share these results, assuming the variable is not yet in singletonVarsInClauseProcessed.  The first item in the list is the result for the NEGATED literal as the second is for the UNNEGATED one.

		// Information to save about the best solution found so far (if we do multiple restarts).
		// Information to save about the best solution found so far (if we do multiple restarts).

		cycle_when_solved                     = new HashMap<>(4);
		
		resetAllInstanceVariables();
	}

	private void resetAllInstanceVariables() { // If isaReset=true, then can CLEAR data instead of NEW'ing.
		for (Clause clause : allClauses) {
			// Start over if not done and a reset.
			countOfTRUEs.put(                clause,  0.0);
			countOfFALSEs.put(               clause,  0.0);
			multiplierPerSatisfiedClause.put(clause,  1.0);
			countOfSatisfiableGndClauses.put( clause, -1.0); // This indicates that the first setting of this is not a 'change.'  (Minor detail in terms of status reporting via println's.)
			cycle_when_solved.put(            clause, -1);   // Indicates 'not yet done.'  Be sure to only set this at the start.
			largestSizeOfStoredGroundings.put(clause, 0.0); // Calculate this over ALL retries (maybe have another pair of variables that are PER TRIAL?).
			largestCrossProductCreated.put(clause, 0.0);
			totalLiteralGroundingsConsidered.put(clause, (long)0);
			freeVarsMap.put(clause, new HashMap<>(4));
			firstVariableAppearance.put(clause, new HashMap<>(4));
			totalLiteralGroundingsConsideredThisLiteral.put(clause, new HashMap<>(4));
			litsToConstantsMap.put(clause, new HashMap<>(4));

			// The remainder need to be reset for each new trial.
			accountedForVariables.put(clause, new HashSet<>(4));
			variablesInClause.put(clause, new HashSet<>(4));
			varsToConstantsMap.put(clause, new HashMap<>(4));
			aggregatorMap.put(clause, new HashMap<>(4));
			aggVarsToAggregatedConstantsMap.put(clause, new HashMap<>(4));
			literalsToKeep.put(       clause, new HashSet<>(4));
			literalsStillToReduce.put(clause, new HashSet<>(4));
			literalsRejectedForReduction.put(clause, new HashSet<>(4));
			if (clause.posLiterals != null) for (Literal  pLit : clause.posLiterals) {
				literalsToKeep.get(               clause).add(pLit); // Initially put everything in here, then remove if no longer needed.
				literalsStillToReduce.get(        clause).add(pLit);
				initializeVariablesInLiteralsInfo(clause, pLit);
			}
			if (clause.negLiterals != null) for (Literal  nLit : clause.negLiterals) {
				literalsToKeep.get(               clause).add(nLit);
				literalsStillToReduce.get(        clause).add(nLit);
				initializeVariablesInLiteralsInfo(clause, nLit);
			}
			countCurrentCombinatorics(clause);
		}
	}


	private void initializeVariablesInLiteralsInfo(Clause clause, Literal lit) {
		// Look for new variables in this literal, and if any found collect all of the possible groundings.
		List<TypeSpec> typeSpecs = task.collectLiteralArgumentTypes(lit);
		if (lit.numberArgs() != Utils.getSizeSafely(typeSpecs)) { Utils.error("Mismatch for " + wrapLiteral(clause, lit) + "  numbArgs=" + lit.numberArgs() + " typeSpecs=" + typeSpecs); }
		// Simultaneously walk through the arguments and the types.
		// Only collect if the argument is a variable that is not already bound.  Also if a variable appears multiple times, only collect it once.
		for (int i = 0; i < lit.numberArgs(); i++) {
			Type type = typeSpecs.get(i).isaType;
			Term term = lit.getArgument(i);			
			if (term instanceof Variable  && !isaSkolem(term)) {
				Variable var = (Variable) term;  // Skip if this variable has already been encountered.						
				if (variablesInClause.get(clause).add(var)) { // Returns true if NOT already there.
					Set<Term> cList = task.getReducedConstantsOfThisType(type); // Collect all the constants of this type.
					varsToConstantsMap.get(clause).put(var, cList);
				}
			}
		}
	}
	
	private boolean isaSkolem(Term term) {
		return task.setOfSkolemMarkers.contains(term);
	}
	
	private CacheLiteralGrounding countLiteralGroundings(Clause clause, Literal lit, boolean pos) throws MLNreductionProblemTooLargeException {
		CacheLiteralGrounding cached = litsToConstantsMap.get(clause).get(lit); // See if this literal's groundings have been cached.
		if (cached != null) {
			if (debugLevel > 1) { Utils.println("%    Using CACHED grounding results for " + wrapLiteral(clause, lit) + "."); }
			return cached; 
		}		
		
		Collection<Variable> freeVariables = freeVarsMap.get(clause).get(lit);
		if (Utils.getSizeSafely(freeVariables) < 1) { Utils.error("Should not handle zero-arity literals here."); }
		CacheLiteralGrounding result = createFullCrossProductFromTheseVariables(clause, lit, pos, freeVariables, emptyIntList);
		litsToConstantsMap.get(clause).put(lit, result);
		return result;
	}

	private double savingsDueToUseOfKnowns = 0.0;
	private long   excessChecks            = 0;
	private long   currentExcessChecks     = 0;
	private Collection<Term> skolemsInLiteralUnderConsideration = null; // Using this instead of passing extra arguments.
	// This method is a bit complex, because it only collects combinations that need to be kept.  Otherwise some large candidate list could be generated, only to be discarded later.  NOTE: still might GENERATE a lot, but at least most won't be saved.

	private CacheLiteralGrounding createFullCrossProductFromTheseVariables(Clause clause, Literal literalInUse, boolean pos, Collection<Variable> freeVariables, int[] positionsOfArgumentsInLiteralToUse) throws MLNreductionProblemTooLargeException {
		return help_createFullCrossProductFromTheseVariables(clause, literalInUse, pos, freeVariables, positionsOfArgumentsInLiteralToUse);
	} 
	// Sometimes we need to collect all the groundings for a literal (e.g, after initial processing [see collectAndCacheRemainingGroundings], so provide a flag that supports this.
	// When simplyCollectAllGroundings=true, the counts need not be accurate.

	private CacheLiteralGrounding help_createFullCrossProductFromTheseVariables(Clause clause, Literal literalInUse, boolean pos, Collection<Variable> freeVariables, int[] positionsOfArgumentsInLiteralToUse) throws MLNreductionProblemTooLargeException {
		if (Utils.getSizeSafely(freeVariables) < 1) { 
			if (containsVariables(literalInUse)) { Utils.error("There should be no free variables in this literal, but the literalInUse has variables: " + wrapLiteral(clause, literalInUse) + "."); }
			return createCacheLiteralGroundingFromVariableFreeClause(literalInUse, pos);
		}
		
		if (debugLevel > 1) { Utils.println("%      Need to create a cross product of all the groundings of these variables: " + freeVariables + " in " + wrapLiteral(clause, literalInUse) + "."); }
		Set<Variable>        unAggregatedVars    = null; // Only used for debugging, so can delete later.
		Set<Variable>          aggregatedVars    = null; // Only used for debugging, so can delete later.
		List<AggVar>         aggregatorsNeeded   = null;
		int                  numbFreeVariables   = Utils.getSizeSafely(freeVariables);
		Collection<Variable> freeVarsInLit       = (literalInUse == null ? null : freeVarsMap.get(clause).get(literalInUse));
		int                  numbFreeVarsInLit   = Utils.getSizeSafely(freeVarsInLit);
		List<Set<Term>>  allArgPossibilities = new ArrayList<>(numbFreeVariables);  // Order matters for the outer list, since it needs to match the order of the arguments, but the order constants appear doesn't matter.
		Map<Term,Integer> mapVariablesToPositionInAggregatorList = null; // If there are aggregators, we need to know their position in aggregatorsNeeded.
		if (debugLevel > 1) { Utils.print("%      Will be doing a 'brute force' cross product over these unaggregated variables ["); }
		// For each free variable, either collect it in unAggregatedVars or record which aggregator holds it.
		if (Utils.getSizeSafely(freeVariables) > 0) for (Variable var : freeVariables) {
			if (aggregatorMap.get(clause).get(var) == null) { // Only do the first cross product for the unaggregated variables.
				Set<Term> groundingsOfThisVariable = varsToConstantsMap.get(clause).get(var);
				if (debugLevel > 1) { Utils.print(" " + var); }
				allArgPossibilities.add(groundingsOfThisVariable);
				if (unAggregatedVars  == null) { unAggregatedVars  = new HashSet<>(4); }
				unAggregatedVars.add(var);
			} else {
				if (aggregatedVars    == null) {   aggregatedVars  = new HashSet<>(4); }
				if (aggregatedVars.contains(var)) { Utils.error("Already have '" + var + "' in aggregatedVars=" + aggregatedVars); } // Should never happen, but check anyway.
				aggregatedVars.add(var);
				if (aggregatorsNeeded == null) { aggregatorsNeeded = new ArrayList<>(1); }
				AggVar aggVar = aggregatorMap.get(clause).get(var).aggVar;
				if (!aggregatorsNeeded.contains(aggVar)) { // Collect the aggregators.
					aggregatorsNeeded.add(aggVar);
					if (mapVariablesToPositionInAggregatorList == null) { mapVariablesToPositionInAggregatorList = new HashMap<>(4); }
					if (mapVariablesToPositionInAggregatorList.containsKey(var)) { Utils.error("Already have '" + var + "' in " + mapVariablesToPositionInAggregatorList); }
					mapVariablesToPositionInAggregatorList.put(var, aggregatorsNeeded.size() - 1);
				} else { // Walk through the existing aggregators and record which one 'owns' this variable.
					for (int i = 0; i < aggregatorsNeeded.size(); i++) { 
						if (aggVar == aggregatorsNeeded.get(i)) { mapVariablesToPositionInAggregatorList.put(var, i); break; }
					}
				}
				allArgPossibilities.add(dummySingletonSetOfConstants); // Need to keep the arity the same.
			}
		}	
		if (debugLevel > 1) { Utils.println(" ]."); }
				
		CrossProductViaContinuation<Term> basicVarCrossProduct = new CrossProductViaContinuation(allArgPossibilities);
		double origSizeOfCrossProduct = Math.max(1.0, basicVarCrossProduct.sizeOfCrossProduct);
		double fullSizeOfCrossProduct = origSizeOfCrossProduct;  // Includes the sizes of the aggregators.

		int numbOfAggregators = Utils.getSizeSafely(aggregatorsNeeded);
		List<List<List<Term>>> allAggArgPossibilities = null;
		if (numbOfAggregators > 0) { // Now need to merge in any aggregated variables.
			if (debugLevel > 1) { Utils.println("%      Need to process these " + numbOfAggregators + " aggregators: " + aggregatorsNeeded + "."); }
			allAggArgPossibilities = new ArrayList<>(numbOfAggregators);
			assert aggregatorsNeeded != null;
			for (AggVar aggVar : aggregatorsNeeded) {
				List<List<Term>> aggregatorListOfLists = aggVarsToAggregatedConstantsMap.get(clause).get(aggVar);
				if (debugLevel > 1) { Utils.println("% **** Aggregator '" + aggVar + "' has bindings = " + Utils.limitLengthOfPrintedList(aggregatorListOfLists, 5)); }
				allAggArgPossibilities.add(aggregatorListOfLists);
				fullSizeOfCrossProduct *= aggregatorListOfLists.size();
				if (debugLevel > 1) { Utils.println("%      Will be expanding the current cross product (size=" + Utils.truncate(origSizeOfCrossProduct, 0) + "), using the " +  Utils.comma(aggregatorListOfLists.size()) + " items of aggregator '"
														+ aggVar + "', for a total new size of aggregators of " + Utils.truncate(fullSizeOfCrossProduct,  0) + "."); }
			}
		}

		CrossProductViaContinuation<List<Term>> crossProductOfAggregatedVars = new CrossProductViaContinuation(allAggArgPossibilities);
		double sizeOfAggVarCrossProduct  = Math.max(1.0, crossProductOfAggregatedVars.sizeOfCrossProduct);	
		if (sizeOfAggVarCrossProduct > largestCrossProductCreated.get(clause)) { largestCrossProductCreated.put(clause, sizeOfAggVarCrossProduct); }
		if (debugLevel > 2) { Utils.println("%      |crossProduct| = " + Utils.truncate(origSizeOfCrossProduct, 0) + ",  |crossProductOfAggregatedVars| = " + Utils.truncate(sizeOfAggVarCrossProduct, 0) + ", and |total| = " + Utils.truncate(fullSizeOfCrossProduct, 0)); } 
		
		// Now collect those combinations that need to be retained.
		List<List<Term>> bindingsToKeep = new ArrayList<>(1);	// Note: need to NOT return NULL unless we didn't collect all the groundings.  Cannot use List<Term> since getNextCrossProduct will return a LIST and need to add those to this list.
		int  debugCounter = 0; int maxDebugCounter = 3;//debugLevel; // Used to limit printing in debugging runs.
		long trueCount    = 0; // NOTE: these counts are for the literal in question IGNORING ITS SIGN (other code deals with that).
		long falseCount   = 0;
		long unknownCount = 0;
		long countOfLitGroundings = 0;	
		
		// Cannot use for literals where facts contains variables, since there we need to generate the combinations.
		Collection<GroundLiteral> queryKnowns       = null; // Defer setting these until we're sure they are needed.
		Collection<GroundLiteral> hiddenKnowns      = null;
		Collection<GroundLiteral> posEvidenceKnowns = null;
		Collection<GroundLiteral> negEvidenceKnowns = null;
		long numberOfKnowns = Long.MAX_VALUE;
		// Can walk through the knowns if we are not collecting all groundings (since then we should exactly be generating what we need)
		//      and we're not forced to collect all remaining groundings (or cwa=true and literal is negated - in this case, any implicit groundings satisfy the clause and hence need not be generated).
		// Also note that cannot uses this when this literal's predicate name involves any facts with variables.
		assert literalInUse != null;
		boolean considerKnowns = ((factsWithVariables == null || !factsWithVariables.contains(literalInUse.predicateName)));
		if (considerKnowns) {
			queryKnowns       = (task.isClosedWorldAssumption(literalInUse) ? task.getQueryKnowns( literalInUse) : null); // If CWA=false, anything not in the positive or negative lists is assumed to be unknown anyway, so no need to check.
			hiddenKnowns      = (task.isClosedWorldAssumption(literalInUse) ? task.getHiddenKnowns(literalInUse) : null);
			posEvidenceKnowns =  task.getPosEvidenceKnowns(literalInUse);
			negEvidenceKnowns =  task.getNegEvidenceKnowns(literalInUse);
			numberOfKnowns = Utils.getSizeSafely(queryKnowns) + Utils.getSizeSafely(hiddenKnowns) + Utils.getSizeSafely(posEvidenceKnowns) + Utils.getSizeSafely(negEvidenceKnowns);
			if (debugLevel > 2) { Utils.println("% lit = " + wrapLiteral(clause, literalInUse) + "  |fullSizeOfCrossProduct| = " + Utils.truncate(fullSizeOfCrossProduct, 0) + "  |totalNumberOfKnowns| = " +  Utils.comma(numberOfKnowns) + "    |queryKnowns| = " +  Utils.comma(queryKnowns) + "   |hiddenKnowns| = " +  Utils.comma(hiddenKnowns) + "   |posKnowns| = " +  Utils.comma(posEvidenceKnowns) + "   |negKnowns| = " +  Utils.comma(negEvidenceKnowns)); }
		}
		// HOWEVER IF THE CROSS-PRODUCT SIZE EXCEEDS THIS SIZE, USE KNOWNS IF POSSIBLE.
		double maxCrossProductSizeToUseKnownsRegardless = 1e7;
		// Processing known's can be slow, so skip if too many.
		double maxNumberOfKnownsToConsider = 1e5;
		// If the explicit size is no more fraction of the size of the 'knowns,' use the explicit cross product since more efficient.
		double multiplierOnSizeOfExplicitCrossProduct = 0.20;
		if (considerKnowns && // See if substantially cheaper to walk through the knowns than the explicit cross product.
					(numberOfKnowns < maxNumberOfKnownsToConsider || fullSizeOfCrossProduct > maxCrossProductSizeToUseKnownsRegardless) &&
					 numberOfKnowns < multiplierOnSizeOfExplicitCrossProduct * fullSizeOfCrossProduct / 2) { // If not less than half the size, don't use this short cut.		
			if (numberOfKnowns > largestCrossProductCreated.get(clause)) { largestCrossProductCreated.put(clause, (double) numberOfKnowns); }

			currentExcessChecks = 0; // See how many UNNEEDED checks are done.

			Utils.println("% mapVariablesToPositionInAggregatorList = " + mapVariablesToPositionInAggregatorList +
						  "  free variables = "                         + freeVariables +
						  "  |basicVarCrossProduct| = "                 + Utils.truncate(basicVarCrossProduct.sizeOfCrossProduct, 0) +
						  "  |crossProductOfAggregatedVars| = "         + Utils.truncate(crossProductOfAggregatedVars.sizeOfCrossProduct, 0) +
						  "  |aggVarIndexes| = "                        + Utils.getSizeSafely((Collection<?>) null));
			int progressCounter = 0; int frequency = 1000;
			if (queryKnowns       != null) for (GroundLiteral gLit : queryKnowns)       { 
				countOfLitGroundings++; // Seems fair to count all the knowns considered as part of the count of groundings considered.
				if (debugLevel > 1 && ++progressCounter % frequency == 0) { Utils.println("%   At " + Utils.comma(progressCounter) + " in the query knowns for " + wrapLiteral(clause, literalInUse) + "."); }
				if (gLitArgumentsStillExistInVariableCrossProducts(clause, literalInUse, positionsOfArgumentsInLiteralToUse, mapVariablesToPositionInAggregatorList, gLit, basicVarCrossProduct, aggregatorsNeeded, crossProductOfAggregatedVars)) { unknownCount++;           bindingsToKeep.add(extractConstants(clause, literalInUse, gLit)); }
			}
			progressCounter = 0;
			if (hiddenKnowns      != null) for (GroundLiteral gLit : hiddenKnowns)      { 
				countOfLitGroundings++;
				if (debugLevel > 1 && ++progressCounter % frequency == 0) { Utils.println("%   At " + Utils.comma(progressCounter) + " in the hidden knowns for " + wrapLiteral(clause, literalInUse) + "."); }
				if (gLitArgumentsStillExistInVariableCrossProducts(clause, literalInUse, positionsOfArgumentsInLiteralToUse, mapVariablesToPositionInAggregatorList, gLit, basicVarCrossProduct, aggregatorsNeeded, crossProductOfAggregatedVars)) { unknownCount++;           bindingsToKeep.add(extractConstants(clause, literalInUse, gLit)); }
			}
			progressCounter = 0;
			if (posEvidenceKnowns != null) for (GroundLiteral gLit : posEvidenceKnowns) { 
				countOfLitGroundings++;
				if (debugLevel > 1 && ++progressCounter % frequency == 0) { Utils.println("%   At " + Utils.comma(progressCounter) + " in the pos-evidence knowns for " + wrapLiteral(clause, literalInUse) + "."); }
				if (gLitArgumentsStillExistInVariableCrossProducts(clause, literalInUse, positionsOfArgumentsInLiteralToUse, mapVariablesToPositionInAggregatorList, gLit, basicVarCrossProduct, aggregatorsNeeded, crossProductOfAggregatedVars)) { trueCount++;  if (!pos) { bindingsToKeep.add(extractConstants(clause, literalInUse, gLit)); }}
			}
			progressCounter = 0;
			if (negEvidenceKnowns != null) for (GroundLiteral gLit : negEvidenceKnowns) { 
				countOfLitGroundings++;
				if (debugLevel > 1 && ++progressCounter % frequency == 0) { Utils.println("%   At " + Utils.comma(progressCounter) + " in the neg-evidence knowns for " + wrapLiteral(clause, literalInUse) + "."); }
				if (gLitArgumentsStillExistInVariableCrossProducts(clause, literalInUse, positionsOfArgumentsInLiteralToUse, mapVariablesToPositionInAggregatorList, gLit, basicVarCrossProduct, aggregatorsNeeded, crossProductOfAggregatedVars)) { falseCount++; if ( pos) { bindingsToKeep.add(extractConstants(clause, literalInUse, gLit)); }}
			}
			if (debugLevel > 2) { Utils.println("% FULL SIZE = " + Utils.truncate(fullSizeOfCrossProduct, 0) + "   unknownCount=" + Utils.comma(unknownCount) + " trueCount=" + Utils.comma(trueCount) + " falseCount=" + Utils.comma(falseCount)); }
			double implicitGroundings = fullSizeOfCrossProduct - (unknownCount + trueCount + falseCount);
			if (implicitGroundings > 0) {
				if (task.isClosedWorldAssumption(literalInUse)) {
					if (debugLevel > 0) { Utils.println("%       Since cwa=true, moving all " + Utils.truncate(implicitGroundings, 0) + " implicit groundings to the FALSE category."); }
					falseCount += implicitGroundings;
				} else {
					unknownCount += implicitGroundings;
				}
				savingsDueToUseOfKnowns += implicitGroundings; // Did not need to look at any of these.
				if (debugLevel > 0) { Utils.println("%  *** Was able to skip " + Utils.truncate(implicitGroundings, 0) + " groundings due to looking only at the " + Utils.comma(numberOfKnowns) + " known groundings for " + wrapLiteral(clause, literalInUse) + ".  Total savings so far: " + Utils.truncate(savingsDueToUseOfKnowns, 0) + ".'"); }
			}
			if (currentExcessChecks > 0) {
				excessChecks += currentExcessChecks;
				if (debugLevel > 0) { Utils.println("%  *** Considered  " + Utils.comma(currentExcessChecks) +
													  " groundings that weren't in the cross products, due to looking only at all the known groundings for " + wrapLiteral(clause, literalInUse) + ".  Total excess checks so far: " + Utils.truncate(excessChecks, 0) + ".'"); }
			}
		} else {
			// Don't join if result will exceed this number (in bindings considered).
			double maxJoinSizeComputation = 1e8;
			if (fullSizeOfCrossProduct > maxJoinSizeComputation) {
				throw new MLNreductionProblemTooLargeException(null);
			}
			if (fullSizeOfCrossProduct > largestCrossProductCreated.get(clause)) { largestCrossProductCreated.put(clause, fullSizeOfCrossProduct); }
			while (!basicVarCrossProduct.isEmpty()) {
				List<Term> bindings  = basicVarCrossProduct.getNextCrossProduct(); // Expand this binding using all the items in aggregatorListOfLists.
				boolean        firstTime = true; // If crossProductOfAggregatedVars is empty, we still need to do through the WHILE once.
				crossProductOfAggregatedVars.reset(); // Need to start this 'inner loop' afresh each time the outer loop is called.
				while (firstTime || !crossProductOfAggregatedVars.isEmpty()) { //  // Collect all the combinations for the aggregated variables.
					List<List<Term>> argVarLists = crossProductOfAggregatedVars.getNextCrossProduct();
					List<Term>       newBindings = new ArrayList<>(bindings); // Get a fresh COPY. Do not REUSE, since these will be collected plus getNextCrossProduct reuses the same memory cells.
					
					if (firstTime) { firstTime = false; }
					// Now walk through each aggregator and correctly fill in the positions in newBindings.
					if (argVarLists != null) for (int argNumber = 0; argNumber < numbFreeVariables; argNumber++) { // Walk through the variables in this literal and see which need to get their values from an aggregator.
						Variable basicVar                      = Utils.getIthItemInCollectionUnsafe(freeVariables, argNumber);
						assert mapVariablesToPositionInAggregatorList != null;
						Integer  aggVarPositionForThisBasicVar = mapVariablesToPositionInAggregatorList.get(basicVar);	// Indexes into argVarList.
						
						if (aggVarPositionForThisBasicVar != null) { // See if this variable is owned by some aggregator.
							assert aggregatorsNeeded != null;
							AggVar            aggVar               = aggregatorsNeeded.get(aggVarPositionForThisBasicVar);
							VariableIndexPair pair                 = aggregatorMap.get(clause).get(basicVar);
							List<Term>    argVarListForThisVar = argVarLists.get(aggVarPositionForThisBasicVar);
							if (debugLevel > 2 && debugCounter < maxDebugCounter)    { 
								Utils.println("%            Var '" + basicVar + "' is aggregated by aggregator var '" + aggVar + "'.  ArgVarListForThisVar = " + argVarListForThisVar + ".");
								Utils.println("%              Have this pair for arg #" + argNumber + ": index=" + pair.index + " for aggVar = " + pair.aggVar + ".");
							}
							if (argNumber < Utils.getSizeSafely(newBindings)) {
								if (pair.index < Utils.getSizeSafely(argVarListForThisVar)) {
									newBindings.set(argNumber, argVarListForThisVar.get(pair.index));
								} else { Utils.warning(" pair.index = " + pair.index + " argVarListForThisVar.size() = " + Utils.getSizeSafely(argVarListForThisVar)); }
							} else { Utils.warning(" argNumber = " + argNumber + " newBindings.size() = " + Utils.getSizeSafely(newBindings)); }
						} else if (debugLevel > 2 && debugCounter < maxDebugCounter) { Utils.println("%            Var '" + basicVar + "' is NOT aggregated."); }
					}
					if (debugLevel > 2) { debugCounter++; }	
					
					boolean keepTheseVariables = false;
					bl.theta.clear();
					List<Variable>  freeVarsInLitAsList = (List<Variable>) freeVarsInLit;
					if (positionsOfArgumentsInLiteralToUse.length < 1) { // There is no mapping. Just pull out the variables in order.
						for (int i = 0; i < numbFreeVarsInLit; i++) {
							assert freeVarsInLitAsList != null;
							bl.addBinding(freeVarsInLitAsList.get(i), newBindings.get(i));
						}
					} else { //  // Pull out the variables for this literal from the possibly longer fullSetOfVariables, using the provided 'map.'
						for (int i = 0; i < numbFreeVarsInLit; i++) {
							assert freeVarsInLitAsList != null;
							bl.addBinding(freeVarsInLitAsList.get(i), newBindings.get(positionsOfArgumentsInLiteralToUse[i]));
						}
					}
					Literal litGroundedRaw = literalInUse.applyTheta(bl.theta);
					Literal litGrounded;
					countOfLitGroundings++;
					if (task.skolemsPerLiteral.get(literalInUse) != null) {
						litGrounded = litGroundedRaw; // Still want any other bindings.
						skolemsInLiteralUnderConsideration = task.skolemsPerLiteral.get(literalInUse); // Using a 'global' instead of passing another argument everywhere.
						if (debugLevel > 3) { Utils.println(literalInUse + " -> " + skolemsInLiteralUnderConsideration); }
					} else {
						litGrounded = task.getCanonicalRepresentative(litGroundedRaw, postponeSavingGroundLiterals); // Want to have one copy of a specific literal.
					}
					if (debugLevel > 3) { Utils.println("    bindings = " + bindings + "  BL = " + bl + "  lit = " + literalInUse + "  litGnd = " + litGrounded); }

					if (litGrounded == null) { // This grounding has not been seen.
						// IF POS AND NOT SEEN, if CWA=true, then UNSAT.  (All other pName/arity possibilities already checked.)
						// IF NEG AND NOT SEEN, if CWA=true, then   SAT.  (All other pName/arity possibilities already checked.)
						if (pos) {
							if (task.isClosedWorldAssumption(litGroundedRaw)) { falseCount++;    keepTheseVariables = true; }
							else                                              { unknownCount++;  keepTheseVariables = true; } // If CWA=false, then treat as a 'hidden' literal.
						} else {
							if (task.isClosedWorldAssumption(litGroundedRaw)) { falseCount++; } // No need to keep, since satisfied.
							else                                              { unknownCount++;  keepTheseVariables = true; } // If CWA=false, then treat as a 'hidden' literal.
						}
					} else if (pos) { // OTHERWISE WE NEED TO LOOK AT THE GROUNDED LITERAL.  If we have  p(...) and it is TRUE,  we do NOT need to keep it.
						if      (matchesPosEvidenceFast(litGrounded)) { trueCount++; }
						else if (matchesNegEvidenceFast(litGrounded)) { falseCount++;    keepTheseVariables = true; }
						else if (matchesQueryFast(      litGrounded)) { unknownCount++;  keepTheseVariables = true; } // Need to keep all literals that can be true or false (which is the case for queries).
						else if (matchesHiddenFast(     litGrounded)) { unknownCount++;  keepTheseVariables = true; } // Need to keep all literals that can be true or false (which is the case for hiddens).
						else if (isaFalseByCWAfast(     litGrounded)) { falseCount++;    keepTheseVariables = true; } // This will FAIL if the literal matches the list of hiddens.
						else                                          { unknownCount++;  keepTheseVariables = true; } // If CWA=false, then treat as a 'hidden' literal.
					} else {   // If we have ~p(...) and it is FALSE, we do NOT need to keep it.
						if      (matchesNegEvidenceFast(litGrounded)) { falseCount++; }
						else if (matchesPosEvidenceFast(litGrounded)) { trueCount++;     keepTheseVariables = true; }
						else if (matchesQueryFast(      litGrounded)) { unknownCount++;  keepTheseVariables = true; } // If a query and IN posEvidence or negEvidence, proper to let the evidence decide.
						else if (matchesHiddenFast(     litGrounded)) { unknownCount++;  keepTheseVariables = true; }
						else if (isaFalseByCWAfast(     litGrounded)) { falseCount++; }
						else                                          { unknownCount++;  keepTheseVariables = true; } // If CWA=false, then treat as a 'hidden' literal.
					}
					skolemsInLiteralUnderConsideration = null; // Need to erase this 'global' when done
					if (keepTheseVariables) {
						// No need to save in the canonical ground literal database, since we're only saving the BINDINGS.
						bindingsToKeep.add(newBindings);
						// Don't join if result will exceed this number (in size of a cross product created).
						double maxJoinSizeStorage = 1e7;
						if (bindingsToKeep.size() > maxJoinSizeStorage) {
							throw new MLNreductionProblemTooLargeException(null);
						}
					}				
				}
			}
		}

		updateCountOfTotalGroundings(clause, literalInUse, (pos ? trueCount : falseCount), countOfLitGroundings);
		if (debugLevel > 3) { Utils.println(" true=" + Utils.comma(trueCount) + " false=" + Utils.comma(falseCount) + " unknown=" + unknownCount + " |keepers|=" + Utils.comma(bindingsToKeep)); }
		return new CacheLiteralGrounding(bindingsToKeep, trueCount, falseCount, unknownCount);
	}

	// Neither this clause nor this literal have any free variables.  Create a CacheLiteralGrounding for this special case.
	private CacheLiteralGrounding createCacheLiteralGroundingFromVariableFreeClause(Literal literalInUse, boolean pos) {
		if (literalInUse == null) { Utils.error("Cannot handle literalInUse == null here."); }
		long trueCount    = 0;
		long falseCount   = 0;
		long unknownCount = 0;
		boolean keeper = false;
		assert literalInUse != null;
		if (pos) { // If we have  p(...) and it is TRUE,  we do NOT need to keep it.
			if      (matchesPosEvidence(literalInUse)) { trueCount++; }
			else if (matchesNegEvidence(literalInUse)) { falseCount++;    keeper = true; }
			else if (matchesQuery(      literalInUse)) { unknownCount++;  keeper = true; } // Need to keep all literals that can be true or false (which is the case for queries).
			else if (matchesHidden(     literalInUse)) { unknownCount++;  keeper = true; } // Need to keep all literals that can be true or false (which is the case for hidden).
			else if (isaFalseByCWAfast( literalInUse)) { falseCount++;    keeper = true; }
			else                                       { unknownCount++;  keeper = true; } // If CWA=false, then treat as a 'hidden' literal.
		} else {   // If we have ~p(...) and it is FALSE, we do NOT need to keep it.
			if      (matchesNegEvidence(literalInUse)) { falseCount++; }
			else if (matchesPosEvidence(literalInUse)) { trueCount++;     keeper = true; }
			else if (matchesQuery(      literalInUse)) { unknownCount++;  keeper = true; } // If a query and IN posEvidence or negEvidence, proper to let the evidence decide.
			else if (matchesHidden(     literalInUse)) { unknownCount++;  keeper = true; }
			else if (isaFalseByCWAfast( literalInUse)) { falseCount++; }
			else                                       { unknownCount++;  keeper = true; } // If CWA=false, then treat as a 'hidden' literal.
		}
		List<List<Term>> groundingsStillNeeded = new ArrayList<>(1); // This needs to be non-null if we WERE collecting groundings.
		if (keeper && literalInUse.numberArgs() > 0) {
			List<Term> listOfConstants = new ArrayList<>(1);
			listOfConstants.addAll(literalInUse.getArguments());
			groundingsStillNeeded.add(listOfConstants);
		}
		return new CacheLiteralGrounding(groundingsStillNeeded, trueCount, falseCount, unknownCount);
	}

	// See if this literal contains any variables.
	private boolean containsVariables(Literal literalInUse) {
		if (literalInUse.numberArgs() < 1) { return false; }
		for (Term term : literalInUse.getArguments()) {
			if (term instanceof Variable) { return true; }
			if (term instanceof Function) { Utils.error("Need to deal with functions: " + term); }
		}
		return false;
	}

	private boolean isAlwaysQuery(Clause clause, Literal literal) {
		Collection<Literal> collection = literalAlwaysInQuery.get(clause);
		if (collection == null) { return false; }
		return collection.contains(literal);
	}
	private boolean isAlwaysHidden(Clause clause, Literal literal) {
		Collection<Literal> collection = literalAlwaysHidden.get(clause);
		if (collection == null) { return false; }
		return collection.contains(literal);
	}
	private boolean isAlwaysTrue(Clause clause, Literal literal) {
		Collection<Literal> collection = literalAlwaysInPosEvidence.get(clause);
		if (collection == null) { return false; }
		return collection.contains(literal);
	}
	private boolean isAlwaysFalse(Clause clause, Literal literal) {
		Collection<Literal> collection = literalAlwaysInNegEvidence.get(clause);
		if (collection == null) { return false; }
		return collection.contains(literal);
	}

	// Reduced literals, that were not discarded because the were satisfiable for some groundings, need to be checked
	// again at the end, to see if any satisfiable groundings still remain.
	private void doFinalCheckOfRemainingLiterals(Clause clause) {
		for (Literal lit : literalsToKeep.get(clause)) {
			if (isAlwaysQuery(clause, lit)) {
				continue;
			} // These should remain, so all is fine.
			if (isAlwaysHidden(clause, lit)) {
				continue;
			} // Ditto.
			if (isAlwaysTrue(clause, lit)) {
				Utils.error("Should not happen: " + wrapLiteral(clause, lit) + " in " + clause);
			}
			if (isAlwaysFalse(clause, lit)) {
				Utils.error("Should not happen: " + wrapLiteral(clause, lit) + " in " + clause);
			}
			CacheLiteralGrounding result;
			try {
				boolean pos = clause.getSign(lit);
				result = countLiteralGroundings(clause, lit, pos);
				long trues = result.trueCount;
				long falses = result.falseCount;
				long unknowns = result.unknownCount;
				if (debugLevel > 2) {
					result.describeCache(lit.toString(Integer.MAX_VALUE));
				} // Since counts ignore sign, print that way as well.
				if (pos && trues > 0) {
					Utils.warning("Should not have any cases of " + wrapLiteral(clause, lit) + " = true here.");
				}
				if (!pos && falses > 0) {
					Utils.warning("Should not have any cases of " + wrapLiteral(clause, lit) + " = false here.");
				}
				if (unknowns == 0) {
					if (debugLevel > 0) {
						Utils.println("%      Can remove " + wrapLiteral(clause, lit) + " from consideration since it no longer has any satisfiable bindings.  Clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + "'.");
					}
				}
			} catch (MLNreductionProblemTooLargeException e) {
				// If too large, ???
				continue; // For now, just continue and deal with this later.
			}
			litsToConstantsMap.get(clause).put(lit, result);

		}
	}
	
	// Get rid of data structures not needed, especially long lists and large sets.  
	// If any groundings left:
	//      if literals left, then the remaining groundings go into SATISFIABLE (those remaining variables not in a literal left are aggregated into a multiplier for the satisfiables) 
	//	    otherwise the remaining grounds go into count of FALSEs (but we still need to know WHICH groundings make it false, so we keep these explicitly).
	private void doFinalCleanup(Clause clause) {
		if (debugLevel > 0) { Utils.println("\n%   Doing a final 'cleaning' of the information collected for clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + "'."); }
		countCurrentCombinatorics(clause); // Do this at the end in case missed earlier due to completing a clause.
		doFinalCheckOfRemainingLiterals(clause);
		
		for (Literal lit : litsToConstantsMap.get(clause).keySet()) {
			CacheLiteralGrounding cache = litsToConstantsMap.get(clause).get(lit);
			if (debugLevel > 0) { if (cache != null) { Utils.println("%   For " + wrapLiteral(clause, lit) + " still storing " + Utils.comma(cache.getGroundingsStillNeeded()) + " ground literals."); }
								  else               { Utils.println("%   For " + wrapLiteral(clause, lit) + " no literal groundings are cached."); }}
			litsToConstantsMap.get(clause).put(lit, null); // Do NOT clear here, since this might be shared.
		}
		
		for (Variable var : varsToConstantsMap.get(clause).keySet()) {
			Set<Term> setOfConstants = varsToConstantsMap.get(clause).get(var);
			if (debugLevel > 0) { if (setOfConstants != null) { Utils.println("%   For '" + var + "' still storing " + Utils.comma(setOfConstants) + " constants."); }
							      else                        { Utils.println("%   For '" + var + "' no constants are cached."); }}
			if (aggregatorMap.get(clause).get(var) != null) {
				 varsToConstantsMap.get(clause).put(var, null); // Do NOT clear here, since this might be shared.
			}
		}
		for (AggVar aggVar : aggVarsToAggregatedConstantsMap.get(clause).keySet()) {
			List<List<Term>> setOfConstants = aggVarsToAggregatedConstantsMap.get(clause).get(aggVar);
			if (debugLevel > 0) { if (setOfConstants != null) { Utils.println("%   For '" + aggVar + "' still storing " + Utils.comma(setOfConstants) + " aggregated constants."); }
							      else                        { Utils.println("%   For '" + aggVar + "' no constants are cached."); }}
		}

		Collection<Variable>              varsInClause    = variablesInClause.get( clause);
		Map<Variable,VariableIndexPair>   aggregators     = aggregatorMap.get(     clause);
		Map<Variable,Set<Term>>       oldConstants    = varsToConstantsMap.get(clause);
		Map<AggVar, List<List<Term>>> aggsToConstants = aggVarsToAggregatedConstantsMap.get(clause);
		Set<Literal>                      litsSurviving   = literalsToKeep.get(clause);
		Map<Literal,List<Variable>>       theFreeVars     = freeVarsMap.get(clause);
		double                countOfRemainingCombinations = -1.0;
		if (countOfSatisfiableGndClauses.get(clause) < 1) { // No need to keep anything other than the counts if no satisfiable groundings.
			removePointersToConstants(clause);
		} else {
			Collection<Variable> varsThatMustBeKept    = null;
			Collection<AggVar>   aggVarsThatMustBeKept = null;
			if (litsSurviving != null) for (Literal lit : litsSurviving) { // First find which variables and aggregated variables appear in surviving literals.
				Collection<Variable> freeVars = theFreeVars.get(lit);
				if (debugLevel > 1) { Utils.println("%   Free variables = " + freeVars + " for remaining literal '" + lit + "'."); }
				if (freeVars != null) for (Variable var : freeVars) {
					VariableIndexPair currentOwnerOfVar = aggregators.get(var);
					if (currentOwnerOfVar == null) {
						if (varsThatMustBeKept    == null) { varsThatMustBeKept    = new HashSet<>(4); }
						varsThatMustBeKept.add(var);
					} else {
						if (aggVarsThatMustBeKept == null) { aggVarsThatMustBeKept = new HashSet<>(  4); }
						aggVarsThatMustBeKept.add(currentOwnerOfVar.aggVar);
					}
				}
			}
			if (debugLevel > 1) { Utils.println("%    VarsThatMustBeKept    = " + varsThatMustBeKept);    }
			if (debugLevel > 1) { Utils.println("%    AggVarsThatMustBeKept = " + aggVarsThatMustBeKept); }
			
			// Now look for any other variables and aggregated variables that are still in the clause, but with no possibility of helping satisfy this clause.
			Collection<AggVar> aggregatorsUsed = null;
			if (varsInClause != null) for (Variable var : varsInClause) {
				VariableIndexPair currentOwnerOfVar = aggregators.get(var);
				// Set to true if OK to clear all data structures at the end (other than the counts).
				if (currentOwnerOfVar == null) {
					if (varsThatMustBeKept == null || !varsThatMustBeKept.contains(var)) { 
						int numberOfCombinations = oldConstants.get(var).size();
						if (countOfRemainingCombinations < 0) { countOfRemainingCombinations = 1.0; }
						countOfRemainingCombinations *= numberOfCombinations;
						if (debugLevel > 0) { Utils.println("%    Removing basic variable '" + var + "' (and accounting for its " + numberOfCombinations + " combinations), because it does not appear in the literals that remain for this clause."); }
						if (debugLevel > 1) { Utils.println("%       Removing: " + Utils.limitLengthOfPrintedList(oldConstants.get(var), 25)); }
						// Need to record which variables have been 'factored out' since otherwise it will have a size of 0 and mess up any later calls to compute the size of the cross product.
						accountedForVariables.get(clause).add(var);
					}
				} else if (aggregatorsUsed == null || !aggregatorsUsed.contains(currentOwnerOfVar.aggVar)) { // Don't double count aggregators.
					AggVar aggVar = currentOwnerOfVar.aggVar;
					if (aggVarsThatMustBeKept == null || !aggVarsThatMustBeKept.contains(aggVar)) { 
						int numberOfCombinations = aggsToConstants.get(aggVar).size(); 
						if (countOfRemainingCombinations < 0) { countOfRemainingCombinations = 1.0; }
						countOfRemainingCombinations *= numberOfCombinations;
						if (debugLevel > 0) { Utils.println("%    Removing aggregated variable '" + aggVar + "' (and accounting for its " + numberOfCombinations + " combinations), because it does not appear in the literals that remain for this clause."); }
						if (debugLevel > 1) { Utils.println("%       Removing: " + Utils.limitLengthOfPrintedList(aggsToConstants.get(aggVar), 25)); }
						accountedForVariables.get(clause).add(var);
						Utils.waitHere("cleaningUpAggVar '" + aggVar + ".");
					}
					if (aggregatorsUsed == null) { aggregatorsUsed = new HashSet<>(4); }
					aggregatorsUsed.add(aggVar);
				}
			}
		}
		if (countOfRemainingCombinations > 0) {
			if (Utils.getSizeSafely(literalsToKeep.get(clause)) > 0) {
				if (multiplierPerSatisfiedClause.get(clause) != 1.0) { Utils.error("Expecting multiplierPerSatisfiedClause.get(clause) = 1.0 but got multiplierPerSatisfiedClause.get(clause)=" + multiplierPerSatisfiedClause.get(clause)); }
				multiplierPerSatisfiedClause.put(clause, multiplierPerSatisfiedClause.get(clause) * countOfRemainingCombinations);
				countOfSatisfiableGndClauses.put(clause, countOfSatisfiableGndClauses.get(clause) / countOfRemainingCombinations);
				if (debugLevel > 1) { Utils.println("%   Cleanup completed.  Found " + Utils.truncate(countOfRemainingCombinations, 0) 
													   + " combinations involving variables not appearing in any remaining literal, so they can be factored into a multiplier for each satisfiable ground among those remaining."); }
			} else {
				countOfSatisfiableGndClauses.put(clause, countOfSatisfiableGndClauses.get(clause) - countOfRemainingCombinations); // Need to remove these from here, since it currently includes the variable being accounted for.
				if (countOfSatisfiableGndClauses.get(clause) != 0.0) { Utils.error("Expecting countOfSatisfiableGndClauses.get(clause)=0 but got countOfSatisfiableGndClauses.get(clause)=" + Utils.truncate(countOfSatisfiableGndClauses.get(clause), 0)); }
				double oldFALSEs = countOfFALSEs.get(clause);
				countOfFALSEs.put(clause, oldFALSEs + countOfRemainingCombinations);
				if (debugLevel > 1) { Utils.println("%   Cleanup completed.  Found " + Utils.truncate(countOfRemainingCombinations, 0) 
												      + " combinations that do not satisfy the clause since there are no literals remaining (previously there had been " +  Utils.truncate(oldFALSEs, 0) + " false combinations)."); }
			}
		} else if (debugLevel > 1) { Utils.println("%   Cleanup completed."); }
		Set<Variable> remainingVariables = null;
		assert litsSurviving != null;
		for (Literal lit : litsSurviving) {
			Collection<Variable> freeVars = freeVarsMap.get(clause).get(lit);
			if (Utils.getSizeSafely(freeVars) > 0) {
				if (remainingVariables == null) { remainingVariables = new HashSet<>(4); }
				remainingVariables.addAll(freeVars);
			}						
		}
		variablesRemainingInClause.put(clause, remainingVariables);
		System.gc(); // Force a garbage collection.
	}


	// See how many combinations there are using all variables in this clause's variable list EXCEPT those in the skipThese list.
	private double computeSizeOfVariableCrossProduct(Clause clause) {
		Collection<Variable>             varsInClause     = variablesInClause.get(    clause);
		if (Utils.getSizeSafely(varsInClause) < 1) { return 1.0; } // If no variables, define the size to be 1.
		Collection<Variable>             accountedForVars = accountedForVariables.get(clause);
		Map<Variable,VariableIndexPair>  aggregators      = aggregatorMap.get(        clause);
		Map<Variable,Set<Term>>      oldConstants     = varsToConstantsMap.get(   clause);
		Collection<AggVar>               aggregatorsUsed  = null; // We only want to count the size of an aggregator ONCE.
		double                           oldLargestSize   = largestSizeOfStoredGroundings.get(clause);
		double                           result           = 1.0; // Cannot use int's since could overflow.
		double                           newSize          = 0.0;
		boolean                          returnZero       = true; // See if anything still exists for this clause.
		if (debugLevel > 1) { Utils.print(" = 1"); }
		if (varsInClause == null) { return 0.0; }
		for (Variable var : varsInClause) if (!accountedForVars.contains(var)) {
			VariableIndexPair currentOwnerOfVar = aggregators.get(var);
			if (currentOwnerOfVar == null) {
				int size = Utils.getSizeSafely(oldConstants.get(var));
				returnZero = false;
				result  *= size;
				newSize += size;
				if (debugLevel > 1) { Utils.print("x" + Utils.comma(size) + "[" + var + "]"); }
			} else if (aggregatorsUsed == null || !aggregatorsUsed.contains(currentOwnerOfVar.aggVar)) { // Don't double count aggregators.
				int size = Utils.getSizeSafely(aggVarsToAggregatedConstantsMap.get(clause).get(currentOwnerOfVar.aggVar));
				returnZero = false;
				result  *= size;
				newSize += size;
				if (debugLevel > 1) { Utils.print("x" + Utils.comma(size)+ "[" + currentOwnerOfVar.aggVar + "]"); }
				if (aggregatorsUsed == null) { aggregatorsUsed = new HashSet<>(4); }
				aggregatorsUsed.add(currentOwnerOfVar.aggVar);
			}
			if (result <= 0.0 && debugLevel <= 1) { break; }  // Continue to end only if printing sizes.
		}
		if (newSize > oldLargestSize) {
			largestSizeOfStoredGroundings.put(clause, newSize); // Alas, cannot report since might be reporting the product.
		}
		if (returnZero) { if (debugLevel > 1) { Utils.print("x0[sinceNoItemsFound]"); } return 0.0; }
		return Math.max(0.0, result);
	}

	private String wrapLiteral(Literal lit, boolean pos) {
		if (pos) { return "'" + lit + "'"; }
		return "'~" + lit + "'"; 
	}		
	private String wrapLiteral(Clause clause, Literal lit) {
		return wrapLiteral(lit, clause.getSign(lit));
	}

	private void recordDoneWithThisClause(Clause clause) {
		if (doneWithThisClause.contains(clause)) { Utils.error("Already noted that done with this clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + "', solved @ " + cycle_when_solved.get(clause)); }
		doneWithThisClause.add(clause);
		int currentCycle = 0;
		// Used to count number of random restarts.
		int currentOverallIteration = 0;
		cycle_when_solved.put(clause, 1000 * currentOverallIteration + currentCycle); // Encode two pieces of information here.
		if (debugLevel > 2) { Utils.println("% **** Done with: '" + clause + "' [cycle_when_solved = " + cycle_when_solved.get(clause) + "]."); }
		numberOfClausesToAnalyze--;  if (numberOfClausesToAnalyze < 0) { Utils.error("Variable 'numberOfClausesToAnalyze' should never be negative!"); }
		if (Utils.getSizeSafely(literalsToKeep.get(clause)) < 1 && countOfSatisfiableGndClauses.get(clause) > 0) {
			if (debugLevel > 0) { Utils.println("%   Since this clause has no surviving literals, it is false for all " + Utils.truncate(countOfSatisfiableGndClauses.get(clause), 0) + " remaining groundings."); }
			clauseAlwaysFalse(clause);
		}
		doFinalCleanup(clause);
	}
	
	private void clauseAlwaysFalse(Clause clause) {
		if (debugLevel > 0) { Utils.println("%    DONE!  Handling a clause that is always FALSE for any remaining variables.  Setting number of satisfiable combinations to 0."); }
		countOfFALSEs.put(clause, countOfFALSEs.get(clause) + countOfSatisfiableGndClauses.get(clause));
		allCombinationsAccountedFor(clause);
	}

	private void allCombinationsAccountedFor(Clause clause) {
		literalsToKeep.get(       clause).clear();
		literalsStillToReduce.get(clause).clear();
		literalsRejectedForReduction.get(clause).clear(); // Can forgot about all of these if all the combinations accounted for (i.e., by other literals).
		countOfSatisfiableGndClauses.put(clause, 0.0);
		if (variablesInClause.get(clause) != null) { accountedForVariables.get(clause).addAll(variablesInClause.get(clause)); }
		if (!doneWithThisClause.contains(clause)) { recordDoneWithThisClause(clause); }
	}

	private void removePointersToConstants(Clause clause) {  // Do NOT erase lists.  They might be pointed to by others.
		if (aggregatorMap != null && aggregatorMap.get(clause) != null) for (Variable var : aggregatorMap.get(clause).keySet()) {
			aggregatorMap.get(clause).put(var, null);
		}
		if (varsToConstantsMap != null && varsToConstantsMap.get(clause) != null) for (Variable var : varsToConstantsMap.get(clause).keySet()) {
			varsToConstantsMap.get(clause).put(var, null); // Don't clear() since might still be pointing to the constants stored in task.
		}
		if (aggVarsToAggregatedConstantsMap != null && aggVarsToAggregatedConstantsMap.get(clause) != null) { aggVarsToAggregatedConstantsMap.put(clause, null); }
		if (litsToConstantsMap              != null && litsToConstantsMap.get(clause)              != null) { litsToConstantsMap.put(clause, null); }
	}
	
	private void countCurrentCombinatorics(Clause clause) {
		double oldCount = countOfSatisfiableGndClauses.get(clause);
		if (debugLevel > 0) { 
			if (oldCount < 0) { Utils.print("% Initial number of variable combinations"); }
			else              { Utils.print("%   Number of remaining variable combinations"); }			 
		}
		double currentCombinatorics = computeSizeOfVariableCrossProduct(clause);
		if (debugLevel > 0) { 
			if (oldCount < 0) {                          Utils.print(" = " + Utils.truncate(currentCombinatorics, 0)); }
			else if (currentCombinatorics == oldCount) { Utils.print(" = " + Utils.truncate(currentCombinatorics, 0) + " [unchanged]"); }
			else {                                       Utils.print(" = " + Utils.truncate(currentCombinatorics, 0) + " [" + Utils.truncate(oldCount, 0) + " previously]"); }
			Utils.println(" for clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + ".");
		}
		countOfSatisfiableGndClauses.put(clause, currentCombinatorics);
	}

	private boolean matchesQuery(      Literal lit) { return (containsPnameAndArity(lit, allQueryPredNames) || containsThisLiteral(lit, allQueriesIndexed)); }
	private boolean matchesPosEvidence(Literal lit) { return (lit.equals(trueLit,  false) || containsPnameAndArity(lit, allPosEvidencePredNames) || containsThisLiteral(lit, allPosEvidenceIndexed) || evaluateProcDefinedEvidence(lit, true )); }
	private boolean matchesNegEvidence(Literal lit) { return (lit.equals(falseLit, false) || containsPnameAndArity(lit, allNegEvidencePredNames) || containsThisLiteral(lit, allNegEvidenceIndexed) || evaluateProcDefinedEvidence(lit, false)); }
	private boolean matchesHidden(     Literal lit) { return (containsPnameAndArity(lit, allHiddenPredNames) || containsThisLiteral(lit, allHiddensIndexed)); }

	// These are to be used when we know we don't need to check the Pname/Arity databases.
	private boolean matchesQueryFast(      Literal lit) { return containsThisLiteral(lit, allQueriesIndexed); }
	private boolean matchesPosEvidenceFast(Literal lit) { return (lit.equals(trueLit,  false) || containsThisLiteral(lit, allPosEvidenceIndexed) || evaluateProcDefinedEvidence(lit, true )); }
	private boolean matchesNegEvidenceFast(Literal lit) { return (lit.equals(falseLit, false) || containsThisLiteral(lit, allNegEvidenceIndexed) || evaluateProcDefinedEvidence(lit, false)); }
	private boolean matchesHiddenFast(     Literal lit) { return containsThisLiteral(lit, allHiddensIndexed); }
	
	private boolean isaFalseByCWA(     Literal lit) { return (task.isClosedWorldAssumption(lit) && !matchesPosEvidence(lit) && !matchesQuery(lit) && !matchesHidden(lit)); }
	private boolean isaFalseByCWAfast( Literal lit) { return  task.isClosedWorldAssumption(lit); } // Fast version for use when matchesPosEvidence, matchesQuery, and matchesHidden have already been checked.

	private boolean thisPosLiteralIsSatisfied(Literal lit) {
		return matchesPosEvidence(lit);
	}
	private boolean thisNegLiteralIsSatisfied(Literal lit) {
		// Have something of the form ~p(x,y,z) in a clause. 
		// We know it is satisfied if p(x,y,z) is in the negative evidence.
		// We assume it is satisfied if p(x,y,z) is not in the positive evidence nor is a query, and we're using the closed-world assumption.
		// HOWEVER, if in the list of 'hidden,' the CWA is not used (see isaFalseByCWA).
		return (matchesNegEvidence(lit) || isaFalseByCWA(lit));
	}
	// Is this literal a query or hidden?  But check first if its truth value is known.
	private boolean isSatisfiable(Literal lit) {
		if (matchesPosEvidence(lit) || matchesNegEvidence(lit)) { return false; }
		if (matchesQuery(lit)       || matchesHidden(lit))      { return true;  }
		return !task.isClosedWorldAssumption(lit); // If CWA=true, then this literal is false by it.  Otherwise this literal's truth value is unknown (and hence it is satisfiable).
	}
	// See if this literal's predicate name and arity are in this index.
	private boolean containsPnameAndArity(Literal lit, Map<PredicateName,Set<Integer>> predNameArityIndex) {
		if (predNameArityIndex == null || predNameArityIndex.size() < 1) { return false; }
		Set<Integer> lookup = predNameArityIndex.get(lit.predicateName);
		if (lookup == null) { return false; }
		return lookup.contains(lit.numberArgs());
	}

	// If this literal is procedurally defined AND its value matches 'desiredValue' then return TRUE else return FALSE.
	private boolean evaluateProcDefinedEvidence(Literal lit, boolean desiredValue) {
		PredicateName pName = lit.predicateName; // Save CPU cycles, assume literal never is null (it is a bug if it is).
		if (procedurallyDefinedPredicatesInUse != null && procedurallyDefinedPredicatesInUse.contains(pName)) {
			BindingList bindings = task.prover.evaluateProcedurallyDefined(lit);
			if (desiredValue) {	return (bindings != null); } // Did it succeed?
			return (bindings == null); // See if FALSE.
		}
		return false;
	}
	// See if this ground literal is in the index.
	private boolean containsThisLiteral(Literal lit, Map<PredicateName,Map<Term,List<List<Term>>>> indexedFacts) {
		if (indexedFacts == null || indexedFacts.size() < 1) { return false; }
		Collection<Term> skolemMarkers = task.skolemsPerLiteral.get(lit); // These match anything since we're not doing any logical inference and are simply matching.
		if (skolemMarkers == null) { skolemMarkers = skolemsInLiteralUnderConsideration; } // Used for cases where unifications produced new literal instances.
		List<Term>    args  = lit.getArguments();
		Term          c1    = (Utils.getSizeSafely(args) < 1 ? null : args.get(0)); 
		PredicateName pName = lit.predicateName; // Save CPU cycles, assume literal never is null (it is a bug if it is).
		Map<Term,List<List<Term>>> lookup1 = indexedFacts.get(pName);
		if (lookup1 == null) { return false; }
		int numbArgs = lit.numberArgs();
		if (numbArgs == 0) { return true; } // Just need to match the predicate name with 0-arity predicates.
		List<List<Term>> lookup2;
		// See if this predicate appears in a fact containing variables.  If so, need to unify this literal and the facts.
		if (factsWithVariables != null && factsWithVariables.contains(pName)) {
			lookup2 = lookup1.get(variableInFactMarker);
			for (List<Term> argsInIndexedFact : lookup2) if (argsInIndexedFact.size() == numbArgs) {
				bl.theta.clear();
				if (unifier.unifyAssumingSameNumberOfArgs(argsInIndexedFact, args, bl) != null) { return true; }
			}
		}
		if (skolemMarkers == null || !skolemMarkers.contains(c1)) { // See if 'c1' is NOT a Skolem marker.
			lookup2 = lookup1.get(c1); // Get the argument lists for this pName with this first argument.
			//if (skolemMarkers != null) { Utils.println("HERE1: " + skolemMarkers + "  " + lookup2); }
			if (lookup2 == null)  { return false; } // Nothing found, so failed.
			if (numbArgs == 1)    { return true;  } // Succeeded (only 1 argument).
			return seeIfArgumentsMatch(lookup2, args, skolemMarkers); // See if the rest of the arguments match.
		} else if (numbArgs == 1) { return true;   // Have matched the predicate name and the SkolemMarker (regardless of the first argument of literal), so done.
		} else { // Cannot use the first term to index (it matches ANYTHING).  So need to look at all KEYs (since they all match the Skolem).
			for (Term key : lookup1.keySet()) {
				lookup2 = lookup1.get(key);
				if (seeIfArgumentsMatch(lookup2, args, skolemMarkers)) { return true; }
			}
			return false;
		}
	}
	
	private boolean seeIfArgumentsMatch(List<List<Term>> storedArgLists, List<Term> litArgs, Collection<Term> skolemMarkers) {
		// In 0 or 1 Skolems, then easy to do 'variable' matching.
		if (Utils.getSizeSafely(skolemMarkers) < 2) { return  help_seeIfArgumentsMatch(storedArgLists, litArgs, (skolemMarkers == null ? null : Utils.getIthItemInCollectionUnsafe(skolemMarkers, 0))); }
		// Otherwise need to unify this literal and the facts.
		int numbOfArgs = litArgs.size();
		for (List<Term> argsInIndexedFact : storedArgLists) if (argsInIndexedFact.size() == numbOfArgs) {
			bl.theta.clear();
			if (debugLevel > 2 && skolemMarkers != null) { Utils.println("% UNIFY in seeIfArgumentsMatch: " + argsInIndexedFact + " and " + litArgs); }
			if (unifier.unifyAssumingSameNumberOfArgs(argsInIndexedFact, litArgs, bl) != null) { return true; }
		}
		return false;
	}
	// See if these arguments match something in the list of arguments.  Notice that the first argument has already been matched,
	// and that the skolemMarker can match anything.
	private boolean help_seeIfArgumentsMatch(List<List<Term>> storedArgLists, List<Term> args, Term skolemMarker) {
		if (debugLevel > 3) { Utils.println("help_seeIfArgumentsMatch: skolemMarker=" + skolemMarker + " and args=" + args + ": " + Utils.limitLengthOfPrintedList(storedArgLists, 25)); }
		int size = args.size(); 
		for (List<Term> indexList : storedArgLists) { // See if a match on the terms.
			boolean match = true;
			for (int i = 1; i < size; i++) { // Note we skip argument 0.
				Term litArg = args.get(i);
				if (litArg != indexList.get(i) && litArg != skolemMarker) {
					match = false; // Found a mismatch.
					break; // No need to look further in this argument list.
				}
			}
			if (match) { return true; } // Found a match, so done.
		}
		return false;
	}
	
	private void updateCountOfTotalGroundings(Clause clause, Literal lit, long satisfiers, long counted) {
		totalLiteralGroundingsConsideredThisLiteral.get(clause).put(lit, counted + totalLiteralGroundingsConsideredThisLiteral.get(clause).get(lit));
		totalLiteralGroundingsConsidered.put(clause,                     counted + totalLiteralGroundingsConsidered.get(clause));
		if (debugLevel > 2) { Utils.println("%      ********** Considered " + Utils.padLeft(counted, 9) + " groundings and found " 
											+ Utils.padLeft(satisfiers, 7) + " that satisfy the clause.  [Total for " + wrapLiteral(clause, lit) + " = " 
											+ Utils.comma(totalLiteralGroundingsConsideredThisLiteral.get(clause).get(lit)) + " and total for this clause = "
											+ Utils.comma(totalLiteralGroundingsConsidered.get(clause)) + ".]"); }
	}	
	
	// Use Terms here so can do later due lookups without needing to cast as Constants.  
	// Also, some facts might contain variables.  For those that do, use variableInFactMarker as the Term for indexing.
	// Put ALL arguments in the list, even though hashing on the first, since sometimes later code needs to match the first arguments (e.g., if it is a variable).
	private void hashSetOfFacts(Collection<GroundLiteral> facts, Map<PredicateName,Map<Term,List<List<Term>>>> hasher) {
		if (facts != null) for (Literal lit : facts) {
			PredicateName pName = lit.predicateName;
			List<Term>    args  = lit.getArguments();
			Term          term1 = (lit.numberArgs() < 1 ? null : args.get(0));
			Map<Term,List<List<Term>>> lookup1 = hasher.get(pName);
			
			// See if any facts containing variables are in use.
			if (lit.numberArgs() > 0) for (Term term : args) if (term == null) {
				if (factsWithVariables == null) { factsWithVariables = new HashSet<>(4); }
			 	factsWithVariables.add(lit.predicateName);
				term1 = variableInFactMarker; 
			}
			
			if (lookup1 == null) { 
				lookup1 = new HashMap<>(4);
				hasher.put(pName, lookup1);
			}
			List<List<Term>> lookup2 = lookup1.computeIfAbsent(term1, k -> new ArrayList<>(4));
			lookup2.add(args); // DO NOT REMOVE DUPLICATES, since we want to count groundings.
		}
	}
	
	// Allow fast lookups of PredNameArityPair's.
	private void hashPredNames(Collection<PredNameArityPair> predNames, Map<PredicateName,Set<Integer>> hash) {
		if (predNames != null) { // Convert the PredNameArityPair's to a quick lookup data structure.
			for (PredNameArityPair pNameArityPair : predNames) {
				Set<Integer> lookup = hash.computeIfAbsent(pNameArityPair.pName, k -> new HashSet<>(4));
				lookup.add(pNameArityPair.arity);
			}
		}
	}

	// This group of methods deals with post-reduction inference.
	void collectAllRemainingGroundings() {
		if (debugLevel > 0) { Utils.println("\n% Explicitly collecting all remaining groundings for reduced groundings that are small enough."); }
		int counter = 0;
		for (Clause clause : allClauses) {
			if (debugLevel > 1 || ++counter % 500 == 0) { Utils.println("%  Collecting all remaining groundings for clause #" + Utils.comma(counter) + "."); }
			if (countOfSatisfiableGndClauses.get(clause) > maxNumberClauseGroundings) {
				checkForUnacceptableLazyClause(clause);
				Utils.println("%    This clause has too many groundings (" + Utils.truncate(countOfSatisfiableGndClauses.get(clause), 0) + ") and will not be grounded: '" + clause + "'.");
				if (stillTooLargeAfterReduction == null) { stillTooLargeAfterReduction = new HashSet<>(4); }
				stillTooLargeAfterReduction.add(clause);
				continue;
			}
			try {
				getAllClauseGroundings(clause);
			} catch (MLNreductionProblemTooLargeException e) {
				checkForUnacceptableLazyClause(clause);
				Utils.println("% Clause #" + Utils.comma(clauseToIndex.get(clause)) + " is too large to fully ground, so it will require lazy evaluation.");
				if (stillTooLargeAfterReduction == null) { stillTooLargeAfterReduction = new HashSet<>(4); }
				stillTooLargeAfterReduction.add(clause);
			}
		}
		collectAllGroundClauses();
		collectAllGroundLiterals();
		if (Utils.getSizeSafely(stillTooLargeAfterReduction) > 0) {
			Utils.writeMe("Lazy inference not implemented here");

		}
		if (Utils.getSizeSafely(allGroundClauses) > 0) {
			computeAllBlocks(); // Need all the ground literals before this can be done.
		}
	}
	
	private void checkForUnacceptableLazyClause(Clause clause) {
		if (!task.isClosedWorldAssumption(null)) {
			Utils.error("The closed-world assumption is not being used, and without it large clauses cannot be handled:\n   " + clause + "\n" + 
						"Reset your use of FROG and try again.");
		}
		if (Utils.getSizeSafely(clause.negLiterals) < 1) {
			Utils.error("This clause has no negated literals and too many groundings (" + Utils.comma(countOfSatisfiableGndClauses.get(clause)) + "), all of which need to be explicitly represented \n" +
						"because the default value of clauses (true) cannot be used.  Please remove or edit this clause, or change default settings in FROG, and try again:\n    " +
						clause);
		}
		if (!isSatisfiableViaDefaults(clause)) {
			Utils.error("This clause has no negated literals where the closed-world assumption appplies and too many groundings (" + Utils.comma(countOfSatisfiableGndClauses.get(clause)) + "), all of which need to be explicitly represented \n" +
						"because the default value of clauses (true) cannot be used.  Please remove or edit this clause, or change default settings in FROG, and try again:\n    " +
						clause);
		}		
	}
	
	private boolean isSatisfiableViaDefaults(Clause clause) {
		if (clause.negLiterals != null) for (Literal nLit : clause.negLiterals) {
			if (task.isClosedWorldAssumption(nLit)) { return true; }
		}
		return false;
	}

	private Set<GroundClause> collectRemainingClauseGroundings(Clause clause) throws MLNreductionProblemTooLargeException {
		return collectRemainingClauseGroundings(clause, variablesInClause.get(clause));
	}

	private Set<GroundClause> collectRemainingClauseGroundings(Clause clause, Collection<Variable> freeVariables) throws MLNreductionProblemTooLargeException {
		long start = System.currentTimeMillis();
		int countGroundingsDiscarded = 0;
		if (debugLevel > 0) { Utils.println("\n% Collect remaining groundings, using free variables " + freeVariables + "" + ", for clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + "'."); }
		Set<GroundClause>    results       = null;	
		if (Utils.getSizeSafely(freeVariables) < 1) {
			if (debugLevel > 0) { Utils.println("%   No variables in '" + clause + "' so it is its own ground clause."); }
			// Recall that ground clauses can represent SETS of groundings, and need to account for that when calculating weights.
			bl.theta.clear();
			GroundClause groundClause = getGroundClause(task, clause, getFreeVarMap(variablesRemainingInClause.get(clause)));
			results = new HashSet<>(4);
			results.add(groundClause);
			return results; // Added (11/2/09) by JWS.
		}
		Collection<Literal>        keeperLiterals         = literalsToKeep.get(clause);
		if (Utils.getSizeSafely(keeperLiterals) < 1) { return null; }
		double                     size                   = 1.0;
		Set<Variable>              unAggregatedVars       = null;  // Used to watch for errors.
		Set<Variable>                aggregatedVars       = null;  // Used to watch for errors.
		List<AggVar>               aggregatorsNeeded      = null;
		List<Set<Term>>        allArgPossibilities    = new ArrayList<>(1);
		List<List<List<Term>>> allAggArgPossibilities = null;
		int                        numbFreeVariables      = Utils.getSizeSafely(freeVariables);
		Map<Variable,Integer>      mapVariablesToPositionInAggregatorList = null; // If there are aggregators, we need to know their position in aggregatorsNeeded.
		for (Variable var : freeVariables) {
			VariableIndexPair currentOwnerOfVar = aggregatorMap.get(clause).get(var);
			if (currentOwnerOfVar == null) {
				if (debugLevel > 0) { Utils.println("% VAR '" + var + "' has these constants " + Utils.limitLengthOfPrintedList(varsToConstantsMap.get(clause).get(var), 25)); }
				if (unAggregatedVars == null) { unAggregatedVars  = new HashSet<>(4); }
				if (unAggregatedVars.contains(var)) { Utils.error("Already have '" + var + "' in unAggregatedVars=" + unAggregatedVars); } // Should never happen, but check anyway.
				unAggregatedVars.add(var);
				size *= Utils.getSizeSafely(varsToConstantsMap.get(clause).get(var));
				allArgPossibilities.add(varsToConstantsMap.get(clause).get(var));
			} else { // This else might be called multiple times with the same aggVar, so keep track.
				if (aggregatedVars == null) { aggregatedVars  = new HashSet<>(4); }
				if (aggregatedVars.contains(var)) { Utils.error("Already have '" + var + "' in aggregatedVars=" + aggregatedVars); } // Should never happen, but check anyway.
				aggregatedVars.add(var);
				AggVar aggVar = aggregatorMap.get(clause).get(var).aggVar;
				if (aggregatorsNeeded == null || !aggregatorsNeeded.contains(aggVar)) {
					if (debugLevel > 0) { Utils.println("% VAR '" + var + "' is aggregated by '"      + aggVar + "', which has these " + Utils.comma(aggVarsToAggregatedConstantsMap.get(clause).get(aggVar))+ " constants " + Utils.limitLengthOfPrintedList(aggVarsToAggregatedConstantsMap.get(clause).get(aggVar), 10)); }
					if (aggregatorsNeeded == null) { aggregatorsNeeded = new ArrayList<>(1); }
					aggregatorsNeeded.add(aggVar);
					if (allAggArgPossibilities == null) { allAggArgPossibilities = new ArrayList<>(1); }
					allAggArgPossibilities.add( aggVarsToAggregatedConstantsMap.get(clause).get(aggVar));				
					size *= Utils.getSizeSafely(aggVarsToAggregatedConstantsMap.get(clause).get(aggVar));
					if (mapVariablesToPositionInAggregatorList == null) { mapVariablesToPositionInAggregatorList = new HashMap<>(4); }
					if (mapVariablesToPositionInAggregatorList.containsKey(var)) { Utils.error("Already have '" + var + "' in " + mapVariablesToPositionInAggregatorList); }
					mapVariablesToPositionInAggregatorList.put(var, aggregatorsNeeded.size() - 1);
				} else {
					if (debugLevel > 0) { Utils.println("% VAR '" + var + "' is also aggregated by '" + aggVar + "'."); }
					int numbExistingAggVars = aggregatorsNeeded.size();
					if (numbExistingAggVars == 1) { mapVariablesToPositionInAggregatorList.put(var, 0); }
					else { 
						for (int i = 0; i < numbExistingAggVars; i++) { 
							if (aggVar == aggregatorsNeeded.get(i)) { mapVariablesToPositionInAggregatorList.put(var, i); break; }
						}
					}
				}
				allArgPossibilities.add(dummySingletonSetOfConstants); // Need to keep the arity the same.
			}
		}
		if (debugLevel > 0) { Utils.println("% TOTAL SIZE: " + Utils.truncate(size, 0) + " for " + freeVariables); }

		if (size > maxNumberClauseGroundings) { throw new MLNreductionProblemTooLargeException(""); }
		if (debugLevel > 3) {
			Utils.println("allArgPossibilities    = " + Utils.limitLengthOfPrintedList(allArgPossibilities,    25));
			Utils.println("allAggArgPossibilities = " + Utils.limitLengthOfPrintedList(allAggArgPossibilities, 25));
		}
		// I cannot figure out how to get rid of the type checking errors ...
		CrossProductViaContinuation<Term>               basicVarCrossProduct = new CrossProductViaContinuation(allArgPossibilities);
		CrossProductViaContinuation<List<Term>> crossProductOfAggregatedVars = new CrossProductViaContinuation(allAggArgPossibilities);
		while (!basicVarCrossProduct.isEmpty()) {
			List<Term> bindings  = basicVarCrossProduct.getNextCrossProduct(); // Expand this binding using all the items in aggregatorListOfLists.
			boolean        firstTime = true; // If crossProductOfAggregatedVars is empty, we still need to do through the WHILE once.
			crossProductOfAggregatedVars.reset(); // Need to start this 'inner loop' afresh each time the outer loop is called.
			while (firstTime || !crossProductOfAggregatedVars.isEmpty()) { // Collect all the combinations for the aggregated variables.
				List<List<Term>> argVarLists = crossProductOfAggregatedVars.getNextCrossProduct();
				List<Term>       newBindings = new ArrayList<>(Utils.getSizeSafely(bindings)); // Get a fresh COPY. Do not REUSE, since getNextCrossProduct reuses the same memory cells.
				
				if (bindings != null) { newBindings.addAll(bindings); }
				if (debugLevel > 3) { Utils.println("  newBindings: " + newBindings + " for freeVariables = " + freeVariables); }
				if (firstTime) { firstTime = false; }
				// Now walk through each aggregator and correctly fill in the positions in newBindings.
				if (argVarLists != null) for (int argNumber = 0; argNumber < numbFreeVariables; argNumber++) { // Walk through the variables in this literal and see which need to get their values from an aggregator.
					Variable basicVar                      = Utils.getIthItemInCollectionUnsafe(freeVariables, argNumber);
					assert mapVariablesToPositionInAggregatorList != null;
					Integer  aggVarPositionForThisBasicVar = mapVariablesToPositionInAggregatorList.get(basicVar);	// Indexes into argVarList.
					
					if (aggVarPositionForThisBasicVar != null) { // See if this variable is owned by some aggregator.
						VariableIndexPair pair                 = aggregatorMap.get(clause).get(basicVar);
						List<Term>    argVarListForThisVar = argVarLists.get(aggVarPositionForThisBasicVar);
						if (debugLevel > 3) { Utils.println(" freeVariables = " + freeVariables + "  basicVar = " + basicVar + "  argVarListForThisVar = " + argVarListForThisVar + "  pair = " + pair); }
						if (pair.index < Utils.getSizeSafely(argVarListForThisVar)) {
							newBindings.set(argNumber, argVarListForThisVar.get(pair.index));
						} else { Utils.warning(" pair.index = " + pair.index + " argVarListForThisVar.size() = " + Utils.getSizeSafely(argVarListForThisVar)); }
					}
				}
				bl.theta.clear();
				if (debugLevel > 3) { Utils.println("  newBindings: " + newBindings + " for freeVariables = " + freeVariables); }
				int counter = 0;
				for (Variable var : freeVariables) { // NOTE: should be safe to assume the order through the freeVariables is correct even though freeVariables is a Collection.
					bl.addBinding(var, newBindings.get(counter++));
				}
				// Now need to create a grounded clause USING ONLY THOSE LITERALS STILL REMAINING.
				List<Literal> posLitsRemaining         = null;
				List<Literal> negLitsRemaining         = null;
				boolean       thisGroundingIsSatisfied = false;
				for (Literal lit : keeperLiterals) {
					boolean containsSkolem = false;
					Literal gLit; // If contains a Skolem, need to expand now (assuming it is satisfiable).
					if (task.skolemsPerLiteral.get(lit) != null) {
						containsSkolem = true;
						gLit = lit.applyTheta(bl.theta); // Since a Skolem, need to handle separately, but still want any bindings.  JWSJWSJWS
						skolemsInLiteralUnderConsideration = task.skolemsPerLiteral.get(lit); // Using a 'global' instead of passing another argument everywhere.
						if (debugLevel > 3) { Utils.println(lit + " -> " + skolemsInLiteralUnderConsideration); } 
					} else {
						gLit = task.getCanonicalRepresentative(lit.applyTheta(bl.theta), postponeSavingGroundLiterals);
					}
					if (clause.getSign(lit)) {
						if (thisPosLiteralIsSatisfied(gLit)) {
							Utils.println("    POS gLit=" + gLit + " is already satisfied!  Bug??");
							thisGroundingIsSatisfied = true;
							break;
						} else if (isSatisfiable(gLit)) {
							if (posLitsRemaining == null) { posLitsRemaining = new ArrayList<>(1); }
							if (containsSkolem) {
								Collection<GroundLiteral> expandedSkolems = expandSkolems(gLit, task.skolemsPerLiteral.get(lit));
								assert expandedSkolems != null;
								posLitsRemaining.addAll(expandedSkolems);
							} else {
								if (postponeSavingGroundLiterals) { task.storeGroundLiteralBeingHeld(); } 
								posLitsRemaining.add(gLit);
							}
						} else if (debugLevel > 0) { // Simply discard since since it cannot be satisfied.
							Utils.println("%   Discard an unsatisfiable ground literal: '" + gLit + "'.");
						}
					} else {
						if (thisNegLiteralIsSatisfied(gLit)) {
							Utils.println("    NEG gLit=" + gLit + " is already satisfied!  Bug??");
							thisGroundingIsSatisfied = true;
							break;
						} else if (isSatisfiable(gLit)) {
							if (negLitsRemaining == null) { negLitsRemaining = new ArrayList<>(); }
							if (containsSkolem) {
								Utils.error("There should not be Skolems in NEGATIVE literals.");
							} else {
								if (postponeSavingGroundLiterals) { task.storeGroundLiteralBeingHeld(); } 
								negLitsRemaining.add(gLit);
							}
						} else if (debugLevel > 0) { // Simply discard since since it cannot be satisfied.
							Utils.println("%   Discard an unsatisfiable ground literal: '~" + gLit + "'.");
						}
					}
				}
				skolemsInLiteralUnderConsideration = null; // Need to erase this 'global' when done (clean up this fragile code?).
				if (thisGroundingIsSatisfied) {
					if (debugLevel > 0) { Utils.println("%  Incrementing TRUE count.  No need to save the ground clause that results from bindings " + bl + " since it is known to be satisfied."); }
					countGroundingsDiscarded++;
					double multiplier = multiplierPerSatisfiedClause.get(clause);
					countOfSatisfiableGndClauses.put(clause, countOfSatisfiableGndClauses.get(clause) - 1);
					countOfTRUEs.put(clause, countOfTRUEs.get(clause) + multiplier);
				} else if (posLitsRemaining == null && negLitsRemaining == null) {
					if (debugLevel > 0) { Utils.println("%  Incrementing FALSE count.  No need to save the ground clause that results from bindings " + bl + " since no literals are satisfiable."); }
					countGroundingsDiscarded++;
					countOfSatisfiableGndClauses.put(clause, countOfSatisfiableGndClauses.get(clause) - 1);
					double multiplier = multiplierPerSatisfiedClause.get(clause);
					countOfFALSEs.put(clause, countOfFALSEs.get(clause) + multiplier);
				} else {
					// Recall that ground clauses can represent SETS of groundings, and need to account for that when calculating weights.
					GroundClause gndClause = getGroundClause(clause, posLitsRemaining, negLitsRemaining);
					if (results == null) { results = new HashSet<>(4); } // We don't want to remove duplicates here.
					results.add(gndClause);
					if (debugLevel > 3) { Utils.println("  bindings: " + bl + " produced ground clause #" + Utils.comma(results) + " '" + gndClause + "'."); }
					// This should have been checked above, but leave here nevertheless.
					if (results.size() > maxNumberClauseGroundings) { throw new MLNreductionProblemTooLargeException(""); }
				}
			}
		}
		if (debugLevel > 0) {
			long   end       = System.currentTimeMillis();
			double timeTaken = (end - start) / 1000.0;
			Utils.println("%   Took " + Utils.truncate(timeTaken, 3) + " seconds to perform the grounding of clause #" + Utils.comma(clauseToIndex.get(clause)) + ".  Produced " + Utils.comma(results) + " ground clauses and could ignore " + Utils.comma(countGroundingsDiscarded) + " ground clauses.");
		}		
		return results;
	}
	
	// Each ground clause needs to record the variable bindings that created it (so duplicates can be detected).
	// If ALL groundings are created at once, there is no need for this extra info. but it is needed for lazy evaluation.
	private List<Term> getFreeVarMap(Set<Variable> set) {
		return null;
	}

	// Expand all the Skolems in this literal.  Do this by looking up all possible constants for each Skolem, doing a cross product if necessary.
	private Collection<GroundLiteral> expandSkolems(Literal lit, Collection<Term> skolemsToExpand) throws MLNreductionProblemTooLargeException {
		Collection<GroundLiteral> results = new HashSet<>(4);
		List<TypeSpec> typeSpecs = task.collectLiteralArgumentTypes(lit);
		int counter = 0;
		double size = 1.0;
		List<Set<Term>> allArgPossibilities = new ArrayList<>(skolemsToExpand.size());
		for (Term term : lit.getArguments()) {
			if (skolemsToExpand.contains(term)) {
				TypeSpec typeSpec = typeSpecs.get(counter);
				Set<Term> existingConstants = task.getReducedConstantsOfThisType(typeSpec.isaType);
				if (existingConstants == null) { return null; }
				allArgPossibilities.add(existingConstants);
				size *= Utils.getSizeSafely(existingConstants);
			} else { // Also need to fold in the non-Skolems.
				Set<Term> termInSet = new HashSet<>(4);
				termInSet.add(term);
				allArgPossibilities.add(termInSet);
			}
			counter++;
		}

		if (debugLevel > 2) { Utils.println("% Have " + Utils.truncate(size, 0) + " expansions of '" + lit + "' due to its Skolems " + skolemsToExpand + "."); }
		// Throw an exception if one literal is expanded more times than this due to Skolems.
		double maxSkolemExpansionPerLiteral = 1e6;
		if (size > maxSkolemExpansionPerLiteral) {
			throw new MLNreductionProblemTooLargeException(".");
		}

		List<List<Term>> crossProduct = Utils.computeCrossProduct(allArgPossibilities, Integer.MAX_VALUE);
		assert crossProduct != null;
		for (List<Term> argList : crossProduct) {
			Literal newLit = task.stringHandler.getLiteral(lit.predicateName);
			List<Term> arguments2 = new ArrayList<>(lit.numberArgs());
			arguments2.addAll(argList);
			newLit.setArguments(arguments2);
			results.add(task.getCanonicalRepresentative(newLit));
		}
		if (debugLevel > 2
				) { Utils.println("%   Expansion: " + Utils.limitLengthOfPrintedList(results, 15)); }
		return results;
	}

	boolean haveCollectedAllGroundLiterals = false;
	boolean haveCollectedAllGroundClauses  = false;

	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public void clearAllMarkers() {
		setAllMarkers(null);
	}

	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public void setAllMarkers(Object marker) {
		setAllClauseMarkers( marker);
		setAllLiteralMarkers(marker);
		markerInUse = marker;
	}

	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public void setAllClauseMarkers(Object marker) {
		if (!haveCollectedAllGroundClauses) {
			Utils.error("Cannot set all the  markers until all the gound clauses have been collected.");
		}
		GroundClause gndClause = getFirstGroundClause();
		while (gndClause != null) {
			gndClause.setMarker(marker);
			gndClause = getNextGroundClause();
		}
		markerInUse = marker;
	}

	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public void setAllLiteralMarkers(Object marker) {
		if (!haveCollectedAllGroundLiterals) {
			Utils.error("Cannot set all the markers until all the gound literals have been collected.");
		}
		GroundLiteral gLit = getFirstGroundLiteral();
		while (gLit != null) {
			gLit.setMarker(marker);
			gLit = getNextGroundLiteral();
		}
		markerInUse = marker;
	}

	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public void clearMarkedClauses() {
		GroundClause gndClause = getFirstMarkedGroundClause();
		while (gndClause != null) { 
			gndClause.setMarker(null);
			gndClause = getNextMarkedGroundClause();
		}
	}
	
	private void collectAllGroundLiterals() {
		if (debugLevel > 1) { Utils.println("%     Collecting all ground literals."); }
		if (allGroundLiteralsOrig != null) { Utils.error("Need to have allGroundLiteralsOrig=null when this is called."); }
		if (allGroundLiterals     != null) { Utils.error("Need to have allGroundLiterals=null when this is called."); }
		if (Utils.getSizeSafely(allGroundClausesOrig) < 1) {
			return;
		}
		Set<GroundLiteral> allGroundLiteralsAsSet = new HashSet<>(4); // Initially use a set, so duplicates will be removed.
		for (GroundClause gndClause : allGroundClausesOrig) {
			if (gndClause.getLength() > 0) for (int i = 0; i < gndClause.getLength(); i++) {
				allGroundLiteralsAsSet.add(gndClause.getIthLiteral(i)); // Duplicates will be removed because this is a set.
			}			
		}
		// Now we need to have the ground literals point back to the ground clauses that contain them.
		allGroundLiteralsOrig = new ArrayList<>(allGroundLiteralsAsSet);
		for (GroundLiteral gLit : allGroundLiteralsOrig) {
			gLit.clearGndClauseSet(); }
		for (GroundClause gndClause : allGroundClausesOrig) {
			if (gndClause.getLength() > 0)
				for (int i = 0; i < gndClause.getLength(); i++) {
					gndClause.getIthLiteral(i).addGndClause(gndClause);
				}
		}
		if (debugLevel > 1) { Utils.println("%       Collected " + Utils.comma(allGroundLiteralsOrig) + " ground literals."); }
		if (debugLevel > 2 && allGroundLiteralsOrig != null) {
			double total = 0.0;
			for (GroundLiteral gLit : allGroundLiteralsOrig) { total += Utils.getSizeSafely(gLit.getGndClauseSet()); }
			Utils.println("%       On average, each ground literal is in " + Utils.truncate(total / allGroundLiteralsOrig.size(), 1) + " ground clauses.");
		}
		help_collectAllGroundLiterals(); 
	}

	private void help_collectAllGroundLiterals() {
		allGroundLiterals         = allGroundLiteralsOrig;
		// Remember these, as a ways of checking of the Orig versions are improperly altered.
		collectQueryGroundLiteralsNotInReducedNetwork();
		numberOfNonLazyGroundLiterals = Utils.getSizeSafely(allGroundLiterals);
		resetNextGroundLiteral();
		haveCollectedAllGroundLiterals = true;		
	}

	private Set<GroundLiteral> groundQueryLiteralNotInReducedNetwork     = null;

	private void collectQueryGroundLiteralsNotInReducedNetwork() {
		groundQueryLiteralNotInReducedNetwork = new HashSet<>(4); // Make anew, so groundQueryLiteralNotInReducedNetworkOrig not touched.
		Set<GroundLiteral> qLits = task.getQueryLiterals();
		if (qLits == null) { Utils.error("Should have some query literals?"); }
		Set<GroundLiteral> tempGndLits = new HashSet<>(2 * allGroundLiterals.size());
		tempGndLits.addAll(allGroundLiterals); // Use space to create this to save time with lookups.
		assert qLits != null;
		for (GroundLiteral gLit : qLits) if (!tempGndLits.contains(gLit)) {
			groundQueryLiteralNotInReducedNetwork.add(gLit);
		}
		Utils.println("% Of the " + Utils.comma(allGroundLiterals) + " ground literals, " + Utils.comma(groundQueryLiteralNotInReducedNetwork) + " are not in the reduced network.");
	}

	private void getAllClauseGroundings(Clause clause) throws MLNreductionProblemTooLargeException {
		if (allGroundClausesPerClause == null) { allGroundClausesPerClause = new HashMap<>(4); }
		Set<GroundClause> results = allGroundClausesPerClause.get(clause);
		if (Utils.getSizeSafely(results) == countOfSatisfiableGndClauses.get(clause)) { return; }
		if (results != null) { Utils.writeMe("Already have some groundings here ..."); } // If we simply overwrite these, might mess up other data structures.
		results = collectRemainingClauseGroundings(clause);
		if (countOfSatisfiableGndClauses.get(clause) != Utils.getSizeSafely(results)) {
			Utils.error("countOfSatisfiableGndClauses.get(clause) = " + Utils.truncate(countOfSatisfiableGndClauses.get(clause), 0) +
						" but generated " + Utils.comma(results) + " groundings.");
		}
		allGroundClausesPerClause.put(clause, results);
		removePointersToConstants(clause); // No longer need these lists once all groundings have been created, so release to Java's garbage collector.
	}

	private void collectAllGroundClauses() {
		Utils.println("%     Collecting all ground clauses.");
		if (allGroundClausesOrig != null) { Utils.error("Need to have allGroundClausesOrig=null when this is called."); }
		if (allGroundClauses     != null) { Utils.error("Need to have allGroundClauses=null when this is called.");     }
		// TVK: allGroundClausesPerClause should already be set here.
		if (allGroundClausesPerClause == null) { Utils.error("Need to have allGroundClausesPerClause!=null when this is called.");     }

		if (countofUniqueGroundClauses < 1) {
			Utils.println("%       There are no remaining satisfiable clause groundings, so no ground clauses to collect.");
			haveCollectedAllGroundClauses = true;
			resetNextGroundClause();
			return; 
		}
		allGroundClausesOrig      = new ArrayList<>();
		for (Integer code : hashOfGroundClauses.keySet()) {
			allGroundClausesOrig.addAll(hashOfGroundClauses.get(code));
		}
		Utils.println("%       Collected " + Utils.comma(allGroundClausesOrig) + " ground clauses.");
		allGroundClauses             = allGroundClausesOrig;
		numberOfNonLazyGroundClauses = Utils.getSizeSafely(allGroundClauses);
		resetNextGroundClause();
		haveCollectedAllGroundClauses = true;
	}

	private List<GroundClause> allGroundUnitClausesFromNegWgtClauses = new ArrayList<>(0);

	private List<GroundClause> allPermanentLazyGroundClauses = new ArrayList<>(0); // These are the lazy ground clauses that 'touch' (intersect with the regular ground literals).

	private List<GroundClause> allLazyGroundClauses = new ArrayList<>(0);

	private int counterIntoGroundClauses            = 0;
	private int numberOfNonLazyGroundClauses        = 0; // Does NOT include the UnitClause ones.
	private int numberOfUnitClauseFromNegWgtClauses = 0; // Instead, they are in this list.
	private int numberOfPermanentLazyGroundClauses  = 0;
	private int numberOfLazyGroundClauses           = 0;
	private int totalNumberOfGroundClauses          = 0;
	private List<GroundClause> allGroundClauses_ExpensiveVersion = new ArrayList<>(0);

	private int getNumberOfGroundClauses() {
		if (debugLevel > 2) { 
			Utils.println("% numberOfNonLazyGroundClauses = "        + Utils.comma(numberOfNonLazyGroundClauses)        + 
						  "  numberOfUnitClauseFromNegWgtClauses = " + Utils.comma(numberOfUnitClauseFromNegWgtClauses) + 
						  "  numberOfPermanentLazyGroundClauses  = " + Utils.comma(numberOfPermanentLazyGroundClauses)  + 
						  "  numberOfLazyGroundClauses = "           + Utils.comma(numberOfLazyGroundClauses)); 
		}
		if (!haveCollectedAllGroundClauses) { Utils.error("haveCollectedAllGroundClauses = false"); }
		return totalNumberOfGroundClauses;
	}

	private  void resetNextGroundClause() {
		allGroundClauses_ExpensiveVersion.clear(); 
		counterIntoGroundClauses   = 0;
		totalNumberOfGroundClauses = numberOfNonLazyGroundClauses + numberOfUnitClauseFromNegWgtClauses + numberOfPermanentLazyGroundClauses + numberOfLazyGroundClauses; 
	}

	GroundClause getNextGroundClause() {
		int currentCount = counterIntoGroundClauses++;
		if (currentCount >= getNumberOfGroundClauses()) {
			counterIntoGroundClauses = 0; // Next time start at front of list.
			return null; // Note at end of list.
		}
		if (currentCount >= 0 && currentCount < numberOfNonLazyGroundClauses) {
			return allGroundClauses.get(currentCount); 
		}
		currentCount -= numberOfNonLazyGroundClauses;
		if (currentCount >= 0 && currentCount < numberOfUnitClauseFromNegWgtClauses) {
			return allGroundUnitClausesFromNegWgtClauses.get(currentCount); 
		}
		currentCount -= numberOfUnitClauseFromNegWgtClauses;
		if (currentCount >= 0 && currentCount < numberOfPermanentLazyGroundClauses) {
			return allPermanentLazyGroundClauses.get(currentCount); 
		}
		currentCount -= numberOfPermanentLazyGroundClauses;
		if (currentCount >= 0 && currentCount < numberOfLazyGroundClauses) {
			return allLazyGroundClauses.get(currentCount); 
		}
		errorWithGroundClauses();
		return null;
	}

	private void errorWithGroundClauses() {
		Utils.println("\n% " + "Error in getNextGroundClause.");
		Utils.error(" Should not reach here: counterIntoGroundClauses = " + Utils.comma(counterIntoGroundClauses)      +
					" numberOfNonLazyGroundClauses = "             + Utils.comma(numberOfNonLazyGroundClauses)        +
					" numberOfUnitClauseFromNegWgtClauses = "      + Utils.comma(numberOfUnitClauseFromNegWgtClauses) +
					" numberOfPermanentLazyGroundClauses = "       + Utils.comma(numberOfPermanentLazyGroundClauses)  +
					" numberOfLazyGroundClauses = "                + Utils.comma(numberOfLazyGroundClauses)           +
					" totalNumberOfGroundClauses = "               + Utils.comma(totalNumberOfGroundClauses));
	}

	GroundClause getNextMarkedGroundClause() {
		GroundClause result = getNextGroundClause();
		while (result != null && !isaMarkedGroundClause(result)) { result = getNextGroundClause(); }
		return result;
	}

	GroundClause getFirstGroundClause()  {
		if (!haveCollectedAllGroundClauses) { Utils.error("Calling getAllGroundClauses(), but haveCollectedAllGroundClauses=false!"); }
		counterIntoGroundClauses = 0;
		return getNextGroundClause();
	}
	GroundClause getFirstMarkedGroundClause()  {
		counterIntoGroundClauses = 0;
		return getNextMarkedGroundClause();
	}

	// Same stuff, but for literals.

	private List<GroundLiteral> allLazyGroundLiterals = new ArrayList<>(0);
	private int counterIntoGroundLiterals     = 0;
	private int numberOfNonLazyGroundLiterals = 0; 
	private int numberOfLazyGroundLiterals    = 0;
	private int totalNumberOfGroundLiterals   = 0;
	private List<GroundLiteral> allGroundLiterals_ExpensiveVersion = new ArrayList<>(0);

	private  void resetNextGroundLiteral() {
		allGroundLiterals_ExpensiveVersion.clear(); 
		counterIntoGroundLiterals = 0;
		totalNumberOfGroundLiterals = numberOfNonLazyGroundLiterals + numberOfLazyGroundLiterals; 
	}

	List<GroundLiteral> getAllGroundLiterals_ExpensiveVersion() { // This version wastes space, but makes for easier calling code.
		if (!haveCollectedAllGroundLiterals) { Utils.error("Calling getAllGroundLiterals(), but haveCollectedAllGroundLiterals=false!"); }
		if (numberOfLazyGroundLiterals == 0) {
			return allGroundLiterals;
		}
		if (allGroundLiterals_ExpensiveVersion.size() == totalNumberOfGroundLiterals) {
			return allGroundLiterals_ExpensiveVersion; // A bit risky if same size, but different objects (i.e., should always call resetNextGroundLiteral when making changes).
		}
		allGroundLiterals_ExpensiveVersion.clear();
		allGroundLiterals_ExpensiveVersion.addAll(allGroundLiterals);
		allGroundLiterals_ExpensiveVersion.addAll(allLazyGroundLiterals);
		return allGroundLiterals_ExpensiveVersion;
	}

	GroundLiteral getNextGroundLiteral() {
		int currentCount = counterIntoGroundLiterals++;
		if (currentCount >= totalNumberOfGroundLiterals)  {
			counterIntoGroundLiterals = 0; // Next time start at front of list.
			return null; // Note at end of list.
		}
		if (currentCount < numberOfNonLazyGroundLiterals) { 
			return allGroundLiterals.get(currentCount); 
		}
		currentCount -= numberOfNonLazyGroundLiterals;
		if (currentCount < numberOfLazyGroundLiterals)    {
			return allLazyGroundLiterals.get(currentCount); 
		}
		Utils.error("Should not reach here: counterIntoGroundLiterals = " + Utils.comma(counterIntoGroundLiterals)     +
					" numberOfNonLazyGroundLiterals = "                   + Utils.comma(numberOfNonLazyGroundLiterals) +
					" numberOfLazyGroundLiterals = "                      + Utils.comma(numberOfLazyGroundLiterals)    +
					" totalNumberOfGroundLiterals = "                     + Utils.comma(totalNumberOfGroundLiterals));
		return null;
	}

	GroundLiteral getFirstGroundLiteral()  {
		counterIntoGroundLiterals = 0;
		return getNextGroundLiteral();
	}

	///////////////////////////////////////////////////////////////////////////////////////////////////////////


	// This is called when looking at the ground clauses pointed to be ground literals.
	// To make sure there is no unintentional 'cross talk,' make sure this clause is marked
	// as being 'current,' which is done by the marker property on the ground clause.
	boolean isaMarkedGroundClause(GroundClause gndClause) {
		return (gndClause.getMarker() == markerInUse);
	}
	boolean isaMarkedGroundLiteral(GroundLiteral gLit) {
		return (gLit.getMarker()      == markerInUse);
	}


	// End of group that deals with methods for post-reduction inference.
	
	///////////////////////////////////////////////////////////////////////////////////////////////
	
	// This next group deals with "blocks" of variables.

	private Map<GroundLiteral,Block>                    allBlocks = null;
	private Map<PredicateName,Map<Integer,List<Block>>> predNameArityToBlockList;
	
	private void computeAllBlocks() {
		initPredNameArityToBlock();
		populateBlocks();
		if (debugLevel > 2) { Utils.println("% GroundThisMarkovNetwork: #blocks = " + Utils.getSizeSafely(getAllBlocks())); }
	}
	
	private Map<GroundLiteral,Block> getAllBlocks() {
		return allBlocks;
	}
	
	/**
	 * Creates a Map where the keys are all the literals which have block constraints.
	 * At the end of this method, the map's values are an empty list of blocks.
	 */
	private void initPredNameArityToBlock() {
		Map<PredicateName,Set<Integer>> predNameArityPairsSeen = new HashMap<>(4);
		predNameArityToBlockList = new HashMap<>(4);
		if (debugLevel > 0) { Utils.println("\n% Initialize the predicate-name blocks."); }
		for (GroundLiteral gLit : allGroundLiterals) if (gLit.numberArgs() > 0) {			
			PredicateName predName = gLit.predicateName;
			int           arity    = gLit.numberArgs();
			Set<Integer> lookup = predNameArityPairsSeen.computeIfAbsent(predName, k -> new HashSet<>(4));
			if (lookup.contains(arity)) { continue; }
			lookup.add(arity);
			List<TypeSpec> listOfTypeSpecs = task.collectLiteralArgumentTypes(predName, arity);
			for (TypeSpec typeSpec : listOfTypeSpecs) {
				if (typeSpec.truthCounts != 0) { // If this is non zero, then have a blocked literal.
					if (debugLevel > 0) { Utils.println("% Have truth counts = " + typeSpec.truthCounts + " in " + typeSpec); }
					addPredNameAndArityToBlockList(predName, arity, new ArrayList<>(1), predNameArityToBlockList);
					break;
				}
			}
		}
	}
	
	// Add this block list to predNameArityToBlockList for pName/arity.  If something already stored for this pair, do nothing.
	private void addPredNameAndArityToBlockList(PredicateName pName, int arity, List<Block> blockList, Map<PredicateName,Map<Integer,List<Block>>> map) {
		Map<Integer,List<Block>> lookup1 = predNameArityToBlockList.get(pName);
		if (lookup1 == null) {
			lookup1 = new HashMap<>(4);
			map.put(pName, lookup1);
		}
		lookup1.putIfAbsent(arity, blockList);
	}
	
	private List<Block> getBlockListFromPredNameAndArity(Literal lit, Map<PredicateName,Map<Integer,List<Block>>> map) {
		return getBlockListFromPredNameAndArity(lit.predicateName, lit.numberArgs(), map);
	}
	private List<Block> getBlockListFromPredNameAndArity(PredicateName pName, int arity, Map<PredicateName,Map<Integer,List<Block>>> map) {
		Map<Integer,List<Block>> lookup1 = map.get(pName);
		if (lookup1 == null) { return null; } // OK to not be present.
		return lookup1.get(arity);
	}
	
	private void populateBlocks() {
		allBlocks = null;
		for (GroundLiteral gLit : allGroundLiterals) {
			List<Block> blockList = getBlockListFromPredNameAndArity(gLit, predNameArityToBlockList);
			if (blockList == null) continue;
			boolean addedToBlock = false;
			for (Block block : blockList) {
				if (block.addGndLiteral(gLit)) {
					gLit.setBlock(block);
					addedToBlock = true;
					break;
				}
			}
			if (!addedToBlock) {
				List<GroundLiteral> temp = new ArrayList<>();
				temp.add(gLit);
				Block block = new Block(gLit, temp);
				gLit.setBlock(block);
				blockList.add(block);
				if (allBlocks == null) { allBlocks = new HashMap<>(4); }
				allBlocks.put(gLit, block);
			}
		}		
		if (allBlocks != null && !task.isClosedWorldAssumption(null)) { setEvidenceInBlocks(task.getPosEvidenceLiterals(), predNameArityToBlockList); }
	}
	
	private void setEvidenceInBlocks(Collection<GroundLiteral> evidence, Map<PredicateName, Map<Integer, List<Block>>> map) {
		if (evidence == null) { return; }
		for (GroundLiteral gLit : evidence) {
			List<Block> blockList = getBlockListFromPredNameAndArity(gLit, map);
			if (blockList == null) continue;
			for (Block block : blockList) {
				if (block.canAddGndLiteral()) {
					block.addEvidence();
					break;
				}
			}
		}
	}
	
	// End of group that deals with methods for processing blocks.
	

	
	// Is this ground literal in this set of constants for this literal in this clause?
	// More specifically, would this ground literal be generated by these cross products?
	// Input positionsOfArgumentsInLiteralToUse is needed when more literals are needed (due to aggregators) than those variables in a literal.
	// Input mapVariablesToPositionInAggregatorList maps variables in the literal to items in crossProductOfAggregatedVars.
	// Input basicVarCrossProduct will have as many items as there are free variables in this literal, but the aggregated ones will have a generic filler.
	// Input crossProductOfAggregatedVars will contain an item for each aggregator in this literal.
	// Input aggVarIndexes maps each constant to the List<Constants> in which it appears as the first item (for faster lookup).
	private boolean gLitArgumentsStillExistInVariableCrossProducts(Clause clause, Literal lit, int[] positionsOfArgumentsInLiteralToUse, Map<Term, Integer> mapVariablesToPositionInAggregatorList, GroundLiteral gLit,
																   CrossProductViaContinuation<Term> basicVarCrossProduct, List<AggVar> aggregatorsNeeded, CrossProductViaContinuation<List<Term>> crossProductOfAggregatedVars) {
		if (literalsContainingConstants.get(clause) != null && literalsContainingConstants.get(clause).contains(lit)) { // If there are constants in here, then need to first see if lit and gLit unify.  If only variables, no need to do the unification.
			bl.theta.clear(); // Save new'ing a binding list.
			if (unifier.unify(lit, gLit, bl) == null) { return false; }
			// These MAY or MAY NOT have been excess, but not worth spending cycles just to see if the assignments to variables is an existing cross product.
			// So assume NOT (i.e., assume that this check here is 'free.'
		}
		Collection<Integer> map = firstVariableAppearance.get(clause).get(lit);  // See original comment for what this encodes.
		// Should never reach here with map=null, so don't waste cycles testing.  Instead, let Java catch bugs.
		List<Term>  litArgs =  lit.getArguments();
		List<Term> gLitArgs = gLit.getArguments();
		Map<Integer,                 List<Term>>   constantsForAggVars      = null;
		Map<Integer,                 List<Integer>>    locationsInAggVars       = null;
		Map<Integer,Map<Term,Set<List<Term>>>> constantsForAggVarsINDEX = null;
		
		int varCounter = 0;

		for (Integer item : map) { // Look at each argument in the ground literal. 
			if (item > 0) { // Only need to check these entries.  These are the first occurrences of variables.
				Term gLitArg = gLitArgs.get(item - 1);  // Remember the map counts from 1, not 0.
				Term      litArg =             litArgs.get(item - 1);
				Integer aggVarPositionForThisBasicVar = (mapVariablesToPositionInAggregatorList == null ? null : mapVariablesToPositionInAggregatorList.get(litArg));	// Indexes into argVarList.				
				
				if (aggVarPositionForThisBasicVar != null) { // See if this variable is owned by some aggregator.
					if (debugLevel > 3) { Utils.println("% *** Checking if aggregated constant '" + gLitArg + "' still exists (for position " + varCounter + ")."); }
					// If so, need to collect ALL gLitArgs that are in this same aggregator, so we can check for the existence of the tuple all together.
					if (constantsForAggVars      == null)                          { constantsForAggVars = new HashMap<>(4); }
					if (locationsInAggVars       == null)                          { locationsInAggVars = new HashMap<>(4); }
					List<Term> lookup1 = constantsForAggVars.get(aggVarPositionForThisBasicVar);
					List<Integer>  lookup2 = locationsInAggVars.get( aggVarPositionForThisBasicVar);
					if (lookup1 == null) { // First time for this aggregated variable.
						lookup1 = new ArrayList<>(2); // Must be at least two since an aggregated variable, though could find exact size in crossProductOfAggregatedVars (but minor savings).
						constantsForAggVars.put(aggVarPositionForThisBasicVar, lookup1);
						lookup2 = new ArrayList<>(2);
						locationsInAggVars.put(aggVarPositionForThisBasicVar, lookup2);
					}
					lookup1.add(gLitArg);
					// Now need to find the position for this argument in the aggregator (eg, we might need 2 of the 3 aggregated variables, and we need to know which 2).
					AggVar aggVar = aggregatorsNeeded.get(aggVarPositionForThisBasicVar);
					lookup2.add(aggVar.getPosition((Variable) litArg));
					if (debugLevel > 3) { Utils.println("%  need to find " + gLitArg + " in " + aggVar + " at position " + aggVar.getPosition((Variable) litArg)); }
				} else { // This variable has not been aggregated yet.  So simply see if it is in the list for the corresponding cross product (which are ordered by the variables location in the literal, so the varCounter represents this).
					if (debugLevel > 3) { Utils.println("% *** Checking if unaggregated constant '" + gLitArg + "' still exists (for position " + varCounter + ")."); }
					int index = varCounter;
					if (positionsOfArgumentsInLiteralToUse.length > 0) { // Pull out the variables for this literal from the possibly longer fullSetOfVariables, using the provided 'map.'
						index = positionsOfArgumentsInLiteralToUse[varCounter];
					}
					if (!basicVarCrossProduct.containsThisEntry(index, gLitArg)) { currentExcessChecks++; return false; }  // If not, we're done.
					else if (debugLevel > 3) { Utils.println("% ***     found it!"); }
				}					
				varCounter++;
			}
		}

		// Now process any constantsForAggVars (needed to wait to collect everything).  Recall that these are LISTS of constants, and we need to see if this combination is still under consideration.
		if (debugLevel > 3) { Utils.println("mapVariablesToPositionInAggregatorList=" + mapVariablesToPositionInAggregatorList + " constantsForAggVars=" + constantsForAggVars + "  constantsForAggVarsINDEX=" + constantsForAggVarsINDEX); }
		if (constantsForAggVars != null) {
			for (Integer item : constantsForAggVars.keySet()) {
				List<Term> args   = constantsForAggVars.get(item);
				List<Integer>  argMap = locationsInAggVars.get( item);
				if (debugLevel > 3) { Utils.println("% *** Looking for aggregated constant(s) " + args + " in positions " + argMap + " of aggregator #" + item + " for gLit '" + gLit + "', a  grounding of " + wrapLiteral(clause, lit) + " whose map = " + map + " and where mapVariablesToPositionInAggregatorList=" + mapVariablesToPositionInAggregatorList); }
				if (argsContainedInThisAggregation(crossProductOfAggregatedVars.getThisEntry(item))) {
					if (debugLevel > 3) { Utils.println("% ***     found it!"); }}
				else { if (debugLevel > 3) { Utils.println("% ***     FAILED"); } currentExcessChecks++; return false; }
			}
		}
		if (debugLevel > 3) { Utils.println("% *** found " + gLit + " still exists as a grounding of " + lit); }
		return true;
	}
	
	// NEED TO FIND *SOME* ARGS IN A POSSIBLY LONGER LIST!  Eg, [x,z] in [ ... [ x, y, z], ...].
	private boolean argsContainedInThisAggregation(Collection<List<Term>> aggregation) {
		if (aggregation == null)        { return false; }
		if (debugLevel > 3) { Utils.println("% ***     " + Utils.limitLengthOfPrintedList(aggregation, 25)); }
		for (List<Term> ignored : aggregation) {
			return true;
		}
		return false;
	}

	// Pull out (in order) the constants in this ground literal that replaced the variables in this literal.
	// Note: this is NOT the same as the gLit's arguments!  
	// For example, if lit=p(1,X,Y,X) and gLit=p(1,2,3,2) then should return {2,3}.
	// See comments about firstVariableAppearance's "semantics."
	private List<Term> extractConstants(Clause clause, Literal lit, GroundLiteral gLit) {
		Collection<Integer> map = firstVariableAppearance.get(clause).get(lit);
		if (map == null) { return null; }
		List<Term>   result = new ArrayList<>(map.size());
		List<Term>     gLitArgs = gLit.getArguments();
		for (Integer item : map) { if (item > 0) result.add(gLitArgs.get(item - 1)); } // Note that firstVariableAppearance's counting starts at 1 (since 0 means "isa constant in the original literal."
		return result;
	}

	
	// %%%%%%%%%%%%%%%%%%%   Start of Managing the Grounded Network, Lazy Evaluation, etc.   %%%%%%%%%%%%%%%%%%%%%

	@Deprecated
	public boolean prepareForInference(TimeStamp timeStamp) { // Return TRUE if LAZY inference needed.
		Utils.println("\n% Create all the query literals.");
		task.createAllQueryLiterals();  // Need all of these to be expanded
		Utils.println("\n% There are " + Utils.comma(task.getQueryLiterals()) + " query literals.");
		collectAllRemainingGroundings();
		if (Utils.getSizeSafely(stillTooLargeAfterReduction) < 1) { Utils.println("\n% Because there are only " + Utils.truncate(totalNumberOfGroundingsRemaining, 0) + " clause groundings remaining, will perform standard inference."); }
		else { Utils.println("\n% Due to the large number of groundings they have remaining, " + Utils.comma(stillTooLargeAfterReduction) + " clauses need to be handled lazily."); }
		return (Utils.getSizeSafely(stillTooLargeAfterReduction) < 1);
	}
	long countofUniqueGroundClauses = 0;
	long countOfMergedGroundClauses = 0;
	private GroundClause getGroundClause(MLN_Task task, Clause clause, List<Term> freeVarBindings) {
		GroundClause newGndClause = new GroundClause(task, clause, multiplierPerSatisfiedClause.get(clause), freeVarBindings);
		addToGroundClauseIndex(newGndClause);
		return newGndClause; // For now, let's just see how many can be reduced.
	}
	private GroundClause getGroundClause(Clause clause, List<Literal> posLits, List<Literal> negLits) {
		GroundClause newGndClause = new GroundClause(clause, posLits, negLits, multiplierPerSatisfiedClause.get(clause), null);
		addToGroundClauseIndex(newGndClause);
		return newGndClause; // For now, let's just see how many can be reduced.
	}
	

	private LiteralComparator litComparator = new LiteralComparator();

	// Return true if this is a NEW ground clause.
	private void addToGroundClauseIndex(GroundClause gndClause) {
		// Put in a canonical form.
		if (gndClause.getLength() < 1) {
			Utils.warning("Have a ground clause with no literals: "    + gndClause.groundClauseSettingToString(this) + ".  It will be ignored.");
			return;
		}
		if (gndClause.getWeightOnSentence() == 0.0) {
			Utils.warning("Have a ground clause with weight of zero: " + gndClause.groundClauseSettingToString(this) + ".  It will be ignored.");
			return;
		}
		// If a singleton clause with a negative weight, convert to the equivalent version (negate the weight and the literal.
		// TVK 8/28 : Flipping before learning weights would add q(x) instead of !q(x) to allGroundClausesPerClause
		// if the initial weights are negative. Only flip the weights if they are learnt.
		// Initially set to false. Set to true, when the weights learnt for the MLN.
		if (gndClause.negLiterals != null) { gndClause.negLiterals.sort(litComparator); }
		if (gndClause.posLiterals != null) { gndClause.posLiterals.sort(litComparator); }
		int hashcode = getNonFastHashCode(gndClause);
		hashOfGroundClauses.get(hashcode);
		List<GroundClause> hits;
		hits = new ArrayList<>(1);
		countofUniqueGroundClauses++;
		hits.add(gndClause);
		hashOfGroundClauses.put(hashcode, hits);
	}
	private int getNonFastHashCode(GroundClause gndClause) {
		boolean holdLiteral = task.stringHandler.useFastHashCodeForLiterals;
		boolean holdClause  = task.stringHandler.useFastHashCodeForClauses;
		task.stringHandler.useFastHashCodeForLiterals = false; // Need this setting in order to get proper matching of equivalent literals.
		task.stringHandler.useFastHashCodeForClauses  = false; // Ditto for clauses.
		int hashcode = gndClause.hashCode();
		task.stringHandler.useFastHashCodeForLiterals = holdLiteral;
		task.stringHandler.useFastHashCodeForClauses  = holdClause;
		return hashcode;
	}

	@Deprecated
	public long getCountOfUniqueGroundClauses() {
		int counter  = 0;
		int counter2 = 0;
		int max      = 0;
		Integer indexOfMax = 0;
		for (Integer index : hashOfGroundClauses.keySet()) {
			int size = hashOfGroundClauses.get(index).size();
			counter += size;
			if (size > max) { max = size; indexOfMax = index; }
			if (size > 1)   { counter2++; }
		}
		Utils.println("\n% There are " + Utils.comma(countofUniqueGroundClauses) + " unique ground clauses; " + Utils.comma(countOfMergedGroundClauses) + " have had their weights merged.");
		Utils.println("%  |canonical ground-clause hash codes| = " + Utils.comma(hashOfGroundClauses.keySet().size()) + 
					   ", |hash of ground clauses| = "             + Utils.comma(counter)  +
					   ", |with collisions| = "                    + Utils.comma(counter2) +
					   ", max # of collisions = "                  + Utils.comma(max));
		Utils.println("%    max collisions: " + Utils.limitLengthOfPrintedList(hashOfGroundClauses.get(indexOfMax), 25));
		return countofUniqueGroundClauses;
	}

	@Deprecated
	public void printLiteralsAndClauses() {
		List<GroundLiteral> gndLiterals = getAllGroundLiterals_ExpensiveVersion();
		for(GroundLiteral gndL : gndLiterals) {
			Utils.println("Literal: " + gndL.toPrettyString());
			Set<GroundClause> gndClauses = gndL.getGndClauseSet();
			for(GroundClause gndC : gndClauses) {
				Utils.println("Clause: " + gndC.toPrettyString());
			}
		}
	}

	// %%%%%%%%%%%%%%%%%%%   End of Processing grounded network, lazy evaluation, etc.   %%%%%%%%%%%%%%%%%%%%%
	
}

// A special variable that aggregates normal variables.
class AggVar {
	private List<Variable> varsCombined; // Order matters, so use a list.  Might want to use a LinkedListSet here, but these lists should be short, so walking through then should be faster than that dealing with hashing.
	
	protected AggVar(List<Variable> varsCombined) {
		this.varsCombined = varsCombined;
	}

	int getPosition(Variable var) {
		int index = varsCombined.indexOf(var);
		if (index < 0) { Utils.error("Cannot find '" + var + "' in " + this); }
		return index;
	}
	
	public String toString() {
		StringBuilder result = new StringBuilder(); // "agg";
		for (Variable var : varsCombined) { result.append("_").append(var); }
		return result.substring(1); // Drop the leading "_".
	}
}

// A data structure used to map a normal variable into a position in an aggregated variable.
class VariableIndexPair {
	AggVar aggVar;
	protected int    index; // The 'var' indexes into a Set of List<Term> and this says which position in these lists is being referenced.
	
	protected VariableIndexPair(AggVar aggVar, int index) {
		this.aggVar = aggVar;
		this.index  = index;
	}
	
	public String toString() {
		return aggVar + "@" + index;
	}
	
}

// Hold information produced during a grounding of a literal.
class CacheLiteralGrounding {
	private   List<List<Term>> groundingsStillNeeded;  // These are the groundings still needed for this literal.
	long trueCount; // Indicate these have no been set.
	long falseCount; // NOTE: these counts are for literals IGNORING THEIR sign.
	long unknownCount;

	CacheLiteralGrounding(List<List<Term>> groundingsStillNeeded, long trueCount, long falseCount, long unknownCount) {
		this.groundingsStillNeeded = groundingsStillNeeded;
		this.trueCount             = trueCount;
		this.falseCount            = falseCount;
		this.unknownCount          = unknownCount;
	}

	void describeCache(String msg) {
		Utils.println("%   Cache Report: " + msg);
		Utils.println("%          #true: " + Utils.comma(trueCount));
		Utils.println("%         #false: " + Utils.comma(falseCount));
		Utils.println("%           #unk: " + Utils.comma(unknownCount));
		Utils.println("%     groundings: " + Utils.limitLengthOfPrintedList(groundingsStillNeeded, 25));	
	}

	List<List<Term>> getGroundingsStillNeeded() {
		if (groundingsStillNeeded != null) { return groundingsStillNeeded; }
		return null;
	}
}

