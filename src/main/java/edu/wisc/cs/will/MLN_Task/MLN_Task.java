/**
 * 
 */
package edu.wisc.cs.will.MLN_Task;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.Utils.Utils;

/**
 *   Richardson, M. and Domingos, P.,
 *   Markov logic networks,
 *   Machine Learning, 62, pp. 107-136, 2006.
 *   http://alchemy.cs.washington.edu/papers/richardson06/
 *   
 *   Note: literals in clauses will be processed faster if any constant arguments are the FIRST argument (of course might not always be possible).
 *         Could index on ALL positions (or the first K), but might not be worth the increase in space.
 * 
 * @author shavlik
 *
 */
public class MLN_Task {	
	private static final int debugLevel = 2; //Integer.MIN_VALUE;

	protected final static int maxWarnings  = 100;
	protected              int warningCount =   0;  // Count how many warnings provided to user; stop when some maximum number reached. 
	
	public  double             maxNumberOfQueryLiterals  = 1e8;

	private boolean            checkForNewConstants = true; // Turn off when done to save time, plus once starting grounding a network, new constants would mess up things.

	public  HandleFOPCstrings  stringHandler;
	public  Unifier            unifier;
	public  HornClauseProver   prover;
	public  int                maxConstantsOfGivenType =    1000000; // When more than this many constants of a given type, discard randomly until this many.
	public  int                maxGroundingsOfLiteral  = 1000000000; // When finding the groundings of a LITERAL, limit to this many.  This is also the max size of JOINED argument lists.
	public  int                maxGroundingsOfClause   = 1000000000; // When finding the groundings of a CLAUSE,  limit to this many.
	
	protected String             workingDirectory;
	protected Collection<Clause> allClauses; // Not many of these, so no need to hash.
	private   Set<GroundLiteral> queryLiterals;   // Make these sets since we don't want any duplicates.
	private   Set<GroundLiteral> hiddenLiterals;  // Do NOT apply the closed-world assumption to these.
	private   Set<GroundLiteral> posEvidenceLiterals; // No need to allow this to be given as PredName as well, since presumably we do not want to say ALL are positive (or negative).
	private   Set<GroundLiteral> negEvidenceLiterals;
	private   boolean            closedWorldAssumption = true; // Assume a literal is false if its truth value is not known.
	
	// All literals that meet one of these spec's is a literal of the associated type.  
	// More compact that creating all such literals, but might be expanded later in any case (also, one might not want ALL groundings to be in the given class, and in that case explicit lits of grounded literals should be used).
	// Also, can add something like 'p(x,y)' to a literal collection, which is the same (???) as putting 'p/2' in a Collection<PredNameArityPair>.
	private Set<PredNameArityPair> queryPredNames; // TODO - if these are used with GroundThisMarkovNetwork, then need to ground before inference?
	private Set<PredNameArityPair> hiddenPredNames; // These need to be SETs (at least in the creators) so that duplicates are not added.
	private Set<PredNameArityPair> posEvidencePredNames; // Probably rarely used, since can then remove from clauses, but allow them anyway.
	private Set<PredNameArityPair> negEvidencePredNames; // Ditto.
	
	private Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> knownQueriesThisPnameArity;
	private Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> knownHiddensThisPnameArity;
	private Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> knownPosEvidenceThisPnameArity;
	private Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> knownNegEvidenceThisPnameArity;
	private boolean knownQueriesThisPnameArityHasVariables     = false;
	private boolean knownHiddensThisPnameArityHasVariables     = false;
	private boolean knownPosEvidenceThisPnameArityHasVariables = false;
	private boolean knownNegEvidenceThisPnameArityHasVariables = false;
	
	// Can override the default value for closed-world assumption.
	private Map<PredicateName,Set<Integer>>  neverCWAonThisPredNameArity;
	private Map<PredicateName,Set<Integer>> alwaysCWAonThisPredNameArity;

	private   Variable                        skolemMarker1    = null; // Skolem arguments are replaced with this marker, so it can be used to match any fact (no logical inference is done, so this works, but be careful of 'unit propagation' or the like is used).
	private   Variable                        skolemMarker2    = null; // A given literal can have more than one skolem variable,
	private   Variable                        skolemMarker3    = null; // so allow up to five in a clause (if more throw error, suggesting code be extended).
	private   Variable                        skolemMarker4    = null;
	private   Variable                        skolemMarker5    = null;
	protected Set<Variable>                   setOfSkolemMarkers; // Duplicate for fast lookup.
	protected Map<Literal,Set<Term>>          skolemsPerLiteral;  // Be sure to not COPY literals or this will be screwed up!
	
	private Map<Type,Set<Term>> hashOfTypeToConstants;        // Record all the constants of a given type.  Use Term here so can become argument lists without copying.
	private Map<Type,Set<Term>> hashOfTypeToReducedConstants; // A subset of the above, used for reducing the size of the ground Markov network via sampling.

	// TODO is the following still used?
	private Map<PredicateName,Map<Integer,Set<Clause>>> predNameToClauseList; // A hash table which gives all the clauses a literal (specified by predicateName/arity) appears in.

	private Map<Integer,List<GroundLiteral>> hashOfGroundLiterals;

	private   Map<Type,Set<Constant>> constantTypePairsHandled = new HashMap<>(4); // Used to prevent unnecessary calls to the stringHandler.  TODO - move this to the string handler, as a space-time tradeoff.
	
	private   TimeStamp timeStamp;

	// The next variant is called by the others to set up various things.
	public MLN_Task(HandleFOPCstrings stringHandler, Unifier unifier, HornClauseProver prover) {
		this.stringHandler           = stringHandler;
		this.unifier                 = unifier;
		this.prover                  = prover;
		stringHandler.setUseStrictEqualsForLiterals(false); // The MLN code does a lot of indexing on literals, and sometimes on clauses, and we don't want spurious matches (even though due to variables being separately named per literal, this probably isn't necessary).
		stringHandler.setUseStrictEqualsForClauses( true);
		hashOfTypeToConstants          = new HashMap<>(4);
		hashOfTypeToReducedConstants   = new HashMap<>(4);
		hashOfGroundLiterals           = new HashMap<>(4);
		knownQueriesThisPnameArity     = new HashMap<>(4);
		knownHiddensThisPnameArity     = new HashMap<>(4);
		knownPosEvidenceThisPnameArity = new HashMap<>(4);
		knownNegEvidenceThisPnameArity = new HashMap<>(4);
	}

	private Set<Type>    warningNoConstantsThisType;
	Set<Term> getReducedConstantsOfThisType(Type type) {
		if (!hashOfTypeToConstants.containsKey(type)) {
			Set<Term> allConstantsOfThisType = stringHandler.isaHandler.getAllInstances(type);
			if (allConstantsOfThisType == null) { 
				if (warningNoConstantsThisType == null || !warningNoConstantsThisType.contains(type)) { 
						if (warningNoConstantsThisType == null) { warningNoConstantsThisType = new HashSet<Type>(4); }
						warningNoConstantsThisType.add(type);
						Utils.warning("Have no constants of type '" + type + "'."); 
				}
				return null;
			}
			hashOfTypeToConstants.put(type, allConstantsOfThisType);
			if (allConstantsOfThisType.size() > maxConstantsOfGivenType) {
				Set<Term> reducedSet = new HashSet<Term>(4);
				reducedSet.addAll(allConstantsOfThisType); // A bit inefficient to copy (especially if lots discarded), but this way we get exactly the desired number.
				hashOfTypeToReducedConstants.put(type, Utils.reduceToThisSizeByRandomlyDiscardingItemsInPlace(reducedSet, maxConstantsOfGivenType));
			} else { hashOfTypeToReducedConstants.put(type, allConstantsOfThisType); }
			Utils.println("% Have " + Utils.padLeft(allConstantsOfThisType.size(), 7) + " constants of type = '" + type  + "'"
							+ (allConstantsOfThisType.size() > maxConstantsOfGivenType ? ", reduced to " + Utils.comma(hashOfTypeToReducedConstants.get(type).size()) : "")
							+ ".");
		}
		return hashOfTypeToReducedConstants.get(type);
	}

	private boolean calledCreateAllQueryLiterals = false;
	protected void createAllQueryLiterals() {
		if (calledCreateAllQueryLiterals) { return; }
		calledCreateAllQueryLiterals = true;
		if (queryPredNames == null) { return; }
		if (queryLiterals  != null) { Utils.error("Already have some query literals: " + Utils.limitLengthOfPrintedList(queryLiterals, 25)); }
		queryLiterals = new HashSet<GroundLiteral>(4);
		if (debugLevel > -10) { Utils.println("%  queryPredNames = " + Utils.limitLengthOfPrintedList(queryPredNames, 25)); }
		for (PredNameArityPair predNameArityPair : queryPredNames) {
			Set<GroundLiteral> groundings = groundThisLiteral(predNameArityPair);
			if (true) { Utils.println("% Have " + Utils.comma(groundings) + " groundings for query " + predNameArityPair+ "."); }
			if (groundings != null) { queryLiterals.addAll(groundings); }
			else { Utils.error("Have no groundings for query: " + predNameArityPair); }
		}
		int numbQueries = Utils.getSizeSafely(queryLiterals);
		if (debugLevel  > 0)   { Utils.println("% Number of query literals generated from queryPredNames: " + Utils.comma(numbQueries)); }
		if (numbQueries > maxNumberOfQueryLiterals) { Utils.error("Too many query literals.  Note that the current code requires they all be explicitly grounded, even with lazy inference, since statistics need to be collected for each."); }
	}

	/**
	 * Get all groundings of the literal whose predicate name and arity are passed as an argument.
	 * Postcondition: Be wary that at the end of this method, gndClauseList in the resulting ground literals in not initialized.
	 *
	 * @return Return all the groundings of predName/arity.
	 */
	private Set<GroundLiteral> groundThisLiteral(PredNameArityPair predNameArity) {
		if (predNameArity == null) { Utils.error("Should not have predNameArity=null."); }
		Set<GroundLiteral> results = new HashSet<>(4);
		assert predNameArity != null;
		if (predNameArity.arity < 1) { // Handle case of a literal with NO arguments.
			Literal lit = stringHandler.getLiteral(predNameArity.pName);
			GroundLiteral gndLiteral = getCanonicalRepresentative(lit);
			results.add(gndLiteral);
			return results;
		}			
			
		// Collect all the types in the literal.
		Collection<TypeSpec> typeSpecs = collectLiteralArgumentTypes(predNameArity.pName, predNameArity.arity);
		Utils.println("% In groundThisLiteral(" + predNameArity + ") with typeSpecs = " + typeSpecs);
		List<Set<Term>> allArgPossibilities = new ArrayList<Set<Term>>(typeSpecs.size());
		for (TypeSpec typeSpec : typeSpecs) { // Need to convert from lists of constants to lists of terms at some point.  Might as well do it here (seems work the same regardless).
			Set<Term> constants = getReducedConstantsOfThisType(typeSpec.isaType);
			if (constants != null) {
				Set<Term> convertConstantsToTerms = new HashSet<Term>(4);
				convertConstantsToTerms.addAll(constants);
				allArgPossibilities.add(convertConstantsToTerms);
			} else {
				return null; // There are no groundings.
			}
		}
		int size = 1;
		if (debugLevel > 3) { Utils.println(" allArgPossibilities = " + allArgPossibilities); }
		for (Set<Term> possibilities : allArgPossibilities) { size *= Utils.getSizeSafely(possibilities); }
		Utils.print("%   Will produce " + Utils.comma(size) + " groundings.  [1"); // TODO - filter if too many?
		for (Set<Term> possibilities : allArgPossibilities) { Utils.print(" x " + possibilities.size()); }
		Utils.println("]");
		List<List<Term>> crossProduct = Utils.computeCrossProduct(allArgPossibilities, maxGroundingsOfLiteral);
		int counter = 0;
		for (List<Term> argList : crossProduct) {
			if (++counter % 100000 == 0) { Utils.println("%       counter = " + Utils.comma(counter)); }
			Literal              lit = stringHandler.getLiteral(predNameArity.pName, argList);
			GroundLiteral gndLiteral = getCanonicalRepresentative(lit);
			results.add(gndLiteral);
		}
		if (debugLevel > 2) { Utils.println("%  Returning " + Utils.comma(Utils.getSizeSafely(results)) + " results\n"); }
		return results;
	}

	private GroundLiteral newGlit_hold;
	private Integer       hashcode_hold;
	void storeGroundLiteralBeingHeld() {
		if (hashcode_hold != null) {
			List<GroundLiteral> lookup = hashOfGroundLiterals.computeIfAbsent(hashcode_hold, k -> new ArrayList<>(1));
			lookup.add(newGlit_hold);
			if (checkForNewConstants) { collectTypedConstants(newGlit_hold.predicateName, newGlit_hold.getArguments()); }  // Check for new constants when first stored.
			if (debugLevel > 2) { Utils.println("%     new ground literal: " + newGlit_hold); }
		}
	}
	GroundLiteral getCanonicalRepresentative(Literal lit) {
		return getCanonicalRepresentative(lit, true, false);
	}
	GroundLiteral getCanonicalRepresentative(Literal lit, boolean storeIfNotThere, boolean postponeAddition) {
		boolean hold = stringHandler.useFastHashCodeForLiterals;
		stringHandler.useFastHashCodeForLiterals = false; // Need this setting in order to get proper matching of equivalent literals.
		int hash = lit.hashCode(); 
		stringHandler.useFastHashCodeForLiterals = hold;
		List<GroundLiteral> lookup = hashOfGroundLiterals.get(hash);
		if (lookup == null) {
			if (!storeIfNotThere) { return null; } // Return an indicator that this literal is not in the hash table.
		} else { 
			for (GroundLiteral gLit : lookup) if (gLit.matchesThisGroundLiteral(lit)) { // Check the literals that hashed here.
				newGlit_hold  = null;
				hashcode_hold = null;
				return gLit; // Have found the canonical representative.  No need to store anything later.
			}
			if (!storeIfNotThere) { return null; } // Return an indicator that this literal is not in the hash table.
		}
		// This literal is new.  Convert to a GroundLiteral (if not already), add to hash table, and return it.
		GroundLiteral newGlit = (lit instanceof GroundLiteral ? (GroundLiteral) lit : new GroundLiteral(lit));
		newGlit_hold  = newGlit; /// If postponeAddition = true, then we'll add these later (e.g., after calling code decides if these should be stored).
		hashcode_hold = hash;
		if (!postponeAddition) { storeGroundLiteralBeingHeld();	}
		return newGlit;
	}

	// Return a list of types for the arguments in this literal.
	List<TypeSpec> collectLiteralArgumentTypes(Literal literal) {
		return collectLiteralArgumentTypes(literal.predicateName, literal.numberArgs());
	}
	List<TypeSpec> collectLiteralArgumentTypes(PredicateName pName, int arity) {
		if (arity < 1) { return null; }
		List<PredicateSpec> typeList = pName.getTypeOnlyList(arity);
		// Currently ASSUME each literal has only one typeList.  TODO - relax assumption 
		if (Utils.getSizeSafely(typeList) < 1) { Utils.error("Could not find the argument types for: '" + pName + "/" + arity + "'."); }
		if (typeList.size() > 1) {
			if (warningCount < maxWarnings) { Utils.println("% MLN WARNING #" + Utils.comma(++warningCount) + ":  There is more than one mode for: '"  + pName + "/" + arity + "'. " + typeList + "  Will only use first one."); }
		}
		return typeList.get(0).getTypeSpecList();
	}

	private boolean isaPositiveEvidenceLiteral(GroundLiteral lit) {
		if (debugLevel > 2) { Utils.print("*** Is '" + lit + "' in positive evidence " + Utils.limitLengthOfPrintedList(posEvidenceLiterals, 25)); }
		boolean foundInPos = false;
		if (posEvidenceLiterals  != null) { foundInPos = posEvidenceLiterals.contains(lit); }
		if (posEvidencePredNames != null) { Utils.error("Need to look here as well - TODO."); }
		if (debugLevel > 2) { Utils.println((foundInPos ? " YES" : " NO")); }
		return foundInPos;
	}
	
	private boolean isaNegativeEvidenceLiteral(GroundLiteral lit) {
		if (debugLevel > 2) { Utils.print("*** Is '" + lit + "' in negative evidence " + Utils.limitLengthOfPrintedList(negEvidenceLiterals, 25)); }
		boolean foundInNeg = false;
		if (negEvidenceLiterals  != null) { foundInNeg = negEvidenceLiterals.contains(lit); }
		if (negEvidencePredNames != null) { Utils.error("Need to look here as well - TODO."); }
		if (debugLevel > 2) { Utils.println((foundInNeg ? " YES" : " NO")); }
		return foundInNeg;
	}
	
	boolean isaEvidenceLiteral(GroundLiteral lit) {
		return (isaNegativeEvidenceLiteral(lit) || isaPositiveEvidenceLiteral(lit));
	}

	public boolean isaKnownLiteral(Literal gLit) {
		PredicateName pName = gLit.predicateName;
		int           arity = gLit.numberArgs();
		return isaKnownLiteral(pName, arity);
	}
	public boolean isaKnownLiteral(PredicateName pName, int arity) {
		return (Utils.getSizeSafely(getKnownsCollection(pName, arity, null, knownPosEvidenceThisPnameArity)) > 0 ||
				Utils.getSizeSafely(getKnownsCollection(pName, arity, null, knownQueriesThisPnameArity))     > 0 ||
				Utils.getSizeSafely(getKnownsCollection(pName, arity, null, knownHiddensThisPnameArity))     > 0 ||
				Utils.getSizeSafely(getKnownsCollection(pName, arity, null, knownNegEvidenceThisPnameArity)) > 0);
	}

	Collection<GroundLiteral> getQueryKnowns(Literal lit) {
		return getKnownsCollection(lit, knownQueriesThisPnameArityHasVariables,     knownQueriesThisPnameArity);
	}
	Collection<GroundLiteral> getHiddenKnowns(Literal lit) {
		return getKnownsCollection(lit, knownHiddensThisPnameArityHasVariables,     knownHiddensThisPnameArity);
	}
	Collection<GroundLiteral> getPosEvidenceKnowns(Literal lit) {
		return getKnownsCollection(lit, knownPosEvidenceThisPnameArityHasVariables, knownPosEvidenceThisPnameArity);
	}
	Collection<GroundLiteral> getNegEvidenceKnowns(Literal lit) {
		return getKnownsCollection(lit, knownNegEvidenceThisPnameArityHasVariables, knownNegEvidenceThisPnameArity);
	}
	private Collection<GroundLiteral> getKnownsCollection(Literal lit, boolean hasVariables, Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> map) {
		PredicateName pName = lit.predicateName;
		int           arity = lit.numberArgs();
		Term       firstArg = (hasVariables || arity < 1 ? null : lit.getArgument(0)); // If there are variables in this Map, then don't use constants index since if we did we would need to merge two lists (TODO - rethink this space-time tradeoff).
		return getKnownsCollection(pName, arity, firstArg, map);
	}
	private Collection<GroundLiteral> getKnownsCollection(PredicateName pName, int arity, Term firstArg, Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> map) {
		Map<Integer,Map<Term,Collection<GroundLiteral>>> lookup1 = map.get(pName);
		if (lookup1 == null) { return null; }
		Map<Term,Collection<GroundLiteral>> lookup2 = lookup1.get(arity);
		if (lookup2 == null) { return null; }
		if (firstArg != null && firstArg instanceof Constant) { return lookup2.get(firstArg); }
		return lookup2.get(null);
	}
	
	Set<GroundLiteral> getQueryLiterals() {
		return queryLiterals;
	}

	Collection<GroundLiteral> getHiddenLiterals() {
		return hiddenLiterals;
	}

	Collection<GroundLiteral> getPosEvidenceLiterals() {
		return posEvidenceLiterals;
	}

	Collection<GroundLiteral> getNegEvidenceLiterals() {
		return negEvidenceLiterals;
	}

	Collection<PredNameArityPair> getQueryPredNames()       { return queryPredNames;       }
	Collection<PredNameArityPair> getPosEvidencePredNames() { return posEvidencePredNames; }
	Collection<PredNameArityPair> getNegEvidencePredNames() { return negEvidencePredNames; }
	Collection<PredNameArityPair> getHiddenPredNames()      { return hiddenPredNames;      }


	private void collectTypedConstants(PredicateName pName, List<Term> args) {
		// These might already have been collected, but play it safe.
		if (debugLevel > 2) { Utils.println("%     collectTypedConstants: " + pName + "/" + args); }
		if (!checkForNewConstants) { Utils.error("Checking for new constants, but should not happen at this stage."); }
		int numberOfArgs = Utils.getSizeSafely(args);
		if (numberOfArgs < 1) { return; }
		List<TypeSpec> typeSpecs = collectLiteralArgumentTypes(pName, numberOfArgs);
		if (debugLevel > 2) { Utils.println("%          typeSpecs(" + pName + "/" + numberOfArgs + ") = " + typeSpecs); }
		for (int i = 0; i < numberOfArgs; i++) if (args.get(i) instanceof Constant) {
			Constant c = (Constant) args.get(i);
			// See if already dealt with this constant/type pair.
			Set<Constant> lookup1 = constantTypePairsHandled.get(typeSpecs.get(i).isaType);
            if (lookup1 == null) { // Never saw this type before.
            	stringHandler.addNewConstantOfThisType(c, typeSpecs.get(i).isaType);
                lookup1 = new HashSet<>(4);
                constantTypePairsHandled.put(typeSpecs.get(i).isaType, lookup1);
            }
            if (!lookup1.contains(c)) { // Save a call to the stringHandler if this constant has already been processed.
            	if (debugLevel > 1) { Utils.println("% Add constant '" + c + "' of type '" + typeSpecs.get(i).isaType + "'."); }
                stringHandler.addNewConstantOfThisType(c, typeSpecs.get(i).isaType);
                lookup1.add(c);
            }
		}
	}

	boolean isClosedWorldAssumption(Literal lit) { // Require NULL so calling code explicitly makes sure this is a generic query.
		if (lit == null) { return closedWorldAssumption; }
		if (closedWorldAssumption) {
			return !neverCWAonThisLiteral(lit); 
		} else {
			return alwaysCWAonThisLiteral(lit); 
		}
	}
	private boolean neverCWAonThisLiteral( Literal lit) {
		if (neverCWAonThisPredNameArity != null) {
			Collection<Integer> arities = neverCWAonThisPredNameArity.get(lit.predicateName);
			if (arities == null) { return false; }
			return arities.contains(lit.numberArgs());
		}
		return false;
	}
	private boolean alwaysCWAonThisLiteral(Literal lit) {
		if (alwaysCWAonThisPredNameArity != null) {
			Collection<Integer> arities = alwaysCWAonThisPredNameArity.get(lit.predicateName);
			if (arities == null) { return false; }
			return arities.contains(lit.numberArgs());
		}
		return false;
	}

}
