package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.MapOfLists;
import edu.wisc.cs.will.Utils.MapOfSets;
import edu.wisc.cs.will.Utils.MessageType;
import edu.wisc.cs.will.Utils.Utils;

import java.io.IOException;
import java.io.Serializable;
import java.util.*;

/*
 * @author shavlik
 *
 *  All predicates with the same name map to the same instance.
 */
public class PredicateName extends AllOfFOPC implements Serializable {
	private static final long serialVersionUID = -7155497162394602383L;
	public final String name;
	private   List<PredicateSpec>      typeSpecList = null; // Information about this Predicate, e.g. legal arguments to it.  A 'type' describes both the kind of arguments it takes (e.g., 'people' are 'books') and whether these arguments are "input" variables, "output" variables, or constants.
	private   List<PredicateSpec>      typeOnlyList = null; // Similar to above, but the input/output markers are not included.
	private   Set<Integer>             typeDeSpeced = null; // Modes that have been disabled - currently all modes of a given arity are disabled
	Set<Integer> boundariesAtEnd_1D       = null; // If true, the last N arguments specify the boundaries, e.g., if 1D the last two arguments are lower and upper, if 2d then they are lower1, upper1, lower2, upper2, etc.
	private Set<Integer> boundariesAtEnd_2D       = null; // If true, the last N arguments specify the boundaries, e.g., if 1D the last two arguments are lower and upper, if 2d then they are lower1, upper1, lower2, upper2, etc.
	private Set<Integer> boundariesAtEnd_3D       = null; // If true, the last N arguments specify the boundaries, e.g., if 1D the last two arguments are lower and upper, if 2d then they are lower1, upper1, lower2, upper2, etc.
	private   Set<Integer> isaInterval_1D           = null; // When used in the form "predicateName(lower, value, upper)" this predicate represents an interval (or a "tile"), i.e., it is true if value is in the range [lower, upper).  Used when pruning search trees in ILP.
	private   Set<Integer> isaInterval_2D           = null; // Similar, but now represents a 2D rectangle and is true if the "x-y" values are in it.  The expected format is predicateName(lowerX, X, upperX, lowerY, Y, upperY). 
	private   Set<Integer> isaInterval_3D           = null; // Similar, but now represents a 3D hyper-rectangle and is true if the "x-y-z" values are in it.  The expected format is predicateName(lowerX, X, upperX, lowerY, Y, upperY, lowerX, Z, upperZ).
	private   Map<Integer,Integer> maxOccurrencesPerArity = null; // During structure (i.e., rule) learning, cannot appear more than this many times in one rule.
	private   Map<Integer,Map<List<Type>,Integer>> maxOccurrencesPerInputVars = null; // During structure (i.e., rule) learning, cannot appear more than this many times in one rule.
	transient private   Map<Integer,MapOfLists<PredicateNameAndArity, Pruner>>  pruneHashMap      = null; // The first integer is the arity of this predicate (of 'prunableLiteral').  The second key is the predicate name of 'ifPresentLiteral' (could also index on the arity of this literal, but that doesn't seem necessary).  A Pruner instance contains 'prunableLiteral', 'ifPresentLiteral', and the max number of ways that 'ifPresentLiteral' can be proven from the current set of rules.
	private   Set<Integer> canBeAbsentThisArity                         = null;  // OK if this predicate name with one of these arities can be absent during theorem proving.
	private   boolean      canBeAbsentAnyArity                          = false;
	private   Set<Integer> dontComplainAboutMultipleTypesThisArity      = null;  // OF if this predicate/arity have multiple types for some argument.
	private   boolean      dontComplainAboutMultipleTypesAnyArity       = false;
	private   Map<FunctionAsPredType,Map<Integer,Integer>>  functionAsPredSpec  = null;  // See if this predicate/arity holds a value of the type specified by String in this position.
	private   Set<Integer>                   bridgerSpec                = null;  // See if this predicate/arity is meant to be a 'bridger' predicate during ILP's search for clauses.  If the arg# is given (defaults to -1 otherwise), then all other arguments should be bound before this is treated as a 'bridger.'
	private   Set<Integer>                   temporary                  = null;  // See if this predicate/arity is only a temporary predicate and if so, it needs to be renamed to avoid name conflicts across runs.  So slightly different than inline.
	private   Set<Integer>                   inlineSpec                 = null;  // See if this predicate/arity is meant to be a 'inline' predicate during ILP's search for clauses.  If the arg# is given (defaults to -1 otherwise), then all other arguments should be bound before this is treated as a 'bridger.'
	private   boolean                        filter                     = false; // Should this predicate (all arities) be filtered from learned rules, presumably because it is a helper function for guiding search.
	private   Set<Integer>                   queryPredSpec              = null;  // Used with MLNs.
	private   Set<Integer>                   supportingLiteral          = null;  // Is this a supporting literal that needs to attached to learned theories?
    private   Set<Integer>                   containsCallable           = null;  // One of the terms of the predicate is called during execution of the predicate.
	private   Map<Integer,Double>            cost                       = null;  // See if this predicate/arity has a cost (default is 1.0).  Costs are used for scoring clauses.
	private   boolean                        costIsFinal                = false; // Is the cost frozen?
	private   Map<Integer,RelevanceStrength> relevance                  = null;  // See if this predicate/arity has a relevance (default is NEUTRAL).

	/* Map from non-operation arities to operational predicates.
     *
     * Currently, the operational predicates must be the same arity as the
     * non-operational one.  Additionally, they must take the exact same arguments
     * in the same order.
     *
     * We store the operational names as a PredicateNameAndArity just to
     * make it explicit what the arity of the operational predicate is.
     */
    private   MapOfSets<Integer,PredicateNameAndArity> operationalExpansion = null;
	
	public    boolean printUsingInFixNotation = false;
	transient private HandleFOPCstrings stringHandler;  // The stringHandler needed to de-serialize the Predicate.

	PredicateName(String name, HandleFOPCstrings stringHandler) { // This is protected because getPredicateName(String name) should be used instead.
		this.name          = name;
		this.stringHandler = stringHandler;
	}	

	public List<PredicateSpec> getTypeList() {
		if (typeDeSpeced == null || typeSpecList == null) { return typeSpecList; }
		
		List<PredicateSpec> results = new ArrayList<>(1);
		for (PredicateSpec pSpec : typeSpecList) {
			int          arity = pSpec.getArity();
			if (!typeDeSpeced.contains(arity)) { results.add(pSpec); }
		}
		return results;
	}
	// Only return when the arity matches.
	public List<PredicateSpec> getTypeListForThisArity(int numberArgs) {
		if (typeSpecList == null) { return null; }
		List<PredicateSpec> results = new ArrayList<>(1);
		for (PredicateSpec pSpec : getTypeList()) {
			if (pSpec.getArity() == numberArgs) {
				results.add(pSpec);
			}
		}
		return results;
	}
	public List<PredicateSpec> getTypeOnlyList() {
		return typeOnlyList;
	}
	// Only return when the arity matches.
	public List<PredicateSpec> getTypeOnlyList(int numberArgs) {
		if (typeOnlyList == null) { return null; }
		boolean allOK = true;
		for (PredicateSpec pSpec : typeOnlyList) {
			if (Utils.getSizeSafely(pSpec.getSignature()) != numberArgs) {
				allOK = false;
				break;
			}
		}
		if (allOK) { return typeOnlyList; } // Save creating a new list.
		List<PredicateSpec> results = new ArrayList<>(1);
		for (PredicateSpec pSpec : typeOnlyList) {
			if (Utils.getSizeSafely(pSpec.getSignature()) == numberArgs) {
				results.add(pSpec);
			}
		}
		return results;
	}

	// See if this literal is a predicate that holds a numeric value.
	boolean isFunctionAsPredicate(List<Term> arguments) {
		if (functionAsPredSpec == null) { return false; }
		Map<Integer,Integer> lookup1 = functionAsPredSpec.get(null);
		if (lookup1 == null) { return false; }
		return (lookup1.get(Utils.getSizeSafely(arguments)) != null);
	}

	public enum FunctionAsPredType {      numeric
	}

	// See if this predicate name is temporary for this run (if so, it might need to be renamed to avoid name conflicts across runs).
	public boolean isaTemporaryName(int arity) {
		if (temporary == null)      { return false; }
		if (temporary.contains(-1)) { return true;  } // "-1" means "any arity matches."
		return (temporary.contains(arity));
	}
	
	// See if this literal is a predicate that serves as a 'bridge' in ILP searches.
	boolean isaBridgerLiteral(List<Term> arguments) {
		return (bridgerSpec != null && bridgerSpec.contains(Utils.getSizeSafely(arguments)));
	}

	// See if this literal is a predicate whose body should be inlined after learning.
	public boolean isaInlined(int arity) {
		return (inlineSpec != null && inlineSpec.contains(arity));
	}

	/* Adds an operational expansion of the predicate.
     *
     * Operational expansions are keyed on the predicate name and the arity.
     * A PredicateNameAndArity is used to provide both the name and arity of
     * the operational expansion.
     */
	private void addOperationalExpansion(PredicateNameAndArity operationalPredicateNameAndArity) {
        if ( operationalExpansion == null ) {
            operationalExpansion = new MapOfSets<>();
        }

        operationalExpansion.put(operationalPredicateNameAndArity.getArity(), operationalPredicateNameAndArity);
    }

    /* Adds an operational expansion of the predicate.
     *
     * Operational expansions are keyed on the predicate name and the arity.
     * A PredicateNameAndArity is used to provide both the name and arity of
     * the operational expansion.
     */
    public void addOperationalExpansion(PredicateName operationalPredicateName, int arity) {
        addOperationalExpansion(new PredicateNameAndArity(operationalPredicateName, arity));
    }

	/*
	 * Can prune 'prunableLiteral' if 'ifPresentLiteral' is present (and both unify consistently with the current literal being considered for adding to the current clause during ILP search).
	 * However, if 'ifPresentLiteral' has 'warnIfPresentLiteralCount' ways to be proven, warn the user (i.e., prune is based on the assumption that fewer than this number of clauses for this literal/arity exist).
	 * Note: this code does not check for duplicate entries (which would need to use 'variant' since variables are present).
	 */
	public void recordPrune(Literal prunableLiteral, Literal ifPresentLiteral, int warnIfPresentLiteralCount, int truthValue) { // TruthValue: -1 means 'prune because false', 1 means because true, and 0 means unknown.
		if (prunableLiteral  == null) {
			Utils.error("Should not pass in null's.");
		}
		// Might NOT want to do this filtering, since this requires MODE's to precede PRUNE's in files.  Plus, not a lot of harm in storing these (the "ifPresent's" can waste some cycles).
		
		if (pruneHashMap == null) {
			pruneHashMap = new HashMap<>();
		}

		int arity = prunableLiteral.getArity();
		MapOfLists<PredicateNameAndArity, Pruner> prunes = getPruners(arity);
		if (prunes == null) {
			prunes = new MapOfLists<>();
			pruneHashMap.put(arity, prunes);
		}

        PredicateNameAndArity pnaa = ifPresentLiteral == null ? null : ifPresentLiteral.getPredicateNameAndArity();

		prunes.add(pnaa, new Pruner(prunableLiteral, ifPresentLiteral, warnIfPresentLiteralCount, truthValue));
	}
	
	/*
	 * Get the list of pruning rules for this literal (whose head should be that of this PredicateName instance, but we also need the specific arity).
	 * Note that this method does not check for those pruners that unify with prunableLiteral.  That is the job of the caller.
	 */
	   public MapOfLists<PredicateNameAndArity, Pruner> getPruners(int arityOfPrunableLiteral) {
		if (pruneHashMap == null) { return null; }
		return pruneHashMap.get(arityOfPrunableLiteral);
	}

	void recordMode(List<Term> signature, List<TypeSpec> typeSpecs, int max, int maxPerInputVars, boolean okIfDup) {
        if (Utils.getSizeSafely(signature) != Utils.getSizeSafely(typeSpecs)) {
            Utils.waitHere(this + " sig = " + signature + " specs = " + typeSpecs);
        }

        PredicateSpec pSpec = new PredicateSpec(signature, typeSpecs, this);

        addToTypeListForILP(pSpec, !okIfDup);
        addToTypeListForMLN(pSpec);

        int arity = Utils.getSizeSafely(signature);

        setMaxOccurrences(arity, max); // Always do these to catch user errors where the same spec is given, once with a max and another time w/o.
        setMaxOccurrencesPerInputVars(arity, pSpec, maxPerInputVars);

	}
	
	void disableMode(List<Term> signature, List<TypeSpec> typeSpecs) {
        if (Utils.getSizeSafely(signature) != Utils.getSizeSafely(typeSpecs)) {
            Utils.waitHere(this + " sig = " + signature + " specs = " + typeSpecs);
        }

        int arity = Utils.getSizeSafely(signature);
        addToDeSpecTypeList(arity);
	}
	
	private void addToTypeListForILP(PredicateSpec pSpec, boolean warnIfDup) {
		boolean checkForWarnings = !name.startsWith("isaInteresting") &&  !name.startsWith("isaDifferentInteresting");	
		if (checkForWarnings) {
			boolean hasPlusArg = false; // Modes should have at least one "input argument" or new predicates won't be coupled to the clause being created.  (Maybe allow this to be overridden?)
			if (pSpec.getTypeSpecList() != null) for (TypeSpec spec : pSpec.getTypeSpecList()) if (spec.mustBeBound()) { hasPlusArg = true; break; }
			if (!hasPlusArg) {
				Utils.warning("At least one argument in a mode should be an input argument.  You provided " + pSpec + " for '" + name + "'.");
			}
		}

		if (typeSpecList == null) { typeSpecList  = new ArrayList<>(1); }
		for (PredicateSpec oldPspec : typeSpecList) if (oldPspec.equals(pSpec)) {
			if (warnIfDup && checkForWarnings) { // Add a way to override?  TODO
				Utils.warning("% Duplicate type specification found for '" + this + "':\n%   '" + pSpec + "'/new vs.\n%   '" + oldPspec + "'/old."); 
			}
			return;
		}
		typeSpecList.add(pSpec);
	}	
	
	private void addToTypeListForMLN(PredicateSpec pSpec) {
		if (typeOnlyList == null) { typeOnlyList  = new ArrayList<>(1); }
		PredicateSpec pSpecStripped = pSpec.strip();
		if (typeOnlyList.contains(pSpecStripped)) { return; } // OK here if duplicates, so no need to warn (since ILP +/-/# markers might be different).
		typeOnlyList.add(pSpecStripped);
	}
	
	private void addToDeSpecTypeList(int arity) {
		if (typeDeSpeced == null) { typeDeSpeced = new HashSet<>(4); }
		typeDeSpeced.add(arity);
	}

	/**
	 * This is used to say that this predicate/arity should appear at most max times in a learned rule.
	 */
	private void setMaxOccurrences(int arity, int max) {		
		if (maxOccurrencesPerArity == null) {
			maxOccurrencesPerArity = new HashMap<>(4);
		}
		Integer current = maxOccurrencesPerArity.get(arity);
		if (current == null) {
			maxOccurrencesPerArity.put(arity, max);
		}
		else if (current > max) { // Use the MIN of all specifications.
			maxOccurrencesPerArity.put(arity, max); 
		}		
	}	
	public Integer getMaxOccurrences(int arity) {
		if (maxOccurrencesPerArity == null) { return null; }
		return maxOccurrencesPerArity.get(arity);
	}
	
	/*
	 * This is used to say that this predicate/arity should appear at most max times in a learned rule
	 * FOR a given binding to the "input" arguments in the typeSpecs.
	 */
	private void setMaxOccurrencesPerInputVars(int arity, PredicateSpec typeSpecs, int max) {		
		if (arity < 2) { 
			if (max < Integer.MAX_VALUE) { 
				Utils.waitHere("It doesn't make sense to call setMaxOccurrencesPerInputVars unless a literal has at least two arguments.  You provided: '" + typeSpecs + "'.");
			}
			return;
		}
		if (maxOccurrencesPerInputVars == null) {
			maxOccurrencesPerInputVars = new HashMap<>(4);
		}
		Map<List<Type>, Integer> firstLookUp = maxOccurrencesPerInputVars.computeIfAbsent(arity, k -> new HashMap<>(4));
		List<Type> inputArgumentTypes = TypeSpec.getListOfInputArgumentTypes(typeSpecs);
		if (inputArgumentTypes.size() < 1) {
			Utils.error("It does not make sense to setMaxOccurrencesPerInputVars for a mode where there are NO input variables: " + typeSpecs); 
		}
		Integer secondLookUp = firstLookUp.get(inputArgumentTypes);
		if (secondLookUp == null) { // Not currently specified.
			firstLookUp.put(inputArgumentTypes, max);
		}
		else if (secondLookUp > max) { // Maybe use the MIN of all specifications?
			firstLookUp.put(inputArgumentTypes, max);
		}		
	}
	public Integer getMaxOccurrencesPerInputVars(int arity, List<Type> inputArgumentTypes) {
		if (maxOccurrencesPerInputVars == null) { return null; }
		Map<List<Type>,Integer> firstLookUp = maxOccurrencesPerInputVars.get(arity);
		if (firstLookUp == null) { return null; }
		return firstLookUp.get(inputArgumentTypes);
	}
	public boolean haveMaxOccurrencesPerInputVarsForThisArity(int arity) { // Allow a quick look to see if worth computing the input arguments.
		return maxOccurrencesPerInputVars != null && maxOccurrencesPerInputVars.get(arity) != null;
	}
	
	/*
	 * Does this literal match some mode? That is, is there some mode for the predicate name of the same arity as this literal?
	 *
	 * @return Whether the given literal has a matching mode.
	 */
	public boolean hasMatchingMode(Literal lit) {
		if (typeSpecList == null) { return false; }
		int arity = lit.numberArgs();
		List<PredicateSpec> items = getTypeList();
		for (PredicateSpec spec : items) if (arity == Utils.getSizeSafely(spec.getSignature())) { return true; }
		if (typeDeSpeced == null) { Utils.println("% No mode match to '" + lit + "' in " + items); }  // Only warn if not de-spec'ed.
		return false;
	}
	
	public boolean canBeAbsent(int arity) {
		if (canBeAbsentAnyArity) { return true; }
		return canBeAbsentThisArity != null && canBeAbsentThisArity.contains(arity);
	}	
	public void setCanBeAbsent(int arity) {
		if (arity < 0) { canBeAbsentAnyArity = true; }
		if (canBeAbsentThisArity == null) { canBeAbsentThisArity = new HashSet<>(4); }
		if (canBeAbsentThisArity.contains(arity)) { return; } // No need to add again.
		canBeAbsentThisArity.add(arity);
	}

	public boolean dontComplainAboutMultipleTypes(int arity) {
		if (dontComplainAboutMultipleTypesAnyArity) { return true; }
		return dontComplainAboutMultipleTypesThisArity != null && dontComplainAboutMultipleTypesThisArity.contains(arity);
	}	
	public void setDontComplainAboutMultipleTypes(int arity) {
		if (arity < 0) { dontComplainAboutMultipleTypesAnyArity = true; }
		if (dontComplainAboutMultipleTypesThisArity == null) { dontComplainAboutMultipleTypesThisArity = new HashSet<>(4); }
		if (dontComplainAboutMultipleTypesThisArity.contains(arity)) { return; } // No need to add again.
		dontComplainAboutMultipleTypesThisArity.add(arity);
	}	
	
	// See FileParser.processIsaInterval() for more documentation.
	public boolean isaInterval_1D(Integer arity) {
		if    (isaInterval_1D == null) { return false; } // For some reason Java throws a nullPointerException without this second test.  Seems to be a bug.
		return isaInterval_1D.contains(arity);
	}
	public void setIsaInterval_1D(int arity, boolean boundariesAtEnd) {
		if (isaInterval_1D     == null) { isaInterval_1D     = new HashSet<>(4); }
		if (boundariesAtEnd_1D == null) { boundariesAtEnd_1D = new HashSet<>(4); }
		if (isaInterval_1D(    arity)) { return; }
		isaInterval_1D.add(    arity);
		if (boundariesAtEnd) { boundariesAtEnd_1D.add(arity); }
	}

	public boolean isaInterval_2D(int arity) {
		if    (isaInterval_2D == null) { return false; }
		return isaInterval_2D.contains(arity);
	}
	public void setIsaInterval_2D(int arity, boolean boundariesAtEnd) {
		if (isaInterval_2D     == null) { isaInterval_2D     = new HashSet<>(4); }
		if (boundariesAtEnd_2D == null) { boundariesAtEnd_2D = new HashSet<>(4); }
		if (isaInterval_2D(    arity)) { return; }
		isaInterval_2D.add(    arity);
		if (boundariesAtEnd) { boundariesAtEnd_2D.add(arity); }
	}

	public boolean isaInterval_3D(int arity) {
		if    (isaInterval_3D == null) { return false; }
		return isaInterval_3D.contains(arity);
	}
	public void setIsaInterval_3D(int arity, boolean boundariesAtEnd) {
		if (isaInterval_3D     == null) { isaInterval_3D     = new HashSet<>(4); }
		if (boundariesAtEnd_3D == null) { boundariesAtEnd_3D = new HashSet<>(4); }
		if (isaInterval_3D(    arity)) { return; }
		isaInterval_3D.add(    arity);
		if (boundariesAtEnd) { boundariesAtEnd_3D.add(arity); }
	}

	public void addFunctionAsPred(FunctionAsPredType type, int arity, int position) throws IllegalStateException {
		if (functionAsPredSpec == null) { 
			functionAsPredSpec = new HashMap<>();
		}
		Map<Integer, Integer> lookup1 = functionAsPredSpec.computeIfAbsent(type, k -> new HashMap<>(4));
		Integer lookup2 = lookup1.get(arity);
		if (lookup2 == null) { // Not currently specified for this arity.
			lookup1.put(arity, position);
		}
		else if (lookup2 != position) {
			throw new IllegalStateException("Cannot set " + type + "FunctionAsPred of '" + name + "/" + arity + "' to position " + position + " because it is currently = " + lookup2 + ".");
		}
		if (type != null) { addFunctionAsPred(null, arity, position); } // Also store here to say SOME type is specified in this position.
	}
	
	public void addBridger(int arity) {
		if (bridgerSpec == null) {
			bridgerSpec = new HashSet<>(4);
		}
		boolean firstLookUp = bridgerSpec.contains(arity);
		if (!firstLookUp) { // Not currently specified.
			bridgerSpec.add(arity);
		}
		else if (stringHandler.warningCount < HandleFOPCstrings.maxWarnings) { Utils.println("% WARNING #" + Utils.comma(stringHandler.warningCount++) + ": Duplicate bridger of " + name + "/" + arity + ".  Will ignore."); }		
	}
	
	public void addTemporary(int arity) { // -1 means 'any parity.'
		if (temporary == null) {
			temporary = new HashSet<>(4);
		}
		boolean firstLookUp = temporary.contains(arity);
		if (!firstLookUp) { // Not currently specified.
			temporary.add(arity);
		}
		else if (stringHandler.warningCount < HandleFOPCstrings.maxWarnings) { Utils.println("% WARNING #" + Utils.comma(stringHandler.warningCount++) + ": Duplicate temporary of " + name + "/" + arity + ".  Will ignore."); }		
	}

	public void addInliner(int arity) {
		if (inlineSpec == null) {
			inlineSpec = new HashSet<>(4);
		}
		boolean firstLookUp = inlineSpec.contains(arity);
		if (!firstLookUp) { // Not currently specified.
			inlineSpec.add(arity);
		}
		else if (stringHandler.warningCount < HandleFOPCstrings.maxWarnings) { Utils.println("% WARNING #" + Utils.comma(stringHandler.warningCount++) + ": Duplicate inline of '" + name + "/" + arity + "'.  Will ignore."); }		
	}
	
	public void addFilter() {
		filter = true;
	}

	public boolean filter() {
		return filter;
	}

	public void addQueryPred(int arity) {
		if (queryPredSpec == null) {
			queryPredSpec = new HashSet<>(4);
		}
		boolean firstLookUp = queryPredSpec.contains(arity);
		if (!firstLookUp) { // Not currently specified.
			queryPredSpec.add(arity);
		}
		else if (stringHandler.warningCount < HandleFOPCstrings.maxWarnings) { Utils.println("% WARNING #" + Utils.comma(stringHandler.warningCount++) + ": Duplicate query predicate of " + name + "/" + arity + ".  Will ignore."); 
		}		
	}

	public void setCost(int arity, double predicateCost, boolean isFinal) {
		if (costIsFinal) { 
			return; // Just return silently
		}
		if (cost == null) {
			cost = new HashMap<>(4);
		}
		boolean firstLookUp = cost.containsKey(arity);
		if (firstLookUp) { 
			if (isFinal) {
				cost.put(arity, predicateCost);
			}
			else if (stringHandler.duplicateCostWarningEnabled && stringHandler.warningCount < HandleFOPCstrings.maxWarnings && cost.get(arity) != predicateCost) {
				Utils.println(MessageType.STRING_HANDLER_PREDICATE_COSTS, "% WARNING #" + Utils.comma(stringHandler.warningCount++) + ": Duplicate cost of '" + name + "/" + arity + "'.  Had previously said cost = " + cost.get(arity) + " and now saying cost = " + predicateCost + ".\n% Will use this latest setting.\n");
			}
		}
		cost.put(arity, predicateCost);
		stringHandler.setPredicatesHaveCosts();
		if (isFinal) { costIsFinal = true; }
	}

	public double getCost(int arity) {
		if (cost == null) { return 1.0; }  // The default cost.
		boolean firstLookUp = cost.containsKey(arity);
		if (firstLookUp) { return cost.get(arity); }
		return 1.0; // The default cost.
	}
	
	public void markAsSupportingPredicate(int arity, boolean okIfDup) {
		if (supportingLiteral == null) {
			supportingLiteral = new HashSet<>(4);
		}
		boolean firstLookUp = supportingLiteral.contains(arity);
		if (!firstLookUp) { // Not currently specified.
			supportingLiteral.add(arity);
		}
		else if (!okIfDup && stringHandler.warningCount < HandleFOPCstrings.maxWarnings) { Utils.println("% WARNING #" + Utils.comma(stringHandler.warningCount++) + ": Duplicate 'supporter' of '" + name + "/" + arity + "'.  Will ignore."); }		
	}
	public boolean isaSupportingPredicate(int arity) {
		return supportingLiteral != null && supportingLiteral.contains(arity);
	}
	
	// On these, the later override the earlier (allows code to change these).
	void setRelevance(int arity, RelevanceStrength strength) {
		if (relevance == null) {
			relevance = new HashMap<>(4);
		}
		boolean firstLookUp = relevance.containsKey(arity);
		if (firstLookUp) { 
			if (stringHandler.warningCount < HandleFOPCstrings.maxWarnings && relevance.get(arity) != strength) {
				if (strength.compareTo(relevance.get(arity)) < 0) { // Turn off these warnings and just print for now.
					Utils.println("% WARNING #" + Utils.comma(stringHandler.warningCount++) + ": Duplicate relevance of '" + name + "/" + arity + "'.\n% Had previously said relevance = " + relevance.get(arity) + " and now saying relevance = " + strength + ".\n% Will keep the stronger.  To lower a relevance use: toBeWritten.\n");
				} else {
					Utils.println("% WARNING #" + Utils.comma(stringHandler.warningCount++) + ": Duplicate relevance of '" + name + "/" + arity + "'.\n% Had previously said relevance = " + relevance.get(arity) + " and now saying relevance = " + strength + ".\n% Will keep the stronger.\n");
				}
			}
			if (strength.compareTo(relevance.get(arity)) < 0) { return; }
		} 
		relevance.put(arity, strength);
		double aCost = stringHandler.convertRelevanceStrengthToCost(strength);
		setCost(arity, aCost, false);
	}

	public RelevanceStrength getRelevance(int arity) {
		if (relevance == null) { return null; }
		boolean firstLookUp = relevance.containsKey(arity);
		if (firstLookUp) { return relevance.get(arity); }
		return null;
	}

	int returnFunctionAsPredPosition(int arity) {
		if (functionAsPredSpec == null) { return -1; }
		Map<Integer,Integer> lookup = functionAsPredSpec.get(null);
		if (lookup == null) { return -1; }
		Integer result = lookup.get(arity);
		if (result == null) { return -1; }
		return result;
	}
	
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return name;
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return name;
	}

   /*
	* Methods for reading a Object cached to disk.
    */
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        if (!(in instanceof FOPCInputStream)) {
            throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject() input stream must support FOPCObjectInputStream interface");
        }

        in.defaultReadObject();

        FOPCInputStream fOPCInputStream = (FOPCInputStream) in;

        this.stringHandler = fOPCInputStream.getStringHandler();
    }

    /* Replaces the stream object with a cached one if available.
     *
     */
    private Object readResolve() {
        return stringHandler.getPredicateName(this);
    }

	@Override
	public PredicateName applyTheta(Map<Variable, Term> bindings) {
		return this;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final PredicateName other = (PredicateName) obj;
		return Objects.equals(this.name, other.name);
	}

    @Override
    public int hashCode() {
        int hash = 5;
        hash = 59 * hash + (this.name != null ? this.name.hashCode() : 0);
        return hash;
    }

    void setContainsCallable(int arity) {
        if ( containsCallable == null ) {
            containsCallable = new HashSet<>();
        }
        containsCallable.add(arity);
    }


}