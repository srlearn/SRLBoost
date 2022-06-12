package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;
import java.util.*;

/*
 * @author shavlik
 *
 *  All predicates with the same name map to the same instance.
 */
public class PredicateName extends AllOfFOPC implements Serializable {
	public final String                   name;
	private   List<PredicateSpec>      typeSpecList = null; // Information about this Predicate, e.g. legal arguments to it.  A 'type' describes both the kind of arguments it takes (e.g., 'people' are 'books') and whether these arguments are "input" variables, "output" variables, or constants.
	private   List<PredicateSpec>      typeOnlyList = null; // Similar to above, but the input/output markers are not included.
	private   Set<Integer>             typeDeSpeced = null; // Modes that have been disabled - currently all modes of a given arity are disabled
	private   Map<Integer,Integer> maxOccurrencesPerArity = null; // During structure (i.e., rule) learning, cannot appear more than this many times in one rule.
	private   Map<Integer,Map<List<Type>,Integer>> maxOccurrencesPerInputVars = null; // During structure (i.e., rule) learning, cannot appear more than this many times in one rule.
	private   Set<Integer> canBeAbsentThisArity                         = null;  // OK if this predicate name with one of these arities can be absent during theorem proving.
	private   boolean      canBeAbsentAnyArity                          = false;
	private   Set<Integer> dontComplainAboutMultipleTypesThisArity      = null;  // OF if this predicate/arity have multiple types for some argument.
	private   boolean      dontComplainAboutMultipleTypesAnyArity       = false;
	private   Set<Integer>                   bridgerSpec                = null;  // See if this predicate/arity is meant to be a 'bridger' predicate during ILP's search for clauses.  If the arg# is given (defaults to -1 otherwise), then all other arguments should be bound before this is treated as a 'bridger.'
	private   Set<Integer>                   queryPredSpec              = null;  // Used with MLNs.
	private   Set<Integer>                   containsCallable           = null;  // One of the terms of the predicate is called during execution of the predicate.

	final transient private HandleFOPCstrings stringHandler;  // The stringHandler needed to de-serialize the Predicate.

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

	// See if this literal is a predicate that serves as a 'bridge' in ILP searches.
	boolean isaBridgerLiteral(List<Term> arguments) {
		return (bridgerSpec != null && bridgerSpec.contains(Utils.getSizeSafely(arguments)));
	}

	void recordMode(List<Term> signature, List<TypeSpec> typeSpecs, int max, int maxPerInputVars) {
        if (Utils.getSizeSafely(signature) != Utils.getSizeSafely(typeSpecs)) {
            Utils.waitHere(this + " sig = " + signature + " specs = " + typeSpecs);
        }

        PredicateSpec pSpec = new PredicateSpec(signature, typeSpecs, this);

        addToTypeListForILP(pSpec);
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
	
	private void addToTypeListForILP(PredicateSpec pSpec) {
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

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return name;
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return name;
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

    void setContainsCallable() {
        if ( containsCallable == null ) {
            containsCallable = new HashSet<>();
        }
        containsCallable.add(1);
    }


}