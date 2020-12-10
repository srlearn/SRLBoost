package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.Boosting.OneClass.PairWiseExampleScore;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.Utils.NumberGroundingsCalculator;
import edu.wisc.cs.will.DataSetUtils.ArgSpec;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.ILP.Regression.BranchStats;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchNode;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask;

import java.util.*;

/*
 * @author shavlik
 */

public class SingleClauseNode extends SearchNode {
	private static final long serialVersionUID = -2094365783950475856L;

	private final static boolean renameAllVariablesWheneverPrinting = true;
	
	Literal literalAdded    = null;
	double  score           = Double.NaN; // Cache these to save recomputing (recomputing fast except for regression?).
	private double  posCoverage     = -1.0;     //   Also, each child node only stores the extensions to the clause body.
	double  negCoverage     = -1.0; // Everything is done with WEIGHTED examples (including the seeds).
	int     numberOfNewVars = 0;    // There is a max number of new (i.e., output) variables in a clause.  This is the total all the way to the root.
	List<Type>                 typesPresent = null; // Keep track of the different types of terms added by this node.  If there is a need to reduce the size of nodes, could compute this when needed from the map below.
	private List<AnnotatedLiteral>   dontReconsider = null; // If something is discarded at some point, don't reconsider it further down the search tree.  DON'T COPY (in buildNewAncestor) THIS WHEN REMOVING AN INTERMEDIATE LITERAL SINCE THAT INTERMEDIATE LITERAL MIGHT BE THE REASON FOR AN ENTRY (SO NEED TO RECREATE THE ONES THAT SHOULD HAVE BEEN KEPT).
	int                predicateOccurrences = 0;    // Count of how often this literal's predicate has occurred (this is a CUMULATIVE count from this node, assuming this predicate was added here, to the root).
	int    predicateOccurrencesPerFixedVars = 0;    // Count of how often this literal's predicate has occurred FOR THESE + and # variables (also a CUMULATIVE count).  This is how Aleph limits counts.
	List<Literal>            canonicalForm  = null; // Once put into a canonical form, cache it.
	private Set<Example>  posExamplesThatFailedHere = null; // Record where each example fails to be satisfied.
	private Set<Example>  negExamplesThatFailedHere = null; // Save space by not creating these until some examples fail at a node.
	Map<Type,List<Term>>           typesMap = null; // AlsogetConstrainsArgumentTypes store this piece-by-piece at nodes (i.e., need to climb to root to collect/check all of them).
	private   Map<Term,Type>          typesOfNewTerms = null; // Record the types of new terms, if any, added here.  Used in at least the case where when evaluated on the full dataset a node has insufficient positive coverage to be kept.  This prevents it from being considered again.
	Map<Term,Integer>           depthOfArgs = null; // For each 'leaf term' (i.e., recur into functions) in this clause's literal, record its distance from the head.  An input var's depth is the depth of its parent.  An output var's depth is 1 + the max depth of all the input args in the literal.
	final boolean                         pruneMe = false;// Can do some pruning here that the normal pruners don't handle.
	boolean                        timedOut = false;
	private   String                      extraString = null; // Used to augment the comment in the toString() with info about the examples that reach this node.
	
	private SingleClauseNode 	 startingNodeForReset = null; // Everytime we select new examples, we reset the scores but we lose the starting node information.(this is not a parent node when number of literals per node >1)

	SingleClauseNode(StateBasedSearchTask task) {
		super(task);
	}
	public SingleClauseNode(SearchNode parentNode, Literal literalAdded) {
		this(parentNode, literalAdded, null, null, null, null);
	}
	public SingleClauseNode(SearchNode parentNode, Literal literalAdded, Map<Term, Integer> argDepths, List<Type> typesPresent, Map<Type, List<Term>> typesMap, Map<Term, Type> typesOfNewTerms) {
		super(parentNode);
		depthOfArgs          = argDepths;
		this.literalAdded    = literalAdded;
		this.typesPresent    = typesPresent;
		this.typesMap        = typesMap;
		this.typesOfNewTerms = typesOfNewTerms;
	}

	boolean matchesThisExample(Example ex, boolean isaPosExample) throws SearchInterrupted {
		if (getPosCoverage() < 0.0) { computeCoverage(); }
		if (isaPosExample) { return !posExampleAlreadyExcluded(ex); }
		return                      !negExampleAlreadyExcluded(ex);
	}

	void addTypeOfNewTerm(Term term, Type type) {
		if (typesOfNewTerms == null) { typesOfNewTerms = new HashMap<>(4); }
		typesOfNewTerms.put(term, type);
	}

	void markDepthOfLeafTerms(List<Term> arguments, int thisDepth) {
		if (arguments == null) { return; }
		for (Term arg : arguments) {
			if (arg instanceof Function) {
				markDepthOfLeafTerms( ((Function) arg).getArguments(), thisDepth);
			} else { depthOfArgs.put(arg, thisDepth); }
		}
	}
	
    private boolean proveExampleBodies(LearnOneClause theILPtask, Literal target, List<List<Literal>> clauseBodies, Literal ex, BindingList bindings) throws SearchInterrupted {
    	if (Utils.getSizeSafely(clauseBodies) < 1) { 
    		if (bindings != null && bindings.theta.size() > 0) { bindings.theta.clear(); } // Revert to the empty binding list. 
    		return theILPtask.unifier.unify(target, ex, bindings) != null;
    	}
    	for (List<Literal> aBody : clauseBodies) {
            boolean result = proveExample(theILPtask, target, aBody, ex, bindings);
            if (!result) return false;
        }
        return true;
    }

	// NOTE: bindings is passed in here to save memory-cell creation, not to constrain the unification.
	boolean proveExample(LearnOneClause theILPtask, Literal target, List<Literal> clauseBody, Literal ex, BindingList bindings) throws SearchInterrupted {
		if (bindings != null && bindings.theta.size() > 0) { bindings.theta.clear(); } // Revert to the empty binding list.
		bindings = ((LearnOneClause) task).unifier.unify(target, ex, bindings);		
		if (bindings == null) { return false; }
		List<Literal> query = bindings.applyTheta(clauseBody);
		return theILPtask.prove(query);
	}
	
	// Recursively climb to the root collecting all the literals.  Remember that the root holds the HEAD literal, and hence shouldn't be collected here.
	List<Literal> getClauseBody() {
		return getClauseBody(false);
	}
	private List<Literal> getClauseBody(boolean stopAtCurrentStartingNode) {
		List<Literal> result;
		SingleClauseNode parent = getParentNode();
		boolean        stopHere = (stopAtCurrentStartingNode && this == ((LearnOneClause) task).currentStartingNode);
		if (!stopHere && parent != null) { 
			result = parent.getClauseBody(stopAtCurrentStartingNode);
			result.add(literalAdded); // Want to add to the END so the clause's literals are in the proper order.
		} else { 
			result = new ArrayList<>(8);  // This makes sure a new list is being created.
		}
		return result;
	}
	List<Literal> getClauseBodyReversed() {
		List<Literal> result;
		SingleClauseNode parent = getParentNode();
		
		if (parent != null) { result = parent.getClauseBodyReversed();
							  result.add(0, literalAdded); }    // Want to add to the FRONT so the clause's literals are in reversed order.
		else                { result = new ArrayList<>(8); } // This makes sure a new list is being created.
		return result;
	}

	Literal getClauseHead() {
		SingleClauseNode parent = getParentNode();
		
		if (parent != null) { return parent.getClauseHead(); }
		return literalAdded;
	}
	
	public Clause getClause() { // There are two climbs of the search tree, but that isn't a big deal since they are shallow.
		return getClause(false);
	}
	private Clause getClause(boolean onlyGetLocalAddition) { // If onlyGetLocalAddition, stop at gettingClauseBody at current starting node.
		List<Literal> headAsPosLiteralList = new ArrayList<>(8);
		headAsPosLiteralList.add(getClauseHead());
		return ((LearnOneClause)task).stringHandler.getClause(headAsPosLiteralList, getClauseBody(onlyGetLocalAddition), extraString);
	}
	
	public Clause getLocallyAddedClause() {
		return getClause(true);
	}
	
	int bodyLength() {
		if (getParentNode() != null) { return 1 + getParentNode().bodyLength(); }
		return 0; // The root is 'true' and we don't count that literal.
	}
	
	double getCost() { // If predicates have costs, sum the costs. Otherwise all predicates 'cost' 1, so we can return length.
		LearnOneClause theTask = (LearnOneClause) task;
		if (theTask.stringHandler.getPredicatesHaveCosts()) {
			double total = 0.0;
			for (Literal lit : getClauseBody()) {  // TODO: use recursion instead of getting the clause body?
				total += lit.predicateName.getCost(lit.numberArgs());
			}
			return total;
		}
		return bodyLength();
	}

	// When the last literal is "determinate," it might be useful as a 'bridging' predicate.  This is used to give some "bonus points" in scoring this node.
	boolean endsWithBridgerLiteral() {
		return (literalAdded != null && literalAdded.isaBridgerLiteral());
	}

	// For the given literal, collect all other instances of this predicate in the current clause.
	// Don't worry about matching (for now), other than confirming the number of args is the same.
	List<Literal> collectAllVariants(Literal newPredicate) {
		List<Literal> result = null;
		
		SingleClauseNode parent = getParentNode();
		if (parent != null) { result = parent.collectAllVariants(newPredicate); }
		
		if (newPredicate.predicateName == literalAdded.predicateName  &&
		    newPredicate.numberArgs()  == literalAdded.numberArgs()) {
			if (result == null) { result = new ArrayList<>(1); } // Create when needed.
			result.add(literalAdded);
		}
		return result;
	}

	boolean thisTermAppearsOnlyOnceInClause(Term termToCheck) { // TODO maybe should generalize to thisTermAppearsAtMostNtimeInClause (and maybe also write a "atLeastN" version).
		return help_thisTermAppearsOnlyOnceInClause(termToCheck, 0);
	}
	private boolean help_thisTermAppearsOnlyOnceInClause(Term termToCheck, int countSoFar) {
		if (literalAdded.getArguments() != null) for (Term term : literalAdded.getArguments()) { 
			if (term == termToCheck) {	countSoFar++; }
			if (countSoFar > 1) { return false; } // Return false once count EXCEEDS 1.
		}
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return parent.help_thisTermAppearsOnlyOnceInClause(termToCheck, countSoFar); }
		return (countSoFar == 1); // If at root, see if count=1.
	}

	List<Term> termsOfThisTypePresentInChild(Type type) {
		List<Term> result = null;
		SingleClauseNode parent = getParentNode();
		
		if (parent != null) { result = parent.termsOfThisTypePresentInChild(type); }
		if (typesPresent != null) {
			List<Term> terms = getAllTypesPresent(type);
			if (terms != null) { 
				if (result == null) { result = new ArrayList<>(4); }
				result.addAll(terms);
			} 
		}
		return result;
	}
	
	// Find all terms added by this node that are of this type.
	// Handles hierarchical types.  If collectBelowType=true, then ok if the item is BELOW 'type' in the ISA hierarchy.
	// Eg, if type=animal and some term of type=dog is present, then return that term. (However, do NOT go the other way in the ISA hier.)
	// Otherwise, it is ok of the item is ABOVE 'type' in the ISA hierarchy.
	private List<Term> getAllTypesPresent(Type type) {
		List<Term> allTerms = null;
		
		LearnOneClause theTask = (LearnOneClause) task;
		for (Type tp : typesPresent) if (theTask.stringHandler.isaHandler.isa(tp, type)) {
			List<Term> terms = typesMap.get(tp);
			if (terms != null) {
				if (allTerms == null) { allTerms = new ArrayList<>(4); }
				allTerms.addAll(terms);
			}
		}
		return allTerms;
	}

	// Count how many times this predicate has occurred in this clause.
	int countPredicateOccurrences(PredicateName pName, int arity) {
		if (literalAdded.predicateName == pName && literalAdded.numberArgs() == arity) { return predicateOccurrences; } // Store CUMMULATIVE counts at nodes (or could always count upwards and save an 'int' in the SingleClauseNode's).
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return parent.countPredicateOccurrences(pName, arity); }
		return 0;
	}
	
	int countPredicateOccurrencesGivenInputArgs(PredicateName pName, int arity, List<Term> constantArgs) {
 		if (literalAdded.predicateName == pName && literalAdded.numberArgs() == arity && sameConstantArguments(arity, constantArgs)) { return predicateOccurrencesPerFixedVars; } // Store CUMMULATIVE counts at nodes (or could always count upwards and save an 'int' in the SingleClauseNode's).
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return parent.countPredicateOccurrencesGivenInputArgs(pName, arity, constantArgs); }
		return 0;
	}
	
	// See if this node has these constant arguments.  When this is called, we know that predicateName/arity have been matched. 
	private boolean sameConstantArguments(int arity, List<Term> constantArgs) {
		// Utils.println("sameConstantArguments: " + literalAdded + " vs.  constantArgs=" + constantArgs);
		List<Term> arguments = literalAdded.getArguments();
		for (int i =0; i < arity; i++) { // See if we get exact matches wherever the constantArgs do not equal null.
			if (constantArgs.get(i) != null && constantArgs.get(i) != arguments.get(i)) { return false; }
		}
 		return true;
	}
	
	Literal getTarget() {
		if (getParentNode() != null) { return getParentNode().getTarget(); }
		//if (!(this instanceof SingleClauseRootNode)) { Utils.error(); }
		return ((SingleClauseRootNode) this).target;
	}
	
	private double wgtedCountOfPosExamplesCovered(List<Example> posExamples) throws SearchInterrupted {
		LearnOneClause   theILPtask = (LearnOneClause) task;
		SingleClauseNode parent     = getParentNode();
		Literal          target     = getTarget();
		List<Literal>    clauseBody = getClauseBody();  // To save space in OPEN, compute this when needed.
		double           total      = 0.0;

		for (Example posEx : posExamples) if (parent == null || !parent.posExampleAlreadyExcluded(posEx)) { 
			if (proveExample(theILPtask, target, clauseBody, posEx, theILPtask.bindings)) { total += posEx.getWeightOnExample(); }
		}
		return total;
	}
	
	private double wgtedCountOfNegExamplesCovered(List<Example> negExamples) throws SearchInterrupted {
		LearnOneClause   theILPtask = (LearnOneClause) task;
		SingleClauseNode parent     = getParentNode();
		Literal          target     = getTarget();
		List<Literal>    clauseBody = getClauseBody();  // To save space in OPEN, compute this when needed.
		double           total      = 0.0;
		
		for (Example negEx : negExamples) if (parent == null || !parent.negExampleAlreadyExcluded(negEx)) { 
			if (proveExample(theILPtask, target, clauseBody, negEx, theILPtask.bindings)) { total += negEx.getWeightOnExample(); }
		}
		return total;
	}

	int countOfSingletonVars(List<Variable> allVars) {
		List<Variable> singletons =  collectSingletonVars(allVars); // Wasted some space, but better than maintaining two minor variants of the same code. 
		
		if (singletons == null) { return 0; }
		return singletons.size();
	}

	// This should be a non-negative number (e.g., it will be subtracted elsewhere).
	// Give a discount on reusing a literal.  Currently the discount is hard-wired to reduce the cost
	// of the 2nd and subsequent uses by 10%,
	double discountForRepeatedLiterals(Set<PredicateName> pNames) {
		double localDiscount = 0.0;
		if (literalAdded != null) {
			PredicateName pName = literalAdded.predicateName;
			if (pNames.contains(literalAdded.predicateName)) { localDiscount += 0.1 * pName.getCost(literalAdded.numberArgs()); }
			else { pNames.add(literalAdded.predicateName); }
		}
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return localDiscount + parent.discountForRepeatedLiterals(pNames); }
		return localDiscount;
	}		
	
	private List<Variable> collectSingletonVars(List<Variable> allVars) {
		if (allVars == null) { return null; }
		List<Variable> singletons = null;
				
		for (Variable var : allVars) {
			int copiesOfVar = 0;
			for (Variable var2 : allVars) if (var == var2) {
				copiesOfVar++;
				if (copiesOfVar > 1) { break; }
			}
			if (copiesOfVar == 1) { 
				if (singletons == null) { singletons = new ArrayList<>(4); }
				singletons.add(var);
			}
			if (copiesOfVar <  1) { Utils.error("Bug in countOfSingletonVars! " + allVars + "  " + this); }
		}
		return singletons;
	}
	
	int countOfUniqueVars(List<Variable> allVars) {
		List<Variable> uniques =  collectUniqueVars(allVars); // Wasted some space, but better than maintaining two minor variants of the same code.
		if (uniques == null) { return 0; }
		return uniques.size();
		
	}
	private List<Variable> collectUniqueVars(List<Variable> allVars) { // TODO - could simply return a set ...
		if (allVars == null) { return null; }
		List<Variable> seenVars = new ArrayList<>(allVars.size());
		
		for (Variable var : allVars) {
			if (!seenVars.contains(var)) { seenVars.add(var); }
		}
		return seenVars;
	}
	
	int countOfUniqueConstants(List<Constant> allConstants) {
		List<Constant> uniques =  collectUniqueConstants(allConstants); // Wasted some space, but better than maintaining two minor variants of the same code. 
		
		if (uniques == null) { return 0; }
		return uniques.size();
		
	}
	private List<Constant> collectUniqueConstants(List<Constant> allConstants) {
		if (allConstants == null) { return null; }
		List<Constant> seenConstants = new ArrayList<>(allConstants.size());
		
		for (Constant var : allConstants) {
			if (!seenConstants.contains(var)) { seenConstants.add(var); }
		}
		return seenConstants;
	}
	
	public List<Variable> collectAllVariables() {
		return collectAllVariables(null);
	}
	private List<Variable> collectAllVariables(List<Variable> listOfVars) {
		List<Term> args = literalAdded.getArguments();		
		
		if (args != null && args.size() > 0) {
			for (Term term : args) if (term instanceof Variable) {
				if (listOfVars == null) { listOfVars = new ArrayList<>(1); }
				listOfVars.add((Variable) term);
			}
		}
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return parent.collectAllVariables(listOfVars); }
		return listOfVars;
	}
	
	List<Constant> collectAllConstants() {
		return collectAllConstants(null);
	}
	private List<Constant> collectAllConstants(List<Constant> listOfConstants) {
		List<Term> args = literalAdded.getArguments();		
		
		if (args != null && args.size() > 0) {
			for (Term term : args) if (term instanceof Constant) {
				if (listOfConstants == null) { listOfConstants = new ArrayList<>(1); }
				listOfConstants.add((Constant) term);
			}
		}
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return parent.collectAllConstants(listOfConstants); }
		return listOfConstants;
	}
	
	boolean acceptableCoverageOnPosSeeds() throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;
		double posSeedWgtedCount;
	
		if (theILPtask.totalWeightOnPosSeeds > 0.0 && theILPtask.seedPosExamples != null) {
			posSeedWgtedCount = wgtedCountOfPosExamplesCovered(theILPtask.seedPosExamples);
			return !(posSeedWgtedCount < theILPtask.clausesMustCoverFractPosSeeds * theILPtask.totalWeightOnPosSeeds);
		} else { // Comment this out if we really want this case.
			Utils.waitHere("Why totalWeightOnPosSeeds = " + theILPtask.totalWeightOnPosSeeds + " and |theILPtask.seedPosExamples| = " + Utils.comma(theILPtask.seedPosExamples));
		}
		return true;
	}
	
	boolean acceptableCoverageOnNegSeeds() throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;
		double negSeedWgtedCount;

		if (theILPtask.totalWeightOnNegSeeds > 0 && theILPtask.seedNegExamples != null) {
			negSeedWgtedCount = wgtedCountOfNegExamplesCovered(theILPtask.seedNegExamples);

			return !(negSeedWgtedCount >= theILPtask.clausesMustNotCoverFractNegSeeds * theILPtask.totalWeightOnNegSeeds);
		}
		return true;
	}

	// See if this clause matches at least the minimal required positive examples.
	boolean acceptableCoverageOnPosExamples() throws SearchInterrupted {
		LearnOneClause   theILPtask = (LearnOneClause) task;
		Literal          target     = getTarget();
		List<Literal>    clauseBody = getClauseBody();  // To save space in OPEN, compute this when needed.
		SingleClauseNode parent     = getParentNode();

		int    counter              = 0;
		double minCount             = theILPtask.getMinPosCoverage();
		for (Example posEx : theILPtask.getPosExamples()) if (parent == null || !parent.posExampleAlreadyExcluded(posEx)) { // Don't check HERE (i.e., start at parent) since we don't want to call computCoverage).
			if (proveExample(theILPtask, target, clauseBody, posEx, theILPtask.bindings)) { 
				counter += posEx.getWeightOnExample();
			}
			if (counter >= minCount) { return true; }
		}
		return false;
	}
	
	// Note that here we get missed examples, INCLUDING THOSE THAT FAILED AT EARLIER NODES.
	void getUptoKmissedPositiveExamples() throws SearchInterrupted {
		// TODO(@hayesall): Can this method be dropped?
		Set<Example>     results    = null;
		LearnOneClause   theILPtask = (LearnOneClause) task;
		Literal          target     = getTarget();
		List<Literal>    clauseBody = getClauseBody();  
		
		int counter = 0;
		List<List<Literal>> optimizedClauseBodies = getOptimizedClauseBodies(theILPtask, target, clauseBody);
		if (theILPtask.getPosExamples() != null) for (Example posEx : theILPtask.getPosExamples()) {
			// proveExample() clears the bindings, so no need to do so here.
			if (!proveExampleBodies(theILPtask, target, optimizedClauseBodies, posEx, theILPtask.bindings)) {
				if (results == null) { results = new HashSet<>(4); }
				results.add(posEx);
				counter++;
				if (counter >= 5) { return; }
			}
		}
	}
	
	void getUptoKcoveredNegativeExamples() throws SearchInterrupted {
		Set<Example>     results    = null;
		LearnOneClause   theILPtask = (LearnOneClause) task;
		Literal          target     = getTarget();
		List<Literal>    clauseBody = getClauseBody();  
		
		int counter = 0;
		List<List<Literal>> optimizedClauseBodies = getOptimizedClauseBodies(theILPtask, target, clauseBody);
		if (theILPtask.getNegExamples() != null) for (Example negEx : theILPtask.getNegExamples()) {
			// proveExample() clears the bindings, so no need to do so here.
			if (proveExampleBodies(theILPtask, target, optimizedClauseBodies, negEx, theILPtask.bindings)) {
				if (results == null) { results = new HashSet<>(4); }
				results.add(negEx);
				counter++;
				if (counter >= 5) { return; }
			}
		}
	}
		
	// TODO - should we store these results?
	private List<List<Literal>> getOptimizedClauseBodies(LearnOneClause theILPtask, Literal target, List<Literal> clauseBody) {
		if (Utils.getSizeSafely(clauseBody) < 1) { return null; }
		List<List<Literal>> optimizedClauseBodies;
        try {
			optimizedClauseBodies = theILPtask.getOptimizedClauseBodies(target, clauseBody);
		} catch (Throwable e) {
			if (theILPtask.stringHandler.exceptionCount++ < HandleFOPCstrings.exceptionCountMax) { Utils.warning("% Exception thrown: Problem optimizing target = " + target + "\n with body = " + clauseBody); }
			optimizedClauseBodies = Collections.singletonList(clauseBody);
        }
        return optimizedClauseBodies;
	}
	
	// Only prove those examples covered by the parent node (but don't want to use too much space).
	public void computeCoverage() throws SearchInterrupted {
		LearnOneClause   theILPtask = (LearnOneClause) task;
		HornClauseProver prover     = theILPtask.getProver();
		Literal          target     = getTarget();
		List<Literal>    clauseBody = getClauseBody();  // To save space in OPEN, compute this when needed.
		SingleClauseNode parent     = getParentNode();
		boolean          firstTime            = false;
		boolean          tookTooLong          = false;
		long             totalResolutions     = 0;
		boolean          stopWhenUnacceptable = theILPtask.stopWhenUnacceptableCoverage; // Don't continue to prove examples when impossible to meet the minPosCoverage and minPrecision specifications.

		List<List<Literal>> optimizedClauseBodies = null;

		// To save time, if posCoverage is not going to reach theILPtask.minPosCoverage stop.
		if (getPosCoverage() < 0.0) {
			extraString = null; // Reset this whenever the coverage changes.
			double maxPossiblePosCoverage = 0.0;
			if (stopWhenUnacceptable) for (Example posEx : theILPtask.getPosExamples()) if (parent == null || !parent.posExampleAlreadyExcluded(posEx)) { // Don't look at THIS node or we'll have an infinite loop.
				maxPossiblePosCoverage += posEx.getWeightOnExample(); // See how much is possible
			}
			setPosCoverage(0.0);
			firstTime = true;

			if (theILPtask.getPosExamples() != null) {
				for (Example posEx : theILPtask.getPosExamples()) {
					if (parent == null || !parent.posExampleAlreadyExcluded(posEx)) { // Don't look at THIS node or we'll have an infinite loop.
						if (optimizedClauseBodies == null) { optimizedClauseBodies = getOptimizedClauseBodies(theILPtask, target, clauseBody); }
						prover.setNodesCreated(0); // This counter gets reset when performSearch() is called, but that might not happen (eg, if the body is empty).
						// proveExample() clears the bindings, so no need to do so here.
						if (proveExampleBodies(theILPtask, target, optimizedClauseBodies, posEx, theILPtask.bindings)) {
							setPosCoverage(getPosCoverage() + posEx.getWeightOnExample());
						}
						else {
							maxPossiblePosCoverage -= posEx.getWeightOnExample(); // Lost out on this.
						if (posExamplesThatFailedHere == null) { posExamplesThatFailedHere = new HashSet<>(); }
						posExamplesThatFailedHere.add(posEx);
						if (theILPtask.regressionTask && !theILPtask.oneClassTask) {
							if (cachedLocalRegressionInfoHolder == null) {  // Don't create until needed.
								cachedLocalRegressionInfoHolder = new LocalRegressionInfoHolder();
							}
							if (cachedLocalRegressionInfoHolder.cachedFalseStats == null) {
								cachedLocalRegressionInfoHolder.cachedFalseStats = theILPtask.getNewRegressionHolderForTask();
							}				   		

							if (!theILPtask.mlnRegressionTask) { // Example counting for MLN tasks later
								cachedLocalRegressionInfoHolder.getFalseStats().addFailureExample(posEx, 1, posEx.getWeightOnExample());
							}

						}
						} 
						totalResolutions += prover.getNodesCreated();
						if (totalResolutions > theILPtask.maxResolutionsPerClauseEval) {
							tookTooLong = true;
							extraString = "Coverage only partially computed- took too long to compute.";
							break; 
						}
						if (stopWhenUnacceptable && maxPossiblePosCoverage < theILPtask.getMinPosCoverage()) { 
							if (parent != null) { parent.addToDontConsiderThisLiteral(theILPtask, literalAdded.predicateName, literalAdded.getArguments(), typesOfNewTerms); }
							setPosCoverage(0.0);
							negCoverage = 0.0; 
							extraString = "Coverage only partially computed. (maxPossiblePosCoverage = " + Utils.truncate(maxPossiblePosCoverage, 3)
									+ " and MinPosCoverage = " + Utils.truncate(theILPtask.getMinPosCoverage(), 3) + ")";
							return; // No need continuing.
						}				
					}
				}
				if (theILPtask.regressionTask &&
						theILPtask.mlnRegressionTask &&
						posExamplesThatFailedHere != null) {
					int fraction = (posExamplesThatFailedHere.size()/(theILPtask.maxExamplesToSampleForScoring*2)) + 1;
					double prob = 1.0/(double)fraction;
					if (!theILPtask.sampleForScoring) {fraction =1;prob=1;}
					for (Example posEx : posExamplesThatFailedHere) {
						if (Utils.random() < prob) {
							long num = 1;
							if (parent != null && parent != getRootNode()) { 
								num = parent.getNumberOfGroundingsForRegressionEx(posEx);
							}
							if (num == 0) {
								Utils.waitHere("Number of groundings = 0 for " + posEx + " with " + parent.getClause());
							}
							((RegressionExample) posEx).getOutputValue();
							cachedLocalRegressionInfoHolder.getFalseStats().addFailureExample(posEx, num, fraction*posEx.getWeightOnExample());
						}
					} 
				}
			}
		}

		// NOTE: Must not compare negCoverage to theILPtask.minPrecision since the task of ILP is to add literals until precision is acceptable.
		if (negCoverage < 0.0 && !tookTooLong) {
			extraString = null; // Reset this whenever the coverage changes.
			negCoverage = 0.0;
			firstTime = true;
			prover.setNodesCreated(0); // This counter gets reset when performSearch() is called, but that might not happen (e.g., if the body is empty).
			if (theILPtask.getNegExamples() != null) for (Example negEx : theILPtask.getNegExamples()) if (parent == null || !parent.negExampleAlreadyExcluded(negEx))  {
				if (optimizedClauseBodies == null) { optimizedClauseBodies = getOptimizedClauseBodies(theILPtask, target, clauseBody); }
				// proveExample() clears the bindings, so no need to do so here.
				if (proveExampleBodies(theILPtask, target, optimizedClauseBodies, negEx, theILPtask.bindings)) {
					negCoverage += negEx.getWeightOnExample();
				}
				else { 
					if (negExamplesThatFailedHere == null) { negExamplesThatFailedHere = new HashSet<>(); }
					negExamplesThatFailedHere.add(negEx);
				}
				totalResolutions += prover.getNodesCreated();
				if (totalResolutions > theILPtask.maxResolutionsPerClauseEval) {
					tookTooLong = true;
					extraString = "Coverage only partially computed - took too long to compute.";
					break; 
				}
			}
		}

		if (tookTooLong) { // Would be nice to report more info regarding when the time-out occurred, but don't bother with extra counters.
			setPosCoverage(0.0); // When we abandon, we simply assume a clause is never true and never keep in the Gleaner.
			negCoverage = 0.0;
			timedOut    = true;
			extraString = "Coverage only partially computed- took too long to compute.";
		}
		// else if (firstTime && totalResolutions > 5000) { Utils.println(" total resolutions = " + totalResolutions + " for " + this); }
		// If this is the first time the coverage of this rule has been computed,
		// see if there is any need to continue searching (ie, if a rule covers ALL pos and NO neg examples, then can stop).  Might want to override this, say if collecting a range of good rules ala' Gleaner.
		if (firstTime && theILPtask.stopIfPerfectClauseFound && 
				!Utils.diffDoubles(getPosCoverage(), theILPtask.totalPosWeight) && negCoverage <= 0.0
				&& acceptableClauseExtraFilter(theILPtask)) { 
			// Be careful that setting this doesn't mess up what is being kept as the best node.  TODO - make sure that if the score of a perfect clause is insufficient (eg, m-estimate of accuracy is too low), this is caught early on.
			theILPtask.continueTheSearch = false;
		}
	}
	public boolean posExampleAlreadyExcluded(Example example) throws SearchInterrupted {
		if (getPosCoverage() < 0.0) { computeCoverage(); }
		if (posExamplesThatFailedHere != null && posExamplesThatFailedHere.contains(example)) { return true; }
		SingleClauseNode parent = getParentNode();
		if (parent == null) { return false; }
		return parent.posExampleAlreadyExcluded(example);
	}
	
	// Used to get examples on the false branch for a node
	private List<Example> posExampleFailedAtNode()  throws SearchInterrupted {
		if (getPosCoverage() < 0.0) { computeCoverage(); }
		if (this == ((LearnOneClause)task).currentStartingNode) {
				return new ArrayList<>();
		}
		
		List<Example> failedExamples;
		if (posExamplesThatFailedHere != null) {
			failedExamples = new ArrayList<>(posExamplesThatFailedHere);
		} else {
			failedExamples = new ArrayList<>();
		}
		
		SingleClauseNode parent = getParentNode();
		if (parent == null) { return failedExamples; }
		failedExamples.addAll(parent.posExampleFailedAtNode());
		return failedExamples;
	}
	
	private boolean negExampleAlreadyExcluded(Literal example) throws SearchInterrupted {
		if (negCoverage < 0.0) { computeCoverage(); }
		if (negExamplesThatFailedHere != null && negExamplesThatFailedHere.contains(example)) { return true; }
		SingleClauseNode parent = getParentNode();
		if (parent == null) { return false; }
		return parent.negExampleAlreadyExcluded(example);
	}
	
	public double precision () throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;

		if (getPosCoverage() < 0.0) { computeCoverage(); }
		// Assume this clause covers the m-estimated NEG examples but NOT the m-estimated POS examples.
		return getPosCoverage() / (getPosCoverage() + negCoverage + theILPtask.getMEstimateNeg());
	}
	
	// Compute m-estimated precision if all negs could be removed. (Note maxRecall is recall.)
	double maxPrecision() throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;

		if (getPosCoverage() < 0.0) { computeCoverage(); }	
		// Assume this clause covers the m-estimated NEG examples but NOT the m-estimated POS examples.
		return getPosCoverage() / (getPosCoverage() + theILPtask.getMEstimateNeg());
	}
	
	public double recall() throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;

		if (getPosCoverage() < 0.0) { computeCoverage(); }
		// Assume this clause does NOT cover the m-estimated POS examples.
		return getPosCoverage() / (theILPtask.totalPosWeight + theILPtask.getMEstimatePos());
	}

	double F(double beta) throws SearchInterrupted { // See http://en.wikipedia.org/wiki/Information_retrieval#F-measure
		if (beta < 0) { Utils.error("Beta in F(Beta) must be non-negative: " + Utils.truncate(beta, 3) + " was provided."); }
		double precision = precision();		
		double recall    = recall();		
		
		double numer = (1 + beta) * precision * recall;
		double denom = beta * precision + recall;
		if (denom < Double.MIN_VALUE) { return 0; }
		return numer / denom;
	}
	
	boolean canImprove(LearnOneClause thisTask) throws SearchInterrupted {  // Is it possible to improve this clause by adding another literal.
		if (getPosCoverage() < 0.0) { computeCoverage(); }
		LearnOneClause theILPtask = (LearnOneClause) task;
		
		// Note that minPrecision is the minimum required to be the "goal" node (i.e., if the best node doesn't score at least this much, the search fails).
		// So don't discard node just because they don't score that well.  Instead, look for the BEST possible score, and only
		// if that is too low can a node be ignored, since it can't be improved enough.
		// Also note that a node that took too long to evaluate will have posCoverage = negCoverage = 0 and this method will say it cannot be improved.
		if (getPosCoverage() <  theILPtask.getMinPosCoverage()) {
			return false;  // to do: also check if if it is possible to get minAcc (due to minEstimate)
		}
		
		if (thisTask.regressionTask) { return true; } // All tests BELOW here do no apply to categorization. 
		
		double bestPrecisionPossible = maxPrecision();
		if (bestPrecisionPossible <  theILPtask.minPrecision) {
			return false;
		}
		if (!acceptableClauseExtraFilter(thisTask)) { return true; } // If a clause doesn't meet the 'acceptability' test, it can presumably be improved (e.g., might need to extend it, even if precision is 100%).
		return !(negCoverage <= theILPtask.stopExpansionWhenAtThisNegCoverage);  // If no negs covered, adding literals wont help.
		// Still some neg's that could be eliminated.
	}
	
	// This allows the user to say when a clause is acceptable for reasons other than recall, precision, or length.
	// E.g., in some work involving plan recognition, a learned rule must be a complete plan (i.e., reaches a final state),
	// rather than simply doing a good job of differentiating good from bad examples.
	// Also, if requireThatAllRequiredHeadArgsAppearInBody=true, see if this requirement is met.
	boolean acceptableClauseExtraFilter(LearnOneClause thisTask) {
		if (thisTask.requireThatAllRequiredHeadArgsAppearInBody && !allRequiredHeadArgsAppearInBody(thisTask)) { return false; }
		return allTheseArgsAppearinBody(getRequiredVariablesInBody());
		// TODO need a better design here.
	}
	
	private Collection<Variable> getRequiredVariablesInBody() {
		if (getParentNode() != null) { return getParentNode().getRequiredVariablesInBody(); }
		return ((SingleClauseRootNode) this).requiredBodyVariablesInTarget;
	}
	
	public SingleClauseRootNode getRootNode() {
		if (this instanceof SingleClauseRootNode) { return (SingleClauseRootNode) this; }
		if (getParentNode() != null) { return getParentNode().getRootNode(); }
		Utils.error("Could not reach the root node from: " + this);
		return null;
	}
	
	List<Term> getVariablesInTarget() {
		if (getParentNode() != null) { return getParentNode().getVariablesInTarget(); }
		return ((SingleClauseRootNode) this).variablesInTarget;
	}
	
	private boolean allRequiredHeadArgsAppearInBody(LearnOneClause thisTask) {
		SingleClauseRootNode root = getRootNode();
		assert root.targetArgSpecs != null;
		for (ArgSpec argSpec : root.targetArgSpecs) if (argSpec.arg instanceof Variable) {
			if ((thisTask.allTargetVariablesMustBeInHead || argSpec.typeSpec.mustBeBound()) 
					&& !variableAppearsInThisClause((Variable) argSpec.arg)) {
					return false;
			}
		}	
		return true;
	}
	
	private boolean allTheseArgsAppearinBody(Collection<Variable> requiredVars) {
		if (Utils.getSizeSafely(requiredVars) < 1) { return true; }
		for (Variable var : requiredVars) {
			if (!variableAppearsInThisClause(var)) {
				return false; 
			}
		}
		return true;
	}
	
	private boolean variableAppearsInThisClause(Variable var) {
		if (getParentNode() == null) { return false; } // We do not want to check the FIRST literal, since that is the head.
		if (literalAdded.containsThisVariable(var)) { return true; }
		
		return getParentNode().variableAppearsInThisClause(var);
	}

	// If this literal is already in the clause or in the "dontReconsider" list, then it should be skipped over.
	boolean dontConsiderThisLiteral(boolean discardDuplicateLiterals, Literal candidate, Map<Term, Type> newTermsInLiteral) {
		if (discardDuplicateLiterals && literalAdded != null && literalAdded.equals(candidate)) {
			return true; 
		}
		if (dontReconsider != null) {
			for (AnnotatedLiteral badLit : dontReconsider) if (badLit.equals(candidate, newTermsInLiteral)) {
				return true;
			}
		}
		SingleClauseNode parent = getParentNode();
		if (parent == null) { return false; }
		return parent.dontConsiderThisLiteral(discardDuplicateLiterals, candidate, newTermsInLiteral);
	}
	
	void addToDontConsiderThisLiteral(LearnOneClause thisTask, PredicateName predName, List<Term> args, Map<Term, Type> thisTypesOfNewTerms) {
		if (dontReconsider == null) { dontReconsider = new ArrayList<>(1); }
		Map<Term,Type> typesOfNewTermsInTheseArgs = null;
		if (thisTypesOfNewTerms != null) {
			for (Term term : args) { // Only keep those new terms (if any) that are in this 'rejected' literal.  (Could see if ALL are there, and if so, no need to copy, but seems better to simply always copy.)
				if (thisTypesOfNewTerms.containsKey(term)) {
					if (typesOfNewTermsInTheseArgs == null) { typesOfNewTermsInTheseArgs = new HashMap<>(4); }
					typesOfNewTermsInTheseArgs.put(term, thisTypesOfNewTerms.get(term));
				}
			}
		}
		dontReconsider.add(new AnnotatedLiteral(thisTask.stringHandler, predName, args, typesOfNewTermsInTheseArgs));
	}

	// The depth of an argument measures its shortest path, in terms of the number of new variables, to the head.
	Integer getDepthOfArgument(Term item) {
		if (depthOfArgs == null) { Utils.error("Should not have depthOfArgs=null!"); }
		Integer integer = depthOfArgs.get(item);
		
		if (integer != null) { return integer; }
		SingleClauseNode parent = getParentNode();
		if (parent == null)  { return null; }
		return parent.getDepthOfArgument(item);
	}

	@Override
	public String toString() {
		LearnOneClause theILPtask = (LearnOneClause) task;
		StringBuilder result = new StringBuilder();
		boolean firstTime = true;
		List<Literal> clauseBody = getClauseBody();
		Literal       clauseHead = getClauseHead();
		
		if (renameAllVariablesWheneverPrinting) {
			List<Literal> posLits = new ArrayList<>(1);
			posLits.add(clauseHead);
			Clause c = theILPtask.stringHandler.getClause(posLits, clauseBody, extraString);
			c = (Clause) theILPtask.stringHandler.renameAllVariables(c);
			clauseBody = c.negLiterals;
			clauseHead = c.posLiterals.get(0);
		}

		if (Utils.getSizeSafely(clauseBody) <= 0) { 
			result.append(clauseHead);
		}
		else if (theILPtask.stringHandler.usingStdLogicNotation()) {
			for (Literal literal : clauseBody) { 
				if (firstTime) { firstTime = false; } else { result.append(" ^ "); }
				result.append(literal);  // Note that in "rule" form, we want unnegated literals.
			}
			result.append(" => ").append(clauseHead);
		}
		else {
			result.append(clauseHead).append(" :- ");
			for (Literal literal : clauseBody) { 
				if (firstTime) { firstTime = false; } else { result.append(", "); }
				result.append(literal);  // Note that in "rule" form, we want unnegated literals.
			}
		}
		
		if (getPosCoverage() < 0 && negCoverage < 0) return result.toString(); // This node is only a candidate and has not yet been scored.

		return result + ".  [covers " 
		                    + Utils.truncate(getPosCoverage()) + "/" + Utils.truncate(theILPtask.totalPosWeight) + " pos, " 
		                    + Utils.truncate(negCoverage) + "/" + Utils.truncate(theILPtask.totalNegWeight) + " neg]" + (extraString == null ? "" : extraString);
	}
 
    /////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    
    // Code for regression trees.  Assumes LEAVES HOLD CONSTANTS (i.e., the group's mean).
    // and that we care to score examples not covered by the clause the same as those covered
    // (this makes sense when learning a TREE; if just learning rules, can set theILPtask.multiplerOnFailedRegressionExamples = 0 or a small positive number).

	double oneClassScore() throws SearchInterrupted {
    	LearnOneClause loc = ((LearnOneClause)this.task);
    	List<Example> failedEgs = posExampleFailedAtNode();
    	 return loc.occScorer.calculateKernelScore(
    				PairWiseExampleScore.removeFromCopy(loc.getPosExamples(), failedEgs),
    				failedEgs, depth);
    }
    

	double regressionFitForMLNs() {
		LearnOneClause  theILPtask = (LearnOneClause) task;

		if (this.timedOut) {
			Utils.println("Giving INF score for " + this.getClause() +
					" as it timed out. The examples on true and false branch are incorrect.");
			return Double.POSITIVE_INFINITY;  
		}
		RegressionInfoHolder holder = getRegressionInfoHolder();
		if (holder.totalExampleWeightAtSuccess() < theILPtask.getMinPosCoverage() ||
			holder.totalExampleWeightAtFailure() < theILPtask.getMinPosCoverage()) {
			return Double.POSITIVE_INFINITY;  // Bad clauses get posCoverage=0 and we don't want to keep such clauses.  Remember we NEGATE the score, so a high score here is bad.
		}
		double result = 0;
		if (holder.getTrueStats() != null) { result += getMLNCost(holder.getTrueStats()); } else { Utils.waitHere("Why is true stats null?" + this.literalAdded); }
		if (holder.getFalseStats() != null) { result += getMLNCost(holder.getFalseStats()); } else { Utils.waitHere("Why is false stats null?"+ this.literalAdded); }

		return result;
	}
	
	
	
	private double getMLNCost(BranchStats stats) {
		double result = 0;
		if (stats.getSumOfNumGroundingSquared() > 0) {
			result = stats.getWeightedVariance();
		}
		if (stats.getNumExamples() == 0) {
			if (result != 0) {
				Utils.println(stats.toString());
				Utils.waitHere("Result is not zero but examples are!!");
			}
			return 0;
		}
		
		if (result < 0) {
			if (!(Math.abs(result) < 1e-8)) {
				Utils.waitHere(result + ":" + stats.toString());
			}
			result = 0;
		}
		return result;
	}

	double regressionFit() {
		// This is the expected variance after this node is evaluated (divided by the wgt'ed number of examples).
		LearnOneClause  theILPtask = (LearnOneClause) task;
		if (getRegressionInfoHolder().totalExampleWeightAtSuccess() < theILPtask.getMinPosCoverage() ||
			getRegressionInfoHolder().totalExampleWeightAtFailure() < theILPtask.getMinPosCoverage()) {
			// Bad clauses get posCoverage=0 and we don't want to keep such clauses.  Remember we NEGATE the score, so a high score here is bad.
			return Double.POSITIVE_INFINITY;
		}
		return getRegressionInfoHolder().weightedVarianceAtSuccess() + getRegressionInfoHolder().weightedVarianceAtFailure();
	}

	
	public RegressionInfoHolder getTotalFalseBranchHolder() {
		if (this == ((LearnOneClause) task).currentStartingNode) {
			return null;
		} // For this calculation don't want to go past the current root (but for other cases we do - i.e., when looking for eligible variables to reuse).
		if (getPosCoverage() < 0) { Utils.error("This should not happen."); } // Should only call via regressionFit (or at least after regressionFit is called). 
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return cachedLocalRegressionInfoHolder.getFalseStats().addFailureStats(parent.getTotalFalseBranchHolder()); }
		return cachedLocalRegressionInfoHolder.getFalseStats();
	}

	double meanIfTrue() {
		return getRegressionInfoHolder().meanAtSuccess();
	}
	
	double meanIfFalse() {
		return getRegressionInfoHolder().meanAtFailure();
	}
	double mlnRegressionForTrue() {
		RegressionInfoHolder holder = getRegressionInfoHolder();
		return holder.meanAtSuccess();
	}
	double mlnRegressionForFalse() {
		RegressionInfoHolder holder = getRegressionInfoHolder();
		return holder.meanAtFailure();
	}
	
	SingleClauseNode getStartingNodeForReset() {
		return startingNodeForReset;
	}
	void setStartingNodeForReset(SingleClauseNode startingNodeForReset) {
		this.startingNodeForReset = startingNodeForReset;
	}

	// If TRUE, then this branch will become a LEAF.
	boolean acceptableScoreFalseBranch(double minAcceptableScore) throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;	
		if (theILPtask.regressionTask) {
			double variance;
			if (theILPtask.oneClassTask) {
				variance = getVarianceFalseBranch();
			} else {
				variance = getRegressionInfoHolder().varianceAtFailure() ;
				Utils.println("Comparing variance: " + variance + " to score=" + minAcceptableScore + " #egs=" + getRegressionInfoHolder().totalExampleWeightAtFailure());
			}
			return variance <= minAcceptableScore;
		}

		double precision = precisionOnFailedExamples();
		if (precision       >= minAcceptableScore) { return true; } // Have a sufficiently pure POS set after splitting.
		// Have a sufficiently pure NEG set after splitting.
		return (1 - precision) >= minAcceptableScore;
	}
	// This is a bit cpu-intensive, but unless this is called multiple times, no need to cache it. 
	private double precisionOnFailedExamples() throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;

		if (getPosCoverage() < 0.0) { computeCoverage(); }
		double posCoverageFailed = 0.0;
		double negCoverageFailed = 0.0;
		for (Example posEx : theILPtask.getPosExamples()) if (posExampleAlreadyExcluded(posEx)) { posCoverageFailed += posEx.getWeightOnExample(); }
		for (Example negEx : theILPtask.getNegExamples()) if (negExampleAlreadyExcluded(negEx)) { negCoverageFailed += negEx.getWeightOnExample(); }

		return posCoverageFailed / (posCoverageFailed + negCoverageFailed + theILPtask.getMEstimateNeg());
	}
	
	double getVarianceTrueBranch() throws SearchInterrupted {
		return getVarianceTrueBranch(false);
	}
	double getVarianceTrueBranch(boolean computeMean) throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;
		if (theILPtask.oneClassTask) {
			return theILPtask.occScorer.getVariance(PairWiseExampleScore.removeFromCopy(theILPtask.getPosExamples(), posExampleFailedAtNode()));
		}
		if (theILPtask.regressionTask) {
			RegressionInfoHolder holder = getRegressionInfoHolder();
			if (computeMean && holder.totalExampleWeightAtSuccess() > 0.0) { return  holder.varianceAtSuccess(); }
			return holder.weightedVarianceAtSuccess();
		}
		return -1.0; // If discrete-valued return this to indicate "not relevant."
	}

	
	double getVarianceFalseBranch() throws SearchInterrupted {
		return getVarianceFalseBranch(false);
	}
	double getVarianceFalseBranch(boolean computeMean) throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;
		
		if (theILPtask.oneClassTask) {
			return theILPtask.occScorer.getVariance(this.posExampleFailedAtNode());
		}
		if (theILPtask.regressionTask) {
			RegressionInfoHolder holder = getRegressionInfoHolder();
			if (computeMean && holder.totalExampleWeightAtFailure() > 0.0) { return  holder.varianceAtFailure(); }
			return holder.weightedVarianceAtFailure();
		}
		return -1.0; // If discrete-valued return this to indicate "not relevant."
	}

	boolean acceptableScoreTrueBranch(double acceptableScore) throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;
		if (theILPtask.regressionTask) {
				double variance;
				if (theILPtask.oneClassTask) {
					variance = getVarianceTrueBranch();
				} else {
					variance = getRegressionInfoHolder().varianceAtSuccess() ;
					Utils.println("Comparing variance: " + variance + " to score=" + acceptableScore+ " #egs=" + getRegressionInfoHolder().totalExampleWeightAtSuccess());
				}	
				
				return variance <= acceptableScore;
		}
		
		double precision = precision();
		if (precision       >= acceptableScore) { return true; } // Have a sufficiently pure POS set after splitting.
		return (1 - precision) >= acceptableScore;
	}
	
	private LocalRegressionInfoHolder cachedLocalRegressionInfoHolder  = null; // Waste a little space for non-regression problems, but only one pointer.

	private RegressionInfoHolder getRegressionInfoHolder() {
		if (cachedLocalRegressionInfoHolder == null) { 
			cachedLocalRegressionInfoHolder = new LocalRegressionInfoHolder();
		}

		LearnOneClause theILPtask = (LearnOneClause) task;

		if (cachedLocalRegressionInfoHolder.resultsHolder == null) {
			cachedLocalRegressionInfoHolder.resultsHolder = theILPtask.getNewRegressionHolderForTask();
			if (cachedLocalRegressionInfoHolder.cachedFalseStats == null) {
				cachedLocalRegressionInfoHolder.cachedFalseStats = theILPtask.getNewRegressionHolderForTask();
			}
			try {
				cachedLocalRegressionInfoHolder.resultsHolder.populateExamples((LearnOneClause)task, this);
			} catch (SearchInterrupted e) {
				e.printStackTrace();
			}
		}
		return cachedLocalRegressionInfoHolder.resultsHolder;
	}

	void resetAssumingAllExamplesCovered() {
		LearnOneClause theILPtask = (LearnOneClause) task;
		setPosCoverage(Example.getWeightOfExamples(theILPtask.getPosExamples()));
		negCoverage = Example.getWeightOfExamples(theILPtask.getNegExamples());
		score = Double.NaN;
		if (theILPtask.regressionTask) { resetRegressionNodeInfoHolder(); }
	}
	
	private void resetRegressionNodeInfoHolder() {
		if (cachedLocalRegressionInfoHolder == null) {
			return; 
		}
		cachedLocalRegressionInfoHolder.reset();
	}
	
	int numberOfBridgersInBody(SingleClauseNode nodeAtWhichThisSearchStarted) {
		if (this == nodeAtWhichThisSearchStarted) { return 0; } // Only count bridgers locally in tree-structured runs.
		int total = (endsWithBridgerLiteral() ? 1 : 0);
		if (getParentNode() == null) { return total; }
		return total + getParentNode().numberOfBridgersInBody(nodeAtWhichThisSearchStarted);
	}

    public SingleClauseNode getParentNode() {
        return (SingleClauseNode) super.getParentNode();
    }


	static class LocalRegressionInfoHolder {	// These are used for regression, so lower nodes can be scored quickly (at the cost of another instance variable,. but designed to only 'waste' one pointer when not doing regressiion.

        RegressionInfoHolder resultsHolder;
        // Keep it separate from the results holder that is used for computing mean/variance
        // Maybe not needed but better to be safe.
		RegressionInfoHolder cachedFalseStats;
        
        LocalRegressionInfoHolder() {
        }

        RegressionInfoHolder getFalseStats() {
        	return cachedFalseStats;
        }
        void reset() {
        	cachedFalseStats = null;
            
        }

    }

    // TODO(@hayesall): `cachedBindingLists = new HashMap<>();` is final?
    private final HashMap<Example, Set<BindingList>> cachedBindingLists = new HashMap<>();

	public long getNumberOfGroundingsForRegressionEx(Example eg) {
		initGroundingCalc();
		LearnOneClause learnClause = ((LearnOneClause)task);
		BindingList theta = learnClause.unifier.unify(this.getClauseHead(), eg.extractLiteral());
		long cached_num = ((RegressionRDNExample)eg).lookupCachedGroundings(this);
		if (cached_num >=0) {
			return cached_num;
		}
		cachedBindingLists.remove(eg);
		long num = 0;
		if (getParentNode() != getRootNode() &&
			getParentNode() != null && getParentNode().cachedBindingLists.containsKey(eg)) {
			for (BindingList bl : getParentNode().cachedBindingLists.get(eg)) {
				BindingList bl2 = new BindingList(theta.collectBindingsInList());
				bl2.addBindings(bl);
				num += getNumberOfGroundingsForRegressionEx(eg, bl2, true);
			}
		} else {
			num = getNumberOfGroundingsForRegressionEx(eg, theta, false);
		}
		if (num < 10) {
			// Easy to recompute the bindings.
			cachedBindingLists.remove(eg);
		}
		if (num == 0) {
			Utils.waitHere("Number of groundings = 0 for " + eg + " with " + getClause() + " BL: " + theta + " Lit: " + literalAdded);
		}
		
		if (cachedBindingLists.containsKey(eg)) {
			Set<BindingList> cachedbl = cachedBindingLists.get(eg);
			if (cachedbl.size() != num) {
				for (BindingList bindingList : cachedbl) {
					Utils.println(bindingList.toString());
				}
				Utils.waitHere("Incorrect groundings : " + num + " for the bl: " + cachedbl );
				
			}
		}
		((RegressionExample)eg).cacheNumGroundings(this, num);
		return num;
	}
	private NumberGroundingsCalculator groundingsCalc = null;
	private void initGroundingCalc() {
		if (groundingsCalc == null) {
			groundingsCalc = new NumberGroundingsCalculator(((LearnOneClause)this.task).context);
		}
	}
	
	private long getNumberOfGroundingsForRegressionEx(Example eg, BindingList theta, boolean isPartial) {
		long num = 1;
		// Check if we can just re-use the groundings from before
		Literal localLit = this.literalAdded.applyTheta(theta);
		if (!isPartial) {
			if (getParentNode() != null && getParentNode() != getRootNode()) {
				num = ((RegressionExample)eg).lookupCachedGroundings(getParentNode());
			}
			// No point in re-using if we haven't cached them
			if (num >= 0) {
				if (groundingsCalc.canLookupLiteral(localLit)) {
					if (groundingsCalc.isaFact(localLit)) {
						((RegressionExample)eg).cacheNumGroundings(this, num);
						return num;	
					}
					Utils.waitHere("num gndings shouldn't be 0 for " + eg + " Lit:" + localLit + " BL: " + theta + " Clause: " + this.getClause());
					return 0;
				}
			}
		}
		
		List<Literal> new_body = theta.applyTheta(this.getClauseBody());
		num = groundingsCalc.countGroundingsForConjunction(new_body, new ArrayList<>(), null);
		return num;
	}

	public double getPosCoverage() {
		return posCoverage;
	}

	private void setPosCoverage(double posCoverage) {
		this.posCoverage = posCoverage;
	}

}
