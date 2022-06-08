package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

import java.util.HashSet;
import java.util.List;

/*
 * @author shavlik 
 * 
 * Many of the ISO predicates are implemented.  Some differences among this code, Java, and ISO Prolog:
 * 
 *  not    is in YAP Prolog (though not in ISO Prolog).  In this code it is treated as the logical NOT (and hence
 *         cannot be used in Horn-clause resolution theorem proving).  The ISO standard for negation-by-failure ('\+(p)') is supported, even though this is quite ugly syntax.
 *         
 *  !      means Prolog's 'cut' and not Java's negation ('~' and 'not' can be used instead).
 *         
 *  ;      this code uses ';' as end-of-line (EOL).  These can be used for "or" instead: { 'or' 'v' 'else' }
 *         (note that 'v' [and 'V"] cannot be a variable or constant name). 
 *         
 *  P -> Q ; R  since this code uses '->' as implication and ';' as end-of-line (EOL), it instead uses
 *              'P then Q else R' (where the 'else R' is optional, just like '; R' is optional in ISO Prolog). 
 * 
 *  once() can take a full conjunctive sentence as its argument, e.g. 'once(p, q)' whereas Prolog requires there only be one argument, e.g., 'once((p, q))'. 
 *         This code's once() currently can only accept conjunctive sentences (or single literals).
 *         
 * 	mod    is used instead of Java's '%' since '%' is a comment in Prolog (and in this code)      
 * 
 * The flag 'lowercaseMeansVariable' allows one to choose between standard logical syntax and Prolog's syntax (in Prolog, variables are uppercase).
 * 
 * Also see this project's class DoBuiltInMath and DoBuiltInListProcessing.
 * 
 * These ISO predicates in YAP are not implemented (an incomplete list):  See http://www.ncc.up.pt/~vsc/Yap/documentation.html
 * 	initialization
 *  public
 *  P ; Q  ['P or Q' is implemented]
 *  'P -> Q' and 'P -> Q ; R'  [ "P then Q" and "P then Q else R"  since '->' is also used as implication
 *  catch
 *  throw
 *  atom_chars(?A,?L)
 *  atom_codes(?A,?L)
 *  number_codes(?A,?L)
 *  char_code(?A,?I)
 *  sub_atom(+A,?Bef, ?Size, ?After, ?At_out)
 *  arg(+N,+T,A)
 *  unify_with_occurs_check(?T1,?T2) (this is an easy fix if needed, but means there'll be another boolean in unify [which need to be fast], or duplicated code)
 *  X @< Y, X @=< Y, X @> Y, X @>= Y 
 *  
 *  
 * Some more to maybe add:
 * 	catch and throw
 *  if(p,q,r) P -> Q ; R
 *  treat 'bare' X's as call(X)'s (X must be a constant or a function)
 *  
 *  asserta see http://www.ncc.up.pt/~vsc/Yap/documentation.html
 *  assertz
 *  abolish
 *  clause
 *  retract
 *  
 *  ensure_loaded
 *  include
 *  multifile
 *  discontiguous
 *  
 *  in prolog mode ';' should be OR!
 *  
 *  :- p, q. [process these when parsing the file, or right afterwards?]
 *  
 *  
 *  file open, close, read, write, exists  <-- call Java's 
 *  format <-- call Java's
 *  
 *  sort - put in a library with the others in this group
 *  keysort
 *  
 *  check YAP's math and collect allCollector the ISO's
 *  
 *
 */
public class BuiltinProcedurallyDefinedPredicateHandler extends ProcedurallyDefinedPredicateHandler {

	private final HandleFOPCstrings stringHandler;


	/*
	 * The job of this class is to evaluate procedurally defined (i.e., built-in) predicates.
     */
	public BuiltinProcedurallyDefinedPredicateHandler(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;

        createBuiltins(stringHandler);
	}
	
	/*
	 * Create the hash map that contains allCollector of the built-in
	 * ("procedurally defined") predicates. If someone extends this class,
	 * but sure to call this first, then add the PredicateName's of the new
	 * built-ins to the hash map before returning it.
	 */
	private void createBuiltins(HandleFOPCstrings stringHandler) {
		boolean hold_cleanFunctionAndPredicateNames = stringHandler.cleanFunctionAndPredicateNames;
		stringHandler.cleanFunctionAndPredicateNames = false;
		hashOfSupportedPredicates = new HashSet<>(64);

		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.var,    1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.list, 1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.number, 1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.is,     2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.equal,  2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.gt,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.lt,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.gte,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.lte,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.length,2));

		stringHandler.cleanFunctionAndPredicateNames = hold_cleanFunctionAndPredicateNames;
	}

    @Override
    public boolean canHandle(PredicateName predicateName, int arity) {
        if ( super.canHandle(predicateName, arity) ) return true;

        // Handle the odd ones...
        if ( predicateName == stringHandler.standardPredicateNames.print )    return true; // These are for allCollector arities...
        if ( predicateName == stringHandler.standardPredicateNames.write )    return true;
		return predicateName == stringHandler.standardPredicateNames.waitHere;
	}
	
	/*
	 *  This handler manages built-in's like equals, diff, <, >, <=, >=, etc.  Note that these return BINDING LISTS and not Booleans.
	 */
	public BindingList handle(HornClauseContext context, Literal literal, Unifier unifier, BindingList bindingList) throws SearchInterrupted {
		PredicateName pred = literal.predicateName;
		List<Term>    args = literal.getArguments();
		int       numbArgs = literal.numberArgs();

		// Trevor: should we set stringHandler=context.getStringHandler() here?  JWS (6/11)
		if ((pred == stringHandler.standardPredicateNames.equal) && numbArgs == 2) {  // This is '==' - must be equal w/o unification.
			if (args.get(0) == args.get(1)) { return bindingList; }
			if (args.get(0) == null)        { return null; }
			return (args.get(0).equals(args.get(1)) ? bindingList : null);
		}
		if (pred == stringHandler.standardPredicateNames.is && numbArgs == 2) {
			Term result = context.getStringHandler().simplify(args.get(1));
			return result == null ? null : unifier.unify(args.get(0), result, bindingList);
		}
		if ((pred == stringHandler.standardPredicateNames.var) && numbArgs == 1) {
			return (args.get(0) instanceof Variable ? bindingList : null);
		}
		if (pred == stringHandler.standardPredicateNames.list && numbArgs == 1) {
			return (args.get(0) instanceof ConsCell ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.number) && numbArgs == 1) {
			return (args.get(0) instanceof NumericConstant ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.gt) && numbArgs == 2) {
			confirmAllVarsAreBound("gt: ", args, true);
			if (!(args.get(0) instanceof NumericConstant) || !(args.get(1) instanceof NumericConstant)) { Utils.error("Both args must be numbers: " + literal); }
			double value1 = ((NumericConstant) args.get(0)).value.doubleValue();
			double value2 = ((NumericConstant) args.get(1)).value.doubleValue();
			return (value1 > value2 ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.lt)  && numbArgs == 2) {
			confirmAllVarsAreBound("lt: ", args, true);
			if (!(args.get(0) instanceof NumericConstant) || !(args.get(1) instanceof NumericConstant)) { Utils.error("Both args must be numbers: " + literal); }
			double value1 = ((NumericConstant) args.get(0)).value.doubleValue();
			double value2 = ((NumericConstant) args.get(1)).value.doubleValue();
			return (value1 < value2 ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.gte) && numbArgs == 2) {
			confirmAllVarsAreBound("gte: ", args, true);
			if (!(args.get(0) instanceof NumericConstant) || !(args.get(1) instanceof NumericConstant)) { Utils.error("Both args must be numbers: " + literal); }
			double value1 = ((NumericConstant) args.get(0)).value.doubleValue();
			double value2 = ((NumericConstant) args.get(1)).value.doubleValue();
			return (value1 >= value2 ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.lte) && numbArgs == 2) {
			confirmAllVarsAreBound("lte: ", args, true);
			if (!(args.get(0) instanceof NumericConstant) || !(args.get(1) instanceof NumericConstant)) { Utils.error("Both args must be numbers: " + literal); }
			double value1 = ((NumericConstant) args.get(0)).value.doubleValue();
			double value2 = ((NumericConstant) args.get(1)).value.doubleValue();
			return (value1 <= value2 ? bindingList : null);
		}
		if (pred == stringHandler.standardPredicateNames.print || pred == stringHandler.standardPredicateNames.write) {
			if (args == null) { Utils.println(""); } else { Utils.println(pred.toString() + ":" + args); }
			return bindingList;
		}
		if (pred == stringHandler.standardPredicateNames.waitHere) {
			Utils.waitHere(args.toString()); // Should we FORCE a wait?  Probably not since this would likely be used for debugging.
			return bindingList;
		}
		if (pred == stringHandler.standardPredicateNames.length && numbArgs == 2) {
			Term arg0 = args.get(0);
			if (arg0 instanceof Variable) { Utils.error("First argument cannot be a variable: " + literal); }
			ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(0));
			return unifier.unify(context.getStringHandler().getNumericConstant(cc.length()), args.get(1), bindingList);
		}

		if (pred == stringHandler.standardPredicateNames.negationByFailure && numbArgs == 1) {
			Utils.error("Negation-by-failure is handled elsewhere (in HornProofStepGenerator) and should not reach here.");
		}
		Utils.error("Unknown procedurally defined predicate: " + literal);
		return null;
	}

}
