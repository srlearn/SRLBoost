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
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.equal2, 2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.diff,      2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.notEqual,  2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.ground,    1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.copyTerm,    2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.unify,       2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.unify2,      2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.ununifiable, 2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.ununifiable2,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.gt,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.lt,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.gte,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.lte,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.findAllCollector,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.findAllCollector,3));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.allCollector,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.allCollector,3));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.bagOfCollector,3));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.setOfCollector,3));
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
		if ((pred == stringHandler.standardPredicateNames.unify || pred == stringHandler.standardPredicateNames.unify2) && numbArgs == 2) {
			return unifier.unify(args.get(0), args.get(1), bindingList);
		}
		if ((pred == stringHandler.standardPredicateNames.equal || pred == stringHandler.standardPredicateNames.equal2) && numbArgs == 2) {  // This is '==' - must be equal w/o unification.
			if (args.get(0) == args.get(1)) { return bindingList; }
			if (args.get(0) == null)        { return null; }
			return (args.get(0).equals(args.get(1)) ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.diff || pred == stringHandler.standardPredicateNames.notEqual) && numbArgs == 2) {
			if (args.get(0) == args.get(1)) { return null; }
			if (args.get(0) == null)        { return bindingList; }
			return (args.get(0).equals(args.get(1)) ? null : bindingList);
		}
		if ((pred == stringHandler.standardPredicateNames.ununifiable || pred == stringHandler.standardPredicateNames.ununifiable2)  && numbArgs == 2) { // Succeeds if arg0 and arg1 do not unify.
			// Cannot allow the bindingList to be modified, so need a copy.  (Might be able to get away without using the oldBindingList, since that should have been applied, but play it safe.)
			BindingList copyOfBindings = bindingList.copy();
			if (unifier.unify(args.get(0), args.get(1), copyOfBindings) == null) { return bindingList; }
			return null;
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
		if (pred == stringHandler.standardPredicateNames.compound && numbArgs == 1) {
			return (args.get(0) instanceof Function ? bindingList : null);
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
		if (pred == stringHandler.standardPredicateNames.findAllCollector) {
			if (numbArgs == 2) { // We're collecting allCollector answers in this phase.
				Term         term           =                args.get(0);
				ObjectAsTerm collector      = (ObjectAsTerm) args.get(1);
				ConsCell     termsCollected = (ConsCell)     collector.item; 
				// Collect ALL proofs of goal, which must be a literal or a conjunct - actually, a clause with only negative literals.
				// And for each proof, save 'term' (which presumably shares variables with 'goal') in a list.
				// Unify this list with 'list' as the final step.
				collector.item = context.getStringHandler().getConsCell(term, termsCollected, null);
				return null;
			}
			else if (numbArgs == 3) { // We're processing the collection of answers in this phase.
				Term         list      =                args.get(0);
				ObjectAsTerm collector = (ObjectAsTerm) args.get(1);
				ConsCell     answers   = (ConsCell)     collector.item;
				return unifier.unify(list, (answers == null ? null : answers.reverse()), bindingList);
			}
			Utils.error("Wrong number of arguments (expecting 2 or 3): '" + literal + "'.");
		}
		if (pred == stringHandler.standardPredicateNames.allCollector) {
			if (numbArgs == 2) { // We're collecting allCollector answers in this phase.
				Term         term           =                args.get(0);
				ObjectAsTerm collector      = (ObjectAsTerm) args.get(1);
				ConsCell     termsCollected = (ConsCell)     collector.item;  
				// Collect ALL proofs of goal, which must be a literal or a conjunct - actually, a clause with only negative literals.
				// And for each proof, save 'term' (which presumably shares variables with 'goal') in a list.
				// Unify this list with 'list' as the final step.
				if (termsCollected.memberViaEquals(term)) { // Need to do a equivalent match since term could be complex (e.g., a Function).
					return null; // Remove duplicates.
				}
				collector.item = context.getStringHandler().getConsCell(term, termsCollected, null);
				return null;
			}
			else if (numbArgs == 3) {
				// We're processing the collection of answers in this phase.
				Term         list      =                args.get(0);
				ObjectAsTerm collector = (ObjectAsTerm) args.get(1);
				ConsCell     answers   = (ConsCell)     collector.item;
				return unifier.unify(list, (answers == null ? null : answers.reverse()), bindingList);
			}
			Utils.error("Wrong number of arguments (expecting 2 or 3): '" + literal + "'.");
		}
		if (pred == stringHandler.standardPredicateNames.bagOfCollector   && numbArgs == 3) {
			Utils.error("'bagof' is not yet implemented");
		}
		if (pred == stringHandler.standardPredicateNames.setOfCollector   && numbArgs == 3) {
			Utils.error("'setof' is not yet implemented");
		}
		if (pred == stringHandler.standardPredicateNames.ground  && numbArgs == 1) {
			return (args.get(0).isGrounded() ? bindingList : null);
		}
		if (pred == stringHandler.standardPredicateNames.copyTerm  && numbArgs == 2) {

            // TAW: I agree that the ISO definition does specify copy_term(?TI,-TF).  However,
            // TAW: this doesn't mean TF has to be a variable.  As with any Prolog call, even
            // TAW: if it is an "output" argument, you can always try to prove the goal with
            // TAW: the argument bound to something.  The - just means that the value will be
            // TAW: generated.
            // TAW: The '+' works a little different.  You must provide a non-free variable at
            // TAW: the time of evaluation.
            // TAW: The '?' basically means that if you provide it, it will be used in the
            // TAW: algorithm (whatever the literal attempts to do), but if you don't then,
            // TAW: it won't.
            // TAW: In allCollector cases, if a non-free variable is passed in, it must unify with
            // TAW: the results.
            
            Term copy = args.get(0).copyAndRenameVariables();
            return unifier.unify(copy, args.get(1), bindingList);

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
