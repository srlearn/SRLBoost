package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author shavlik
 */
public class DoBuiltInListProcessing extends AllOfFOPC {

	private final FunctionName conscell; // Should really have ConsCell instances, but check for this as a function name as well.
	private final FunctionName first;

	private final FunctionName convertListToString;

	private final HandleFOPCstrings stringHandler;
	private final Map<FunctionName,Set<Integer>> canHandle = new HashMap<>(16);

	DoBuiltInListProcessing(HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
		boolean hold = stringHandler.cleanFunctionAndPredicateNames;
		stringHandler.cleanFunctionAndPredicateNames = false;
		
		conscell = addFunctionName("conscell");
		first    = addFunctionName("first");
		convertListToString  = addFunctionName("convertListToString");
		
		stringHandler.cleanFunctionAndPredicateNames = hold;
	}
	
	private FunctionName addFunctionName(String fNameString) {
		FunctionName fName = stringHandler.getFunctionName(fNameString);
		Set<Integer> lookup = canHandle.computeIfAbsent(fName, k -> new HashSet<>(4));
		lookup.add(1);
		return fName;
	}

	private boolean canHandle(FunctionName fName, int arity) {
		Set<Integer> lookup = canHandle.get(fName);
		if (lookup == null) { return false; }
		return lookup.contains(arity);
	}
	boolean canHandle(Term expression) {
		if (expression instanceof Function) {	
			FunctionName fName = ((Function) expression).functionName;
			
			return canHandle(fName, ((Function) expression).numberArgs());
		}
		return false;
	}
	
	/** 
	 * Simplify expressions involving lists.  Complain if this can't be done.
	 * @return The simplification of the given expression.
	 */
	public Term simplify(Term expression) {
		if (Function.isaConsCell(expression)) {
			return expression;
		}
		if (expression instanceof Function) {	
			FunctionName name = ((Function) expression).functionName;
			List<Term>   args = ((Function) expression).getArguments();
			
			if (name == conscell) {
				return ConsCell.ensureIsaConsCell(stringHandler, expression);
			}
			
			if (name == first) {
				if (args.size() != 1) { Utils.error("Must have ONE argument here: " + expression); }
				ConsCell arg1 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(0)));
				return arg1.first();
			}
			else if (name == convertListToString) { 
				if (args.size() != 1) { Utils.error("Must have ONE argument here: " + expression); }
				ConsCell arg1 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(0)));
				return stringHandler.getStringConstant(arg1.toString(), false);
			}
            else {
                Utils.error("Cannot simplify, unknown name '" + name + "' in\n  " + expression);
                return null;
            }
		}
        else {
            return expression;
        }
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return "<this is an instance of the DoBuiltInListProcessing class>";
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return "<this is an instance of the DoBuiltInListProcessing class>";
	}

	@Override
	public DoBuiltInMath applyTheta(Map<Variable, Term> bindings) {
		Utils.error("Should not call applyTheta on a DoBuiltInListProcessing.");
		return null;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}

}
