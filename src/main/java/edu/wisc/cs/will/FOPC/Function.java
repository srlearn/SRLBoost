package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author shavlik
 *
 */
public class Function extends Term implements LiteralOrFunction {
	private static final long serialVersionUID = 7269089649845325225L;
	public FunctionName functionName;
	List<Term>   arguments;    // Note: should not directly manipulate.  Instead use addArgument(), removeArgument(), and setArguments().
	private List<String> argumentNames; // (Optional) names of the arguments.
	private int        cached_arity      = -1;
	int        cachedVariableCount = -1; // Only set to false if CHECKED.  (Key: -1 = unknown, 0 = false, 1 = true.)

	Function(HandleFOPCstrings stringHandler, FunctionName functionName, List<Term> arguments, TypeSpec typeSpec) {
		this.stringHandler = stringHandler;
		this.functionName  = functionName;
		this.arguments     = arguments;
		this.setTypeSpec(typeSpec);
		assert functionName != null;
		if (functionName.name.equals("")) { Utils.error("You have not provided a function name that is the empty string!"); }
	}
	Function(HandleFOPCstrings stringHandler, FunctionName functionName, TypeSpec typeSpec) {
		this(stringHandler, functionName, null, typeSpec);
	}
	Function(HandleFOPCstrings stringHandler, FunctionName functionName, List<Term> arguments, List<String> argumentNames, TypeSpec typeSpec) {
		this(stringHandler, functionName, arguments, typeSpec);
		this.argumentNames = argumentNames;
		sortArgumentsByName();
		// Allow either to be null (e.g., a 'bare copy' might be being made).
		if (arguments != null && argumentNames != null && Utils.getSizeSafely(arguments) !=  Utils.getSizeSafely(argumentNames)) {
			Utils.error("Have " + arguments + " and " + argumentNames + " - number of arguments and number of names must match.");
		}
	}

	void clearArgumentNamesInPlace() {
		if (numberArgs() < 1) { return; }
		if (argumentNames != null) {
			if (argumentNames.get(0).equalsIgnoreCase("name")) {
				removeArgument(arguments.get(0), argumentNames.get(0));
			}
		}
		argumentNames = null;
		if (arguments == null) { return; }
		for (Term term : arguments) if (term instanceof Function) {
			((Function) term).clearArgumentNamesInPlace();
		}
	}

	public int numberArgs() {
		if (cached_arity < 0) { setNumberArgs(); }
		return cached_arity;
	}
	private void setNumberArgs() {
		if (arguments == null) { cached_arity = 0; }
		else                   { cached_arity =  arguments.size(); }
	}

	private void removeArgument(Term term, String name) {
		if (!arguments.remove(term))     { Utils.error("Could not remove '" + term + "' from '" + this + "'."); }
		if (!argumentNames.remove(name)) { Utils.error("Could not remove '" + name + "' from '" + this + "'."); }
		setNumberArgs();
		sortArgumentsByName();
	}
	
	// Cache this calculation to save time.
	public boolean containsVariables() {
		if (cachedVariableCount < 0) {
			if (arguments == null) { cachedVariableCount = 0; return false; }
			for (Term term : arguments) { 
				if ( term instanceof Variable)                                           { cachedVariableCount = 1; return true; }
				if ((term instanceof Function) && term.containsVariables()) { cachedVariableCount = 1; return true; }
			}
			if (cachedVariableCount < 0) { cachedVariableCount = 0; }
		}
		return (cachedVariableCount > 0);
	}

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        if (!(that instanceof Function)) return null;

        Function function = (Function) that;

        if (!this.functionName.equals(function.functionName)) return null;
        if ( this.numberArgs() != function.numberArgs() ) return null;

        for (int i = 0; i < numberArgs(); i++) {
            bindings = this.getArgument(i).isEquivalentUptoVariableRenaming(function.getArgument(i), bindings);
            if ( bindings == null ) return null;
        }

        return bindings;
    }

	/* Would any variables in this function remain UNBOUND if this binding list were to be applied?
	 */
    @Override
	public boolean freeVariablesAfterSubstitution(BindingList theta) {
		if (!containsVariables()) { return false; }
		if (theta == null || arguments == null) { return false; }
		for (Term term : arguments) if (term.freeVariablesAfterSubstitution(theta)) { return true; }
		return false;
	}

	@Override
	public Function applyTheta(Map<Variable,Term> theta) {
		// This should be essentially the same code as in Literal.applyTheta
        boolean needNewFunction = false; // See if there is a chance this might need to change (only do a one-level deep evaluation).
        if (arguments != null) {
            for (Term term : arguments) {
                if (!((term instanceof Variable && theta.get(term) == null) || term instanceof Constant)) {
                    needNewFunction = true;
                    break;
                }
            }
        }

        if (!needNewFunction) {
			return this;
        }

        int numbArgs = numberArgs();
        List<Term> newArguments = (numbArgs == 0 ? null : new ArrayList<>(numberArgs()));
        if (numbArgs > 0) {
            for (int i = 0; i < numbArgs; i++) {
                Term arg = arguments.get(i);
                if (arg == null) {
                    Utils.error("Has an arg=null: " + this);
                }
                newArguments.add(arg.applyTheta(theta));
            }
        }
		return getBareCopy(newArguments);
	}

	Function getBareCopy(List<Term> newArguments) {
		return stringHandler.getFunction(functionName, newArguments, argumentNames, typeSpec);
	}
	private Function getBareCopy(List<Term> newArguments, List<String> newArgumentNames) {
		return stringHandler.getFunction(functionName, newArguments, newArgumentNames, typeSpec);
	}

	@Override
	public Function copy(boolean recursiveCopy) { // recursiveCopy=true means that the copying recurs down to the leaves.
		List<Term>   newArguments = (arguments     != null ? new ArrayList<>(  numberArgs()) : null);
		List<String> newArgNames  = (argumentNames != null ? new ArrayList<>(numberArgs()) : null);
		if (argumentNames != null) { newArgNames.addAll(argumentNames); }
		assert newArguments != null;
		if (recursiveCopy) {
			if (arguments != null) {				
				for (Term term : arguments) {	
					newArguments.add(term == null ? null : term.copy(true));
				}
			}
			return getBareCopy(newArguments, newArgNames);
		}
		if (arguments!= null) { newArguments.addAll(arguments);    }
		return getBareCopy(newArguments, newArgNames);
	}

    @Override
	public Function copy2(boolean recursiveCopy, BindingList bindingList) { // recursiveCopy=true means that the copying recurs down to the leaves.
		List<Term>   newArguments = (arguments     != null ? new ArrayList<>(  numberArgs()) : null);
		List<String> newArgNames  = (argumentNames != null ? new ArrayList<>(numberArgs()) : null);
		if (argumentNames != null) { newArgNames.addAll(argumentNames); }
		assert newArguments != null;
		if (recursiveCopy) {
			if (arguments != null) {
				for (Term term : arguments) {
					newArguments.add(term == null ? null : term.copy2(true, bindingList));
				}
			}
			return getBareCopy(newArguments, newArgNames);
		}
		if (arguments!= null) { newArguments.addAll(arguments);    }
		return getBareCopy(newArguments, newArgNames);
	}

    @Override
    public Sentence asSentence() {
        return stringHandler.getLiteral(stringHandler.getPredicateName(functionName.name), arguments);
    }

    public Clause asClause() {
        return stringHandler.getClause( stringHandler.getLiteral(stringHandler.getPredicateName(functionName.name), arguments), true);
    }

    public Literal asLiteral() {
        return stringHandler.getLiteral(stringHandler.getPredicateName(functionName.name), arguments, argumentNames);
    }
	
    @Override
	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
		List<Variable> result = new ArrayList<>(numberArgs());
		
		if (arguments != null) for (Term term : arguments) if (term != null) {	
			Collection<Variable> tempVarList = term.collectFreeVariables(boundVariables);
			
			if (tempVarList != null) { for (Variable var : tempVarList) if (!result.contains(var)) { result.add(var); }}
		}
		return result;
	}
	
	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((functionName == null) ? 0 : functionName.hashCode());
		result = prime * result + ((arguments    == null) ? 0 : arguments.hashCode());
		return result;
	}

	// Are these two literals identical even if not the same instance?  Can be overridden by stringHandler.useStrictEqualsForLiterals
	@Override
	public boolean equals(Object other) {
		if (this == other) { return true; }
		if (!(other instanceof Function)) { return false; }
		
		Function otherAsFunction = (Function) other;
		if (functionName != otherAsFunction.functionName) { return false; }
		int thisNumberOfArgs  =                 numberArgs();
		int otherNumberOfArgs = otherAsFunction.numberArgs();
		if (thisNumberOfArgs != otherNumberOfArgs)       { return false; }

		// Should do a double walk of the two lists, but I don't recall the syntax
		for (int i = 0; i < thisNumberOfArgs; i++) {
			if (!arguments.get(i).equals(otherAsFunction.arguments.get(i))) { return false; }
		}
		if (argumentNames == null && otherAsFunction.argumentNames == null) { return true;  }
		if (argumentNames == null || otherAsFunction.argumentNames == null) { return false; }
		// Should do a double walk of the two lists, but I don't recall the syntax
		for (int i = 0; i < thisNumberOfArgs; i++) {
			if (!argumentNames.get(i).equalsIgnoreCase(otherAsFunction.argumentNames.get(i))) { return false; }
		}
		return true;
	}

   // Are these two equivalent POSSIBLY AFTER SOME VARIABLE RENAMING.
    @Override
    public BindingList variants(Term other, BindingList bindings) {
        // Need to collect the matched variables (so they don't get matched to another variable elsewhere).
        if (!(other instanceof Function)) {
            return null;
        }
        
        Function otherAsFunction = (Function) other;
        if (functionName != otherAsFunction.functionName) {
            return null;
        }
        
        int thisNumberOfArgs = numberArgs();
        int otherNumberOfArgs = otherAsFunction.numberArgs();
        
        if (thisNumberOfArgs != otherNumberOfArgs) {
            return null;
        }
        
        if (arguments != null) {
            int i = 0;
            for (Term arg : arguments) { // Should do a double walk of the two lists, but I don't recall the syntax (to do).
                bindings = arg.variants(otherAsFunction.arguments.get(i++), bindings);
                if (bindings == null) {
                    return null;
                }
            }
        }
        
        if (argumentNames == null && otherAsFunction.argumentNames == null) {
            return bindings;
        }
        
        if (argumentNames == null || otherAsFunction.argumentNames == null) {
            return null;
        }
        
        for (int j = 0; j < thisNumberOfArgs; j++) {
        	// Should do a double walk of the two lists, but I don't recall the syntax
            if (!argumentNames.get(j).equalsIgnoreCase(otherAsFunction.argumentNames.get(j))) {
                return null;
            }
        }
        return bindings;
    }

	public Literal convertToLiteral(HandleFOPCstrings stringHandler) {
		PredicateName predicateName = stringHandler.getPredicateName(functionName.name);
		return stringHandler.getLiteral(predicateName, arguments, argumentNames);
	}
	
    @Override
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		if (functionName.name.equalsIgnoreCase("conscell")) {
			return stringHandler.getConsCell(this).toPrettyString(newLineStarter, precedenceOfCaller, bindingList);
		}
		String  fNameStr = (typeSpec != null ? typeSpec.getModeString() + typeSpec.isaType.typeName + ":" : "") + functionName;
		String  end      = (typeSpec != null ? typeSpec.getCountString() : "");
		boolean firstOne = true;
		boolean hasArgNames = (argumentNames != null);
		
		if (functionName.printUsingInFixNotation && numberArgs() == 1) {
			int precedence = HandleFOPCstrings.getOperatorPrecedence_static(functionName.name);
			if (precedenceOfCaller < precedence) { return "(" + fNameStr + (hasArgNames ? argumentNames.get(0) + "=": "") + arguments.get(0).toPrettyString(newLineStarter, precedence, bindingList) + ")" + end; }
			return fNameStr + (hasArgNames ? argumentNames.get(0) + "=": "") + arguments.get(0).toPrettyString(newLineStarter, precedence, bindingList) + end;
	    }
		if (functionName.printUsingInFixNotation && numberArgs() == 2) {
			int precedence =  HandleFOPCstrings.getOperatorPrecedence_static(functionName.name);
			if (precedenceOfCaller < precedence) { return "(" + (hasArgNames ? argumentNames.get(0) + "=": "") + arguments.get(0).toPrettyString(newLineStarter, precedence, bindingList) + " " + fNameStr + " " + (hasArgNames ? argumentNames.get(1) + "=": "") + arguments.get(1).toPrettyString(newLineStarter, precedence, bindingList) + ")" + end; }
			return                                              (hasArgNames ? argumentNames.get(0) + "=": "") + arguments.get(0).toPrettyString(newLineStarter, precedence, bindingList) + " " + fNameStr + " " + (hasArgNames ? argumentNames.get(1) + "=": "") + arguments.get(1).toPrettyString(newLineStarter, precedence, bindingList)       + end;
	    }
		StringBuilder result = new StringBuilder(fNameStr + "(");
		for (int i = 0; i < numberArgs(); i++) {
			Term arg = arguments.get(i);
			if (firstOne) { firstOne = false; } else {
				result.append(", "); }
			result.append(hasArgNames ? argumentNames.get(i) + "=" : "").append(arg.toPrettyString(newLineStarter, Integer.MAX_VALUE, bindingList)); // No need for extra parentheses in an argument list.
		}		
		return result + ")" + end;
	}

    @Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		if (functionName.name.equalsIgnoreCase("consCell")) {
			return stringHandler.getConsCell(this).toString(precedenceOfCaller, bindingList);
		}
		boolean useTypes = stringHandler.printTypedStrings;
		String  fNameStr = (typeSpec != null && useTypes ? typeSpec.getModeString() + typeSpec.isaType.typeName + ":" : "") + functionName;
		String  end      = (typeSpec != null && useTypes ? typeSpec.getCountString() : "");
		boolean firstOne = true;
		boolean hasArgNames = (argumentNames != null);
		
		if (functionName.printUsingInFixNotation && numberArgs() == 1) {
			int precedence = (stringHandler.alwaysUseParensForInfixFunctions ? Integer.MAX_VALUE : HandleFOPCstrings.getOperatorPrecedence_static(functionName.name));
			if (precedenceOfCaller <= precedence) { return "(" + fNameStr + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + ")" + end; }
			return                                               fNameStr + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList)       + end;
	    }
		if (functionName.printUsingInFixNotation && numberArgs() == 2) {
			int precedence = (stringHandler.alwaysUseParensForInfixFunctions ? Integer.MAX_VALUE : HandleFOPCstrings.getOperatorPrecedence_static(functionName.name));
			if (precedenceOfCaller <= precedence) { return "(" + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + " " + fNameStr + " " + (hasArgNames ? argumentNames.get(1) + "=": "") + arguments.get(1).toString(precedence, bindingList) + ")" + end; }
			return                                               (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + " " + fNameStr + " " + (hasArgNames ? argumentNames.get(1) + "=": "") + arguments.get(1).toString(precedence, bindingList)       + end;
	    }

		StringBuilder result = new StringBuilder(fNameStr + "(");
		for (int i = 0; i < numberArgs(); i++) {
			Term arg = arguments.get(i);	
			if (firstOne) { firstOne = false; } else {
				result.append(", "); }
			result.append(hasArgNames && i < argumentNames.size() ? argumentNames.get(i) + "=" : "").append(arg.toString(Integer.MAX_VALUE, bindingList)); // No need for extra parentheses in an argument list.
		}		
		return result + ")" + end;
	}
	
	public int countLeaves() {
		if (numberArgs() < 1) { return 0;}
		int total = 0;
		for (Term term : arguments) {
			if (term instanceof Function) { total +=  ((Function) term).countLeaves(); }
			else { total++; }
		}
		return total;
	}
	
	public List<Term> getArguments() {
		return arguments == null ? Collections.EMPTY_LIST : arguments;
	}	
	public Term getArgument(int i) {
		return arguments.get(i);
	}
	void setArguments(List<Term> arguments) {
		this.arguments = arguments;
		sortArgumentsByName();
	}
	public List<String> getArgumentNames() {
		return argumentNames;
	}
	void setArgumentNames(List<String> argumentNames) {
		this.argumentNames = argumentNames;
		sortArgumentsByName();
	}
	private void sortArgumentsByName() {
		if (argumentNames == null) { return; }
		int numbArgs = numberArgs();
		if (Utils.getSizeSafely(argumentNames) != numbArgs) { 
			Utils.error("# of arguments (" + numbArgs                           + ") does not equal number of argument names ("
										   + Utils.getSizeSafely(argumentNames) + "):\n   args = " + arguments + "\n  names = " + argumentNames + "\n    lit = " + this);
		}
		if (numbArgs < 2) { return; }
		List<NamedTerm> namedTerms = new ArrayList<>(numbArgs);
		Set<String> namesSeen = new HashSet<>(4);
		for (int i = 0; i < numbArgs; i++) {
			String argName = argumentNames.get(i);
			if (namesSeen.contains(argName)) { Utils.error("Cannot have duplicate names (" + argName + "): " + argumentNames); }
			if ( argName != null ) namesSeen.add(argName);
            namedTerms.add(new NamedTerm(arguments.get(i), argName));
		}
		namedTerms.sort(NamedTerm.comparator);
		arguments.clear();
		argumentNames.clear();
		for (NamedTerm nt : namedTerms) { 
			arguments.add(    nt.term);
			argumentNames.add(nt.name);
		}
	}

    // Sometimes what should be ConsCell instances are Function instances instead.
	// This provides a way to check for that case.
	public static boolean isaConsCell(Term expression) {  // This and the above look to be identical (JWS, 7/25/10). So I (JWS) deleted checkIfReallyIsaConsCell.
		if (expression instanceof ConsCell) { return true; }
		if (expression instanceof Function) {
			Function     f     = (Function) expression;
			FunctionName fName = f.functionName;
			return fName.name.equalsIgnoreCase("conscell");
		}
		return false;
	}

	@Override
    public <Return,Data> Return accept(TermVisitor<Return,Data> visitor, Data data) {
        return visitor.visitFunction(this, data);
    }
	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		int total = 0;
		if (arguments != null) { for (Term arg : arguments) { total += arg.countVarOccurrencesInFOPC(v); } }
		return total;
	}

	public int getArity() {
        return numberArgs();
    }

	public PredicateName getPredicateName() {
        return getStringHandler().getPredicateName( functionName.name );
    }

}

