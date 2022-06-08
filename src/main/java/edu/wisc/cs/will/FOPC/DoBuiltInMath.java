package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author shavlik
 * 
 * Differences from ISO Prolog (as per YAP's documentation 12/07: http://www.ncc.up.pt/~vsc/Yap/documentation.html)
 * 
 *   /@ is integer division instead of // (since that is a comment to us)
 *   several items from Java's Math class ARE included (e.g., toDegreesFunction)
 *   
 *   These are NOT implemented:
 *   	float(X)
 *		float_fractional_part(X)
 *		float_integer_part(X)
 *		X /\ Y  [Integer bitwise conjunction]
 *		X \/ Y  [Integer bitwise disjunction]
 *		X #  Y  [Integer bitwise exclusive disjunction]
 *		X >> Y  [Integer bitwise right logical shift of X by Y places]
 *		\ X     [Integer bitwise negation]
 *
 *		
 *	This generally produces DOUBLES, which isn't ideal, but we'll live with it for now.
 *  The use of the built-in function 'int' can override this.  (TODO if all args are int's keep as an int?)
 *  
 *  To EXTEND this class, "cut-and-paste" from what is done here.
 *  ALSO (a) before to call super() when creating instances of the new class and 
 *       (b) call this class's simplify() method if the new class encounters an unknown function name.
 *       
 *  TODO Build a simpler-to-use mechanism for allowing users to extend the set of built-in math functions.
 *  TODO this code is a memory hog and needs to be cleaned up (eg, this design keeps all calculations encountered, including intermediate ones, as strings.
 *        
 */
public class DoBuiltInMath extends AllOfFOPC {

    private final HandleFOPCstrings stringHandler;

    private final Map<FunctionName, Set<Integer>> canHandle = new HashMap<>(16);

    /*
     * Reduce an arithmetic expression, producing a NumericConstant node.   Throw an error if any variables encountered where a number is needed.
     * Can NOT use statics since the function names will be different instances for each string handler.
     */
    DoBuiltInMath(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;

        addFunctionName("integer", 1); // Allow the user to force integer results.
        addFunctionName("mod", 2); // Use Java's definition of mod.  Don't use a single-character symbol due to confusion between Java and Prolog.
        addFunctionName("min", 2);
        addFunctionName("max", 2);
        addFunctionName("abs", 1);
        addFunctionName("sin", 1);
        addFunctionName("cos", 1);
        addFunctionName("tan", 1);
        addFunctionName("sinh", 1);
        addFunctionName("cosh", 1);
        addFunctionName("tanh", 1);
        addFunctionName("asin", 1);
        addFunctionName("acos", 1);
        addFunctionName("atan", 1);
        addFunctionName("atan2", 1);
        addFunctionName("log", 1);
        addFunctionName("log", 2); // With TWO arguments, the second is the BASE.
        addFunctionName("exp", 1);
        addFunctionName("exp", 2); // With TWO arguments, is 'pow' (ie, X^Y).
        addFunctionName("pow", 2);
        addFunctionName("sqrt", 1);
        addFunctionName("sqrtSafe", 1);
        addFunctionName("sqrtAbs", 1);
        addFunctionName("random", 0);
        addFunctionName("ceiling", 1); // Also use 'ceil' since that is Java's name.
        addFunctionName("floor", 1);
        addFunctionName("round", 1);
        addFunctionName("sign", 1);
        addFunctionName("hypot", 1);
        addFunctionName("toDegrees", 1);
        addFunctionName("toRadians", 1);
        addFunctionName("length", 1); // Explicitly list those list-processing functions that return numbers.
        addFunctionName("position", 2);
    }

    private void addFunctionName(String fNameString, int arity) {
        FunctionName fName = stringHandler.getFunctionName(fNameString);
        Set<Integer> lookup = canHandle.computeIfAbsent(fName, k -> new HashSet<>(4));
        lookup.add(arity);
    }

    private boolean canHandle(FunctionName fName, int arity) {

        Set<Integer> lookup = canHandle.get(fName);
        if (lookup == null) {
            return false;
        }
        return lookup.contains(arity);
    }

    boolean canHandle(Term expression) {
        if (expression instanceof NumericConstant) {
            return true;
        }
        if (expression instanceof Function) {
            FunctionName fName = ((Function) expression).functionName;
            return canHandle(fName, ((Function) expression).numberArgs());
        }
        return false;
    }

    /*
     * Simplify a logical Term into a numeric constant.  Complain if this can't be done.
     * @return The numeric constant that is the simplification of the given expression.
     */
    public NumericConstant simplify(Term expression) {
        if (expression instanceof NumericConstant) {
            return (NumericConstant) expression;
        }
        if (expression instanceof Function) {
            double result = simplifyAsDouble(expression);
            return stringHandler.getNumericConstant(result);
        }
		Utils.error("Cannot simplify: " + expression);
		return null;
    }

    /*
     * Do all the intermediate calculations using doubles.  The method above converts into a FOPC data structure at the end.
     * @return A double, the result of computing the given expression.
     */
    private double simplifyAsDouble(Term expression) {
    	
        if (expression instanceof NumericConstant) {
            return ((NumericConstant) expression).value.doubleValue();
        }
        if (expression instanceof Function) {
            FunctionName name = ((Function) expression).functionName;
            List<Term>   args = ((Function) expression).getArguments();

            Utils.error("Unknown math operator: " + name);
        } else if (expression instanceof SentenceAsTerm) {
        	Sentence s = ((SentenceAsTerm) expression).sentence;
        	if (s instanceof Clause) {
        		Clause c = (Clause) s;
        		if (c.getLength() == 1 && c.isDefiniteClause()) {
        			Literal lit = c.getPosLiteral(0);
        			Function  f = lit.asFunction();
        			return simplifyAsDouble(f);
        		}
        		Utils.error("Cannot simplify: (class = " + ((SentenceAsTerm) expression).sentence.getClass() + ")\n  clause = " + c);
        	}
        	Utils.error("Cannot simplify: (class = " + ((SentenceAsTerm) expression).sentence.getClass() + ")\n  sentence = " + s);
        } else if (expression instanceof StringConstant) {
        	try {
        		return Double.parseDouble(expression.toString()); // JWS added this June 2011 because the next ELSE had an error, so we might as well try this before throwing that error.
        	} catch (NumberFormatException e) {
        		Utils.error("Cannot simplify: (class = " + expression.getClass() + ")\n  " + expression);
        	}
        }
        else {
            Utils.error("Cannot simplify: (class = " + expression.getClass() + ")\n  " + expression);
        }
        return Double.NaN;
    }

    public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
        return "<this is an instance of the DoBuiltInMath class>";
    }

    public String toString(int precedenceOfCaller, BindingList bindingList) {
        return "<this is an instance of the DoBuiltInMath class>";
    }

    @Override
    public DoBuiltInMath applyTheta(Map<Variable, Term> bindings) {
        Utils.error("Should not call applyTheta on a DoBuiltInMath.");
        return null;
    }

    @Override
    public int countVarOccurrencesInFOPC(Variable v) {
        return 0;
    }
}
