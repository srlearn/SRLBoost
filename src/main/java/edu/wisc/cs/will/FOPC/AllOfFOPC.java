package edu.wisc.cs.will.FOPC;

import java.util.Map;

/*
 * @author shavlik
 */
public abstract class AllOfFOPC {
	protected final static int debugLevel = 0;   // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).
	final static int defaultPrecedence = Integer.MIN_VALUE;  // This plays it safe and uses a lot of parentheses.
	public          static boolean renameVariablesWhenPrinting = false;
	static boolean truncateStrings             = true; // Prevent printing very long strings if true.
	public          static boolean printUsingAlchemyNotation   = false;
 
    /*
	 * This class is a superclass of all FOPC constructs.
	 */
	public AllOfFOPC() {
	}

	public abstract AllOfFOPC applyTheta(Map<Variable,Term> bindings);
	public abstract int       countVarOccurrencesInFOPC(Variable v);

    public abstract String    toString(                             int precedenceOfCaller, BindingList bindingList);
	public abstract String    toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList);

	public String toPrettyString() {
		return toPrettyString("", defaultPrecedence); // Use some average value?
	}
	public String toPrettyString(String newLineStarter) {
		return toPrettyString(newLineStarter, defaultPrecedence); // Use some average value?
	}
    @Override
	public String toString() {
		return toString(defaultPrecedence); // Use some average value?
	}

    public String toString(BindingList bindingList) {
        return toString(defaultPrecedence, bindingList);
    }

    public String toString(int precedenceOfCaller) {
        if ( renameVariablesWhenPrinting ) {
            return toString(precedenceOfCaller, new BindingList());
        }
		return toString(precedenceOfCaller, (BindingList)null);
    }

    public String toPrettyString(String newLineStarter, int precedenceOfCaller) {
        if ( renameVariablesWhenPrinting ) {
            return toPrettyString(newLineStarter, precedenceOfCaller, new BindingList());
        }
		return toPrettyString(newLineStarter, precedenceOfCaller, null);
    }
}
