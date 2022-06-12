package edu.wisc.cs.will.FOPC;

import java.util.Map;

/*
 * @author shavlik
 *
 *  All functions with the same name map to the same instance. 
 */
public class FunctionName extends AllOfFOPC {
	public final String  name;
	final boolean printUsingInFixNotation = false;

	FunctionName(String name) { // This is protected because getFunctionName(String name) should be used instead.
		this.name = name;
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return name;
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return name;
	}

	@Override
	public FunctionName applyTheta(Map<Variable, Term> bindings) {
		return this;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}
}
