package edu.wisc.cs.will.FOPC;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/*
 * @author shavlik
 *
 *  All functions with the same name map to the same instance. 
 */
public class FunctionName extends AllOfFOPC {
	public final String  name;
	private Map<List<Constant>,Constant> extensionalSemantics;
	boolean printUsingInFixNotation = false;

	FunctionName(String name) { // This is protected because getFunctionName(String name) should be used instead.
		this.name = name;
	}

	public void addExtensionalDefinition(List<Constant> inputs, Constant output) throws IllegalArgumentException {
		if (extensionalSemantics == null) { extensionalSemantics = new HashMap<>(8); }
		
		Constant current = extensionalSemantics.get(inputs);
		if (current != null) {
			if (current == output) { return; } // OK if redefined.
			throw new IllegalArgumentException("Cannot set " + name + inputs + " = '" + output + "' because it is currently = '" + current + "'");
		}
		extensionalSemantics.put(inputs,output);
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
