package edu.wisc.cs.will.FOPC;

import java.io.IOException;
import java.io.Serializable;
import java.util.Map;

/*
 * @author shavlik
 * 
 * The material in this class is used in ILP and MLNs, though it can play a role in other logical-reasoning systems.
 *
 */
public class Type extends AllOfFOPC implements Serializable {
	public final String typeName;

    Type(String typeName) {
        this.typeName = typeName;
    }

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return typeName;
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return typeName;
	}

    @Override
	public Type applyTheta(Map<Variable, Term> bindings) {
		return this;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}
}
