package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/*
 * @author shavlik
 * The material in this class is used in ILP and MLNs, though it can play a role in other logical-reasoning systems.
 */
public class TypeSpec extends AllOfFOPC implements Serializable, Cloneable { // IMPORTANT NOTE: if adding more symbols here, also edit atTypeSpec() in the parser.

	// TODO(hayesall): Enum?

    private final static int unspecifiedMode = -1; // For use when modes aren't needed.
	final static int plusMode      = 1; // An 'input' argument (should be bound when the predicate or function containing this is called).
	public final static int minusMode     = 3; // An 'output' argument - need not be bound.
	private final static int constantMode  = 5; // An argument that should be a constant (i.e., not a variable).

	public Integer mode;    // One of the above, which are used to describe how this argument is to be used.
	public Type    isaType; // Can be "human," "book," etc.  Type hierarchies are user-provided.

	final transient HandleFOPCstrings stringHandler;

	public TypeSpec(char modeAsChar, String typeAsString, HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
		if      (modeAsChar == '+') { mode = plusMode;      }
		else if (modeAsChar == '-') { mode = minusMode;     }
		else if (modeAsChar == '#') { mode = constantMode;  }
		else { Utils.error("Unknown mode character: '" + modeAsChar + "'"); }
		isaType = stringHandler.isaHandler.getIsaType(typeAsString);
	}	
	public static boolean isaModeSpec(char c) { // Also look at FileParser.processTerm
		return c == '+' || c == '-' || c == '#';
	}
	public TypeSpec(Type isaType, HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
		this.mode          = unspecifiedMode;
		this.isaType       = isaType;
	}

	/*
         * Collect those type specifications that are for INPUT arguments. For
         * the other arguments, use 'null' (this way two different
         * specifications such as '(+human,-human,+dog)' and
         * '(-human,+human,-dog)' will be differentiated).
         *
         * @return A list of the argument types for the given predicate specification.
         */
	public static List<Type> getListOfInputArgumentTypes(PredicateSpec fullTypeSpec) {
		List<Type> inputArgumentTypes = new ArrayList<>(1);
		for (TypeSpec spec : fullTypeSpec.getTypeSpecList()) {
			if (spec.mustBeBound()) { inputArgumentTypes.add(spec.isaType); } else { inputArgumentTypes.add(null); }
		}
		return inputArgumentTypes;
	}	
	
    @Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + mode;
		result = prime * result + ((isaType == null) ? 0 : isaType.hashCode());
		return result;
	}	
    @Override
	public boolean equals(Object obj) {
		if (!(obj instanceof TypeSpec)) { return false; }
		TypeSpec typeSpec = (TypeSpec) obj;
		return (mode.equals(typeSpec.mode) && isaType == typeSpec.isaType);
	}

	public boolean mustBeBound() {
		int modeToUse = mode;
		return modeToUse == plusMode;
	}

	public boolean canBeNewVariable() {
		int modeToUse = mode;
		return modeToUse == minusMode;
	}

	public boolean mustBeConstant()	{
		int modeToUse = mode;
		return modeToUse == constantMode;
	}


	public boolean canBeConstant()	{
		int modeToUse = mode;
		return modeToUse == constantMode;
	}

	String getModeString() {
		return getModeString(mode);
	}
	private static String getModeString(int modeToUse) {
		switch (modeToUse) {
			case plusMode:      return "+";
			case minusMode:     return "-";
			case constantMode:  return "#";
			default: Utils.error("Unknown mode type code: '" + modeToUse + "'");
					 return null;
		}		
	}

	@Override
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return getModeString() + isaType;
	}
    @Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return getModeString() + isaType;
	}
	@Override
	public TypeSpec applyTheta(Map<Variable, Term> bindings) {
		return this;
	}

    public Type getType() {
        return isaType;
    }

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}

	public TypeSpec copy() {
		return clone();
	}

    protected TypeSpec clone() {
        try {
            return (TypeSpec) super.clone();
        } catch (CloneNotSupportedException ex) {
            return null;
        }
    }
}
