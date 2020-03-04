package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import edu.wisc.cs.will.Utils.Utils;

import java.io.ObjectStreamException;
import java.io.Serializable;

/*
 * @author shavlik
 */
public class NumericConstant extends Constant implements Serializable {

    public Number value;

    // TODO(@hayesall): A comment previously suggested that case: 2 in this file is unused.

    private int type;

    private NumericConstant() {
    }

    // DON'T CALL THESE DIRECTLY.  GO VIA HandleFOPCstrings.
    NumericConstant(HandleFOPCstrings stringHandler, Number value, int type, TypeSpec typeSpec) {
    	this();
        this.stringHandler = stringHandler;
        this.value = value;
        this.setType(type);
        this.setTypeSpec(typeSpec);
    }

    public String getName() {
        switch (getType()) {
            case 0:
                return Integer.toString(value.intValue());
            case 3:
                return Long.toString(value.longValue());
            case 1:
                return Double.toString(value.doubleValue());
            case 2:
                return Float.toString(value.floatValue());
            default:
                Utils.error("Have a numeric constant whose type is undefined: " + this);
                return null;
        }
    }

    private void setType(int type) {
        this.type = type;
    }

    private int getType() {
        return type;
    }

    boolean isaInteger() {
        return getType() == 0;
    }

    boolean isaDouble() {
        return getType() == 1;
    }

    boolean isaFloat() {
        return getType() == 2;
    }

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        if (!(that instanceof NumericConstant)) {
            return null;
        }

        NumericConstant numericConstant = (NumericConstant) that;

        return (value.equals(numericConstant.value) ? bindings : null);
    }

    @Override
    public boolean freeVariablesAfterSubstitution(BindingList theta) {
        return false;
    }

    @Override
    public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
        return toString(precedenceOfCaller, bindingList);
    }

    @Override
    protected String toString(int precedenceOfCaller, BindingList bindingList) {
        return getName();
    }

    /*
     * Replace with the cached version from stringHandler.
     */
    private Object readResolve() throws ObjectStreamException {
        if (type == 0) {
            return stringHandler.getNumericConstant(typeSpec, value.intValue());
        }
        else if (type == 1) {
            return stringHandler.getNumericConstant(typeSpec, value.doubleValue());
        }
        else if (type == 2) {
            return stringHandler.getNumericConstant(typeSpec, value.floatValue());
        }
        else if (type == 3) {
            return stringHandler.getNumericConstant(typeSpec, value.longValue());
        }
        else {
            throw new ObjectStreamException("Unknown NumberConstant type encountered: " + type) {
            };
        }
    }

    @Override
    public <Return, Data> Return accept(TermVisitor<Return, Data> visitor, Data data) {
        return visitor.visitNumericConstant(this);
    }

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}
}
