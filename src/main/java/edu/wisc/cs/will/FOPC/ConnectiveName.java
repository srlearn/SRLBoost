package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.io.IOException;
import java.io.Serializable;
import java.util.Map;

/*
 * @author shavlik
 *
 *  All functions with the same name map to the same instance. 
 */
public class ConnectiveName extends AllOfFOPC implements Serializable { // If items are added here, add them to HandleFOPCstrings as well.
	
    private final static String ANDalt0        = "AND";
	private final static String ANDalt1        = "^";
	private final static String ANDalt2        = "&";
	private final static String ANDalt3        = ",";
	private final static String ORalt0         = "OR";
	private final static String ORalt1         = "v";
	private final static String ORalt2         = "|";
	private final static String ORalt3         = "ELSE";
	private final static String NOTalt0        = "NOT";
	private final static String NOTalt1        = "~";
	private final static String NOTalt2        = "\\+";
	private final static String IMPLIESalt0    = "=>";
	private final static String IMPLIESalt1    = "->";
	private final static String IMPLIESalt2    = "IMPLIES";
	private final static String IMPLIESalt3    = ":-"; // This is what Prolog uses.  THESE NEED TO BE IN isaBackwardsIMPLIES().
	private final static String IMPLIESalt4    = ":="; // And allow these two variants.
	private final static String IMPLIESalt5    = "IF";
	private final static String EQUIVALENTalt0 = "<=>";
	private final static String EQUIVALENTalt1 = "<->";
	private final static String EQUIVALENTalt2 = "EQUIVALENT";
	private final static String SPECIAL        = "THEN";
	
	private final static String LogicalAND     = "LogicalAnd";
	private final static String LogicalOR      = "LogicalOr";
	private final static String LogicalNOT     = "LogicalNot";

    public final static ConnectiveName AND     = new ConnectiveName(ANDalt0);
    final static ConnectiveName OR      = new ConnectiveName(ORalt0);
    public final static ConnectiveName NOT     = new ConnectiveName(NOTalt0);

	public final String name;

	ConnectiveName(String name) { // This is protected because getConnectiveName(String name) should be used instead.
		this.name = name;
	}

	public static boolean isaAND(String str) {
		return (   str.equalsIgnoreCase(ConnectiveName.ANDalt0) || str.equalsIgnoreCase(ConnectiveName.ANDalt1) || str.equalsIgnoreCase(ConnectiveName.ANDalt2) || str.equalsIgnoreCase(ConnectiveName.ANDalt3) || str.equalsIgnoreCase(ConnectiveName.LogicalAND));
	}
	public static boolean isaOR(String str) {
		return (   str.equalsIgnoreCase(ConnectiveName.ORalt0)  || str.equalsIgnoreCase(ConnectiveName.ORalt1)  || str.equalsIgnoreCase(ConnectiveName.ORalt2)  ||  str.equalsIgnoreCase(ConnectiveName.ORalt3) || str.equalsIgnoreCase(ConnectiveName.LogicalOR));
	}
	public static boolean isaNOT(String str) {
		return (   str.equalsIgnoreCase(ConnectiveName.NOTalt0) || str.equalsIgnoreCase(ConnectiveName.NOTalt1) || str.equalsIgnoreCase(ConnectiveName.NOTalt2) || str.equalsIgnoreCase(ConnectiveName.LogicalNOT));
	}
	static boolean isaIMPLIES(String str) {
		return (   str.equalsIgnoreCase(ConnectiveName.IMPLIESalt0)    || str.equalsIgnoreCase(ConnectiveName.IMPLIESalt1)    || str.equalsIgnoreCase(ConnectiveName.IMPLIESalt2)
				|| str.equalsIgnoreCase(ConnectiveName.IMPLIESalt3)|| str.equalsIgnoreCase(ConnectiveName.IMPLIESalt4)    || str.equalsIgnoreCase(ConnectiveName.IMPLIESalt5));
	}
	static boolean isaBackwardsIMPLIES(String str) {
		return (   str.equalsIgnoreCase(":-") || str.equalsIgnoreCase("if") || str.equalsIgnoreCase(":="));
	}
	static boolean isaEQUIVALENT(String str) {
		return (   str.equalsIgnoreCase(ConnectiveName.EQUIVALENTalt0) || str.equalsIgnoreCase(ConnectiveName.EQUIVALENTalt1) || str.equalsIgnoreCase(ConnectiveName.EQUIVALENTalt2));
	}
	private static boolean isaSPECIAL(String str) {
		return (   str.equalsIgnoreCase(ConnectiveName.SPECIAL) );
	}
	
	private static boolean sameConnective(ConnectiveName a, ConnectiveName b) {
        if ( a.name.equals(b.name) ) return true;
		if (isaAND(       a.name)) { return isaAND(       b.name); }
		if (isaOR(        a.name)) { return isaOR(        b.name); }
		if (isaNOT(       a.name)) { return isaNOT(       b.name); }
		if (isaIMPLIES(   a.name)) { return isaIMPLIES(   b.name); }
		if (isaEQUIVALENT(a.name)) { return isaEQUIVALENT(b.name); }
		if (isaSPECIAL(   a.name)) { return isaSPECIAL(   b.name); }
		Utils.error("Unknown connectives: << '" + a + "' << and '" + b + "'");
		return false;
	}

    boolean isSameConnective(ConnectiveName that) {
        return sameConnective(this, that);
    }
	
	public static boolean isaConnective(String str) {
		return ( isaAND(str) || isaOR(str) || isaNOT(str) || isaIMPLIES(str) || isaEQUIVALENT(str) || isaSPECIAL(str) );
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return name;
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return name;
	}

    /* Substitutes the ConnectiveName with a SerializableConnectiveName while Serializing.
     */
    private Object writeReplace() {
        return new SerializableConnectiveName(name);
    }

	/* This is a little hack to allow the Type to be canonicalized by the string handler.
     *
     * We want to use readResolve to canonicalize the Type object.  However, when we
     * run readResolve, we don't have the InputStream.  No inputStream, no string handler.
     * So, we serialize this little stub class which has a variable to temporarily hold
     * the string handler.
     *
     * This call will then use the readResolve method to fix up the stream.
     */
    static class SerializableConnectiveName implements Serializable {

        final String name;

        transient HandleFOPCstrings stringHandler;

        SerializableConnectiveName(String name) {
            this.name = name;
        }

        /* Methods for reading a Object cached to disk.
         */
        private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
            if (!(in instanceof FOPCInputStream)) {
                throw new IllegalArgumentException(ConnectiveName.class.getName() + ".readObject input stream must support FOPCObjectInputStream interface");
            }

            in.defaultReadObject();

            FOPCInputStream fOPCInputStream = (FOPCInputStream) in;

            this.stringHandler = fOPCInputStream.getStringHandler();
        }

        public Object readResolve() {
            // Canonicalize the object via the string handler...
            return stringHandler.getConnectiveName(name);
        }
    }

	@Override
	public ConnectiveName applyTheta(Map<Variable,Term> bindings) {
		return this;
	}
	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}

}