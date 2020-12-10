package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;

/*
 * @author shavlik
 *
 */
public class StringConstant extends Constant implements Serializable {
    private String name = null;

    private boolean alwaysUseDoubleQuotes = false;

    private StringConstant() {
        checkIfQuoteMarksNeeded();  // 'name' not set, so don't need this, but keep it in case we later change the code.
    }

    StringConstant(HandleFOPCstrings stringHandler, String name, boolean alwaysUseDoubleQuotes, TypeSpec typeSpec) {
    	this();
    	this.name = name; // DON'T CALL THESE DIRECTLY.  GO VIA HandleFOPCstrings.
        while (name != null && name.length() > 1 && name.charAt(0) == '"' && name.charAt(name.length() - 1) == '"' ) { 
        	name = name.substring(1, name.length() - 1);  // We'll add these back on if needed.
        }
        this.stringHandler = stringHandler;
        this.setTypeSpec(typeSpec);
        if (name != null && name.equalsIgnoreCase("-inf")) {
            Utils.error("Where did this come from? ");
        }
        this.alwaysUseDoubleQuotes = alwaysUseDoubleQuotes;
        if (!alwaysUseDoubleQuotes) { checkIfQuoteMarksNeeded(); }
    }

    public boolean freeVariablesAfterSubstitution(BindingList theta) {
        return false;
    }

    private String toTypedString() {
        String end = (typeSpec != null ? typeSpec.getCountString() : "");
        assert typeSpec != null;
        if (name == null) {
            return typeSpec.getModeString() + typeSpec.isaType.typeName + end;
        } // Sometimes anonymous string constants are used (e.g., to pass around typeSpec's).
        String nameToUse = getName();
        return (typeSpec != null ? typeSpec.getModeString() + typeSpec.isaType.typeName + ":" + nameToUse + end : nameToUse + end);
    }
    
    private void checkIfQuoteMarksNeeded() { 
    	alwaysUseDoubleQuotes     = false;
    	boolean containsNonNumber = false;
        if (name != null) for (int i = 0; i < name.length(); i++) {
        	char chr = name.charAt(i);
        	if (!(Character.isLetterOrDigit(chr) || (i > 0 && chr == '_'))) {// Should we quote if the FIRST char is a digit?
        		alwaysUseDoubleQuotes = true; // CHECK IF CHAR IS ONE THAT FileParser's tokenizer does not handle.
        		break; 
        	} else if (chr >= '\u00AA' && chr <= '\u00FF') { // SOME THINGS WERE SLIPPING THROUGH (eg, Beioncé), SO DO THIS      DONT DO THIS BOTH HERE AND IN StreamTokenizeTAW (though not harmful - would just add more quote marks than are necessary).
        		alwaysUseDoubleQuotes = true;
        		break;
        	}
        	if (!containsNonNumber && Character.isLetter(chr)) { containsNonNumber = true; }
        } 
        if (!containsNonNumber) { alwaysUseDoubleQuotes = true; } // If something was a string of numbers, we want it quoted (for later parsing as a StringConstant rather than as a NumericConstant).
    }

    public String getName() {
    	String safeName = makeSureNameIsSafe(name);
        assert safeName != null;
        if (safeName.isEmpty()) { return "\"\""; } // Need something here so the string can be 'seen' (e.g., parsed back in).
    	if (safeName.length() >  1 && safeName.charAt(0) == '"' && safeName.charAt(safeName.length() - 1) == '"') { return safeName; } // Already quoted.
    	if (safeName.length() == 1 && safeName.charAt(0) == '"')  { return '"' + '\\' + safeName + '"'; }
    	if (safeName.length() == 1 && safeName.charAt(0) == '\'') { return '"' +        safeName + '"'; } // This line might not be needed.
        return (stringHandler.isaConstantType(name)
                ? (alwaysUseDoubleQuotes ? '"' + safeName + '"' : safeName)
                : '"' + safeName + '"'); // Need to override by quoting.  Note that if safeName started with quote marks, it would have been caught above.
    }

    /* Returns the name without any quoting or escaping of characters.
     *
     * Sometime we need the name of a StringConstant without the quoting
     * and escaping of characters.  This is necessary when we are going to
     * do custom printing (aka the PrettyPrinter) or when we want to do
     * processing of the name prior to quoting.
     */
    public String getBareName() {
        return name;
    }

    private static String makeSureNameIsSafe(String name) {
        if (name == null) { return null; }
    	if (name.isEmpty()) { return name; }
    	
    	StringBuilder    result = new StringBuilder(name.length());
    	boolean startsWithQuote = false, endsWithQuote = false;
    	if (name.charAt(0)                 == '"') { startsWithQuote = true; }
    	if (name.charAt(name.length() - 1) == '"') {   endsWithQuote = true; }    	
    	
    	if (startsWithQuote && endsWithQuote) { result.append('"');  }
    	else if (startsWithQuote)             { result.append('\\').append('"'); } // Seems more readable than using :  result.append("\\\"");

		boolean nextCharEscaped = false;
    	for (int i = (startsWithQuote ? 1 : 0); i < name.length() - (endsWithQuote ? 1 : 0); i++) {
    		char chr = name.charAt(i);
    		// For quotes
    		if (chr == '"') {
    			// If prev character wasn't \, escape it
    			if (!nextCharEscaped) {
    				result.append('\\');
    			} 
    		} 
    		if (chr != '"' && chr != '\\') {
    			// A character apart from " was escaped=> add an extra slash
    			// Handle's cases such as \n, \t
    			if (nextCharEscaped) {
    				result.append('\\');
    			}
    		}
    		if (chr =='\\') {
    			// If there is a slash before, already escaped but the next character is not
                // The next character is escaped by this slash
                nextCharEscaped = !nextCharEscaped;
    		} else {
    			// Set this to false for any other character
    			nextCharEscaped = false;
    		}

    		result.append(chr);
    	}
    	// The string may end with a slash.
    	if (nextCharEscaped) { result.append('\\'); }
    	
    	if (startsWithQuote && endsWithQuote) { result.append('"');  }
    	else if (endsWithQuote)               { result.append('\\').append('"'); }

    	return result.toString();
    }

    public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
        return toString(precedenceOfCaller, bindingList);
    }

    protected String toString(int precedenceOfCaller, BindingList bindingList) {
        if (stringHandler.printTypedStrings) {
            return toTypedString();
        }
        String prefix = "";
        if (name == null) {
            if (typeSpec == null) {
                Utils.error("Have a stringConstant with name=null and typeSpec=null");
            }
            return prefix + typeSpec.getModeString() + typeSpec.isaType.typeName + typeSpec.getCountString();  // Sometimes anonymous string constants are used (e.g., to pass around typeSpec's).
        }
        if (stringHandler.doVariablesStartWithQuestionMarks()) {
            if (!alwaysUseDoubleQuotes && name.charAt(0) == '?') {
                Utils.error("How did a variable get into a constant? " + getName());
            }
            return prefix + getName();
        }
        return prefix + getName();
    }

    public Clause asClause() {
        return stringHandler.getClause(stringHandler.getLiteral( stringHandler.getPredicateName(name)), true);
    }
    @Override
    public Sentence asSentence() {
        return stringHandler.getLiteral(stringHandler.getPredicateName(name));
    }

    @Override
    public Literal asLiteral() {
        return stringHandler.getLiteral( stringHandler.getPredicateName(name));
    }

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        if (!(that instanceof StringConstant)) {
            return null;
        }

        StringConstant stringConstant = (StringConstant) that;

        if (!this.name.equals(stringConstant.name)) {
            return null;
        }

        return bindings;
    }

    /* Replace with the cached version from stringHandler.
     */
    private Object readResolve() {
        return stringHandler.getStringConstant(typeSpec, name, true);
    }

    @Override
    public <Return, Data> Return accept(TermVisitor<Return, Data> visitor, Data data) {
        return visitor.visitStringConstant(this);
    }
}
