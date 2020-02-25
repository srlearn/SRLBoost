package edu.wisc.cs.will.FOPC;

import java.util.Comparator;

/*
 * Create a pair of a term and its name.
 * 
 * @author shavlik
 *
 */
class NamedTerm {
	public final Term   term;
	public final String name;
	
	public static final Comparator<NamedTerm> comparator = new NamedTermComparator();
	
	NamedTerm(Term term, String name) {
		super();
		this.term = term;
		this.name = name;
	}	
	
	public String toString() {
		return term + "=" + name;
	}
	
	private static final String nameField          = "name";
	static final String worldNameField     = "wiWorld"; // These are used for situation calculus.
	static final String stateNameField     = "wiState";
	static final String returnedValueField = "value"; // Do NOT use 'returnValue' here since that is treated specially in IL.

    static class NamedTermComparator implements Comparator<NamedTerm> {

		NamedTermComparator() {}

		public int compare(NamedTerm o1, NamedTerm o2) {
			// TODO(@hayesall): Suspicious to return `(o1 == o2)` before the null check.

			if (o1 == o2) { return 0;}

			assert o2 != null;
			assert o1 != null;

			if (o1.name == null && o2.name == null ) { return 0; }
			if (o1.name == null) { return 1; }
			if (o2.name == null) { return -1; }

			if (o1.name.equalsIgnoreCase(NamedTerm.nameField))      { return -1; } // Always keep NAME in the first field.
			if (o2.name.equalsIgnoreCase(NamedTerm.nameField))      { return  1; }
			if (o1.name.equalsIgnoreCase(NamedTerm.worldNameField)) { return -1; } // The WORLD goes second.
			if (o2.name.equalsIgnoreCase(NamedTerm.worldNameField)) { return  1; }
			if (o1.name.equalsIgnoreCase(NamedTerm.stateNameField)) { return  1; } // The STATE goes at the END.
			if (o2.name.equalsIgnoreCase(NamedTerm.stateNameField)) { return -1; }
			if (o1.name.equalsIgnoreCase(NamedTerm.returnedValueField))  { return  1; }  // The returnValue goes second from last.
			if (o2.name.equalsIgnoreCase(NamedTerm.returnedValueField))  { return -1; }
			return o1.name.compareToIgnoreCase(o2.name);
		}

	}
}
