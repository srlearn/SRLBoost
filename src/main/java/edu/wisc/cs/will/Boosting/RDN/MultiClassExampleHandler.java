package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author tkhot
 */
class MultiClassExampleHandler {

	/*
	 * Use a list for class arg index since more than one argument (combined) may be a class arg.
	 * E.g. genderAndGenre(person, gender!, genre!).
	 */
	private Map<String, List<Integer>> predicateToClassArgIndex ;

	Map<String, ConstantLookupList> constantsForPredicate;
	
	MultiClassExampleHandler() {
		constantsForPredicate = null;
	}

	/*
	 * Initialize the class argument location for every predicate
	 */
	void initArgumentLocation(WILLSetup setup) {
		predicateToClassArgIndex = new HashMap<>();

		for (PredicateNameAndArity pnaa : setup.getHandler().getKnownModes()) {
			String predName = pnaa.getPredicateName().name;
			if (predicateToClassArgIndex.containsKey(predName)) {
				Utils.error("Already seen predicate name: " + predName);
			}
			List<Integer> classArg = new ArrayList<>();
			// For each pred spec

			for (PredicateSpec pspec : pnaa.getPredicateSpecs()) {
				// For each argument
				for (int i = 0; i < pspec.getTypeSpecList().size(); i++) {
					TypeSpec tspec = pspec.getTypeSpec(i);
					if (tspec.truthCounts == 1) {
						classArg.add(i);
					}
				}
			}
			
			if (classArg.size() > 0 ) {
				Utils.println("Setting class args for " + predName + " to: " + Utils.toString(classArg, ","));
				predicateToClassArgIndex.put(predName, classArg);
			}
			
		}
	}

	void addConstantsFromLiterals(List<? extends Literal> facts) {
		if (constantsForPredicate == null) {
			constantsForPredicate = new HashMap<>();
		}
		
		for (Literal lit : facts) {
			String pName = lit.predicateName.name;
			// If it has class args
			if (predicateToClassArgIndex.containsKey(pName)) {
				List<Term> constList = getConstantList(lit);
				// Add constants
				if (!constantsForPredicate.containsKey(pName)) {
					constantsForPredicate.put(pName, new ConstantLookupList());
				}
				constantsForPredicate.get(pName).addConstant(new ArgumentList<>(constList));
			}
		}
	}

	private List<Term> getConstantList(Literal lit) {
		List<Term> constList = new ArrayList<>();
		String pName = lit.predicateName.name;
		for (Integer index : predicateToClassArgIndex.get(pName)) {
			constList.add(lit.getArgument(index));
		}
		return constList;
	}


	int numConstantsForPredicate(String predicate) {
		ConstantLookupList cll =  constantsForPredicate.get(predicate);
		if (cll == null) {
			return 2;
		}
		return cll.size();
	}
	
	
	public static class ConstantLookupList {

		private final static String startList = "{";
		private final static String endList = "}";
		private final static String startTermList = "(";
		private final static String endTermList = ")";
		private final static String startTerm = "\"";
		private final static String endTerm = "\"";
		
		ConstantLookupList() {
			this.constants = new ArrayList<>();
			this.constantIndex = new HashMap<>();
		}

		int size() {
			return constants.size();
		}
		private final List<ArgumentList<Term>> constants ;
		
		private final Map<ArgumentList<Term>, Integer> constantIndex;
		
		void addConstant(ArgumentList<Term> addThis) {
			if (!constantIndex.containsKey(addThis)) {
				int index = constants.size();
				constants.add(addThis);
				constantIndex.put(addThis, index);
				Utils.println("Adding constant: " + Utils.toString(addThis, ","));
			}
		}

		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append(startList);
			for (ArgumentList<Term> termList : constants) {
				sb.append(startTermList);
				for (Term term : termList) {
					sb.append(startTerm);
					sb.append(term.toString());
					sb.append(endTerm);
				}
				sb.append(endTermList);
			}
			sb.append(endList);
			return sb.toString();
		}
	}

	static class ArgumentList<T> extends ArrayList<T> {

		private static final long serialVersionUID = 5435503324007711494L;

		ArgumentList(Collection<? extends T> c) {
			super(c);
		}

		@Override
		public int hashCode() {
			int code = 0;
			int prime = 31;
			for (T item : this) {
				code += prime * item.hashCode();
			}
			return code;
		} 
		
		@Override 
		public boolean equals(Object other) {
			if (!(other instanceof ArgumentList<?>)) {
				return false;
			}
			ArgumentList<T> otherList = (ArgumentList<T>)other;
			if (otherList.size() != this.size()) {
				return false;
			}
			for (int i = 0; i < this.size(); i++) {
				T item1 = this.get(i);
				T item2 = otherList.get(i);
				if (!item1.equals(item2)) {
					return false;
				}
			}
			return true;
		}
	}
}
