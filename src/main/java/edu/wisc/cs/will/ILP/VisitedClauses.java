package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.ClosedList;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

import java.util.*;
import java.util.Map.Entry;

/*
 * @author shavlik
 * 
 * TODO pull out the generic part of this and then specialize for SearchNodes
 *
 */
public class VisitedClauses extends ClosedList {
	private final LiteralComparator literalComparator; // Only need one of these even if many instances, but for safety give each instance its own since the space needed is trivial (only one comparator per ILP search).
	private final Map<Integer,Map<PredicateName,List<List<Literal>>>> canonicalClauses; // Index first on total number of args (dont bother to recur into any functions) + 97 * length.  Then hash on the predicate of the last literal.
	private int    size    =  0; // Count how many items are in this CLOSED.
	private int    maxSize = -1; // If size gets close to this, then 1-fractionToKeep of the items are randomly deleted.  A non-pos value means "do not prune CLOSED."
	private final double fractionToKeep = 0.75; // When CLOSED reaches 90% of its maxSize, discard 25% of the items (which means it will be be about 2/3rds full).
	private final BindingList tempBindings;

	/*
	 * 
	 * Need a way to put visited clauses in a (quasi)canonical form.  It is ok if there are a few 'false negatives' - ie, ok to revisit 
	 * a clause since that only wastes CPU time.  However, there should not be any 'false positives,' since in that case a good clause
	 * might have been discarded.
	 * 
	 * Current Design
	 * 	sort the literals in the clause (including the head though that might not be necessary)
	 *  see if variants
	 */
	private VisitedClauses() {
		literalComparator = new LiteralComparator();
		canonicalClauses  = new HashMap<>(64);
		tempBindings      = new BindingList();
	}
	VisitedClauses(int maxSize) {
		this();
		this.maxSize = maxSize;		
	}

	private void reduceSize(double fraction) { // Reduce the size to about this fraction of its current size.
		if (fraction <= 0.0) { emptyClosedList(); return; } // Negative fractions interpreted as 'clear all.'
		if (fraction >= 1.0) { return; }
		
		int countIter1removes = 0;
		// Walk through the hash maps and random discard some literals.
		Set< Entry<Integer,Map<PredicateName,List<List<Literal>>>>> entrySet1 = canonicalClauses.entrySet();
		for (Entry<Integer,Map<PredicateName,List<List<Literal>>>>  entry1 : entrySet1) {
			Map<      PredicateName,List<List<Literal>>>   hashObj1   = entry1.getValue(); // TODO(?) delete this comment if no errors for awhile [8/1/08]  canonicalClauses.get(primaryKey);
			Set<Entry<PredicateName,List<List<Literal>>>>  entrySet2  = hashObj1.entrySet();

			for (Entry<PredicateName, List<List<Literal>>> entry2 : entrySet2) {
				PredicateName       secondaryKey = entry2.getKey();
				List<List<Literal>> storedItems  = hashObj1.get(secondaryKey);
				Iterator<List<Literal>> iter     = storedItems.iterator();
				while (iter.hasNext()) if ( Utils.random() > fractionToKeep) {
					iter.next();
					iter.remove();
					size--;
					countIter1removes++;
				}
			}
		}
		if (countIter1removes > 0) { removeEmptyPortions(); } // Do some garbage collection (ie, remove portions of CLOSED that contain no literal lists.
	}
	
	private void removeEmptyPortions() {
		// Walk through the hash maps and discard if nothing underneath.
		Set<     Entry<Integer,Map<PredicateName,List<List<Literal>>>>> entrySet1 = canonicalClauses.entrySet();
		Iterator<Entry<Integer,Map<PredicateName,List<List<Literal>>>>> iter1     = entrySet1.iterator();

		while (iter1.hasNext()) {
			boolean                                            discardIter1 = true; // See if anything found underneath.
			Set<     Entry<PredicateName,List<List<Literal>>>> entrySet2    = iter1.next().getValue().entrySet();
			Iterator<Entry<PredicateName,List<List<Literal>>>> iter2        = entrySet2.iterator();
			
			while (iter2.hasNext()) {
				 List<List<Literal>> literals = iter2.next().getValue();
				 
				 if (Utils.getSizeSafely(literals) < 1) { iter2.remove();
				 }
				 else if (discardIter1) { discardIter1 = false; } // Found something so don't discard iter1.
			}
			if (discardIter1) { iter1.remove();
			}
		}
	}
	
	private List<Literal> createCanonicalClause(SingleClauseNode clauseNode) {		
		if (clauseNode.canonicalForm != null) { return clauseNode.canonicalForm; }
		
		HandleFOPCstrings stringHandler = ((LearnOneClause) clauseNode.task).stringHandler;
		List<Literal>     literals      = clauseNode.getClauseBodyReversed();
		Literal           head          = clauseNode.getClauseHead();
		literals.add(head);
		List<Literal>     newLiterals   = createCanonicalClause(stringHandler, literals);
		clauseNode.canonicalForm = newLiterals;
		return newLiterals;
	}
	private List<Literal> createCanonicalClause(HandleFOPCstrings stringHandler, Clause clause) {
		List<Literal> literals = new ArrayList<>(1);
		if (clause.posLiterals != null) { literals.addAll(clause.posLiterals); }
		if (clause.negLiterals != null) { literals.addAll(clause.negLiterals); }
		return createCanonicalClause(stringHandler, literals);
	}
	private List<Literal> createCanonicalClause(HandleFOPCstrings stringHandler, List<Literal> literals) {
		if (literals == null) { return null; }
		List<Literal> newLiterals = new ArrayList<>(Utils.getSizeSafely(literals));

		stringHandler.pushVariableHash(); // Want to have all new variables in these.
		for (Literal lit : literals) { newLiterals.add(lit.copy(true)); }
		stringHandler.popVariableHash();
		newLiterals.sort(literalComparator);
		return newLiterals;
	}
	
	// Create a hashcode by walking through a list of literals.
	private Integer getPrimaryKey(List<Literal> literals) {
		int count = 0;
		
		if (literals == null) { return 0; }
		for (Literal lit : literals) { 
			List<Term> terms = lit.getArguments();
			
			if (terms != null) {
				if (count > Integer.MAX_VALUE / 2) { count -= Integer.MAX_VALUE / 2; } // Play it safe to watch for integer overflow.
				if (Utils.getSizeSafely(terms) > 0) { 
					Term term1 = terms.get(0); 
					count += 91 * terms.size() + (term1 == null ? 0 
																: (term1 instanceof Variable ? 1 
																							 : (term1 instanceof Function ? ((Function) term1).functionName.hashCode() / 3 // Don't want to count any variables in here.
																									 				      : term1.hashCode() / 3))); // Include the first term's hashcode, unless it is a variable (due to renaming of vars).
				}
				count += lit.predicateName.hashCode() / 5;  // The 91 (above) is some prime so that the sizes don't "synch with" hashcode's of adjacent predicateNames'.  The "divide by X's" are intended to help protect from int overflow.
			}
		}
		return count;
	}
	
	private PredicateName getSecondaryKey(List<Literal> literals) {
		if (literals == null) { return null; } // Or do we need to return some actual PredicateName here?
		return (literals.get(literals.size()/2).predicateName); // Get the middle literal's predicate name.
	}
	
	public void addNodeToClosed(SearchNode node)  // Assume that this node's literals are not already in CLOSED (i.e., be sure to check elsewhere).
	{	SingleClauseNode clauseNode = (SingleClauseNode) node;
		List<Literal>    literals   = createCanonicalClause(clauseNode);
		addListOfLiteralsToClosed(literals);
	}
	void addClauseToClosed(HandleFOPCstrings stringHandler, Clause clause) {
		List<Literal>    literals   = createCanonicalClause(stringHandler, clause);
		addListOfLiteralsToClosed(literals);
	}

	private void addListOfLiteralsToClosed(List<Literal> literals) {
		Integer          primaryKey   = getPrimaryKey(  literals);
		PredicateName    secondaryKey = getSecondaryKey(literals);
		Map<PredicateName,List<List<Literal>>> hashObj1 = canonicalClauses.get(primaryKey);		

		size++;
		if (maxSize > 0 && maxSize - size < maxSize / 10) { reduceSize(fractionToKeep); }  // Reduce if within 10% of full.
		if (hashObj1 == null) { // No items yet with this primary key.
			List<List<Literal>> newSecondaryObject = new ArrayList<>(8);  // Create a new entry.
			newSecondaryObject.add(literals);
			Map<PredicateName,List<List<Literal>>> newPrimaryObject = new HashMap<>(8);
			newPrimaryObject.put(secondaryKey, newSecondaryObject);
			canonicalClauses.put(primaryKey,   newPrimaryObject);
			return;
		}
		List<List<Literal>> hashObj2 = hashObj1.get(secondaryKey);
		if (hashObj2 == null) { // No items yet with this secondary key.
			List<List<Literal>> newObject = new ArrayList<>(8);  // Create a new entry.
			newObject.add(literals);
			hashObj1.put(secondaryKey,newObject);
		}
		else { // Already have some entries for these two keys, so make a list.
			hashObj2.add(literals);
		}
	}
	
	private boolean variantClauses(List<Literal> list1, List<Literal> list2) {
		int counter = 0; // Should do a double for loop, but this code is more readable and the lengths should be short.
		tempBindings.theta.clear(); // Reuse this memory and save a 'new.'
		BindingList bindings = tempBindings;
		int size1 = Utils.getSizeSafely(list1);
		int size2 = Utils.getSizeSafely(list2);
		if (size1 < 1 && size2  < 1) { return true;  }
		if (size1     != size2)      { return false; } // The caller already checked for size, but this is an easy way to see if ONE list equals null.
		for (Literal lit : list1) {
			bindings = lit.variants(list2.get(counter++), bindings);
			if (bindings == null) { return false; }
		}
		return true;
	}
	
	public boolean alreadyInClosedList(SearchNode node)
	{	SingleClauseNode clauseNode = (SingleClauseNode) node;
		List<Literal>    literals   = createCanonicalClause(clauseNode);
		List<Literal>    oldLits    = alreadyInClosedList(literals);
		return oldLits != null;
	}

	private List<Literal> alreadyInClosedList(List<Literal>    literals) {
		Integer          primaryKey   = getPrimaryKey(  literals);
		PredicateName    secondaryKey = getSecondaryKey(literals);
		Map<PredicateName,List<List<Literal>>> hashObj1 = canonicalClauses.get(primaryKey);
		
		// Pass in a clauseNode if these need to be turned on
		
		if (hashObj1 == null) {
			return null;
		}
		
		List<List<Literal>> hashObj2 = hashObj1.get(secondaryKey);

		if (hashObj2 == null) {
			return null;
		}
		
		int count = Utils.getSizeSafely(literals);
		for (List<Literal> prevLiterals : hashObj2) {
			if (count != Utils.getSizeSafely(prevLiterals)) {  continue; } // Can't match if not same number of literals.
			if (variantClauses(literals, prevLiterals)) {
				return prevLiterals;
			}
		}
		return null;
	}

	public void emptyClosedList() {
		size = 0;
		if (canonicalClauses != null) { canonicalClauses.clear(); }		
	}

	public String toString() {
		StringBuilder result = new StringBuilder();
		// Walk through the hash maps and random discard some literals.
		Set< Entry<Integer,Map<PredicateName,List<List<Literal>>>>> entrySet1 = canonicalClauses.entrySet();
		for (Entry<Integer,Map<PredicateName,List<List<Literal>>>>  entry1 : entrySet1) {
			Map<               PredicateName,List<List<Literal>>>   hashObj1   = entry1.getValue(); // TODO(?) delete this comment if no errors for awhile [8/1/08]  canonicalClauses.get(primaryKey);
			Set<Entry<         PredicateName,List<List<Literal>>>>  entrySet2  = hashObj1.entrySet();
			
			for (Entry<        PredicateName, List<List<Literal>>> entry2 : entrySet2) {
				PredicateName       secondaryKey = entry2.getKey();
				List<List<Literal>> storedItems  = hashObj1.get(secondaryKey);

				for (List<Literal> storedItem : storedItems) {
					result.append("%     ").append(storedItem).append("\n");
				}
			}
		}
		return result.toString();
	}

}
