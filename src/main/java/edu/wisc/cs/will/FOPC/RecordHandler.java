package edu.wisc.cs.will.FOPC;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

//Written by Trevor Walker.

public class RecordHandler {

	private RecordReferenceMap referenceMap;
	private Map<String,RecordList> recordMap = new HashMap<>();
	
	RecordHandler() {
		this.referenceMap = new RecordReferenceMap();
	}

	/** Performs a DB lookup of for the key, unifying Term with the first appropriate entry and updating bindingList.
	 *
	 * This version of recorded does not allow backtracking.  If you need backtracking, use the
	 * recorded version which allows a RecordBacktrackEntry to be provided.
	 * 
	 * @param key DB Key to use
	 * @param Term Term to unify against.  Term will be modified with the appropriate bindings.
	 * @param bindingList BindingList to place unified bindings into
	 * @param u Unifier to use.
	 * @return RecordReference to the record which was unified against.
	 */
	public RecordReference recorded(String key, Term Term, BindingList bindingList, Unifier u) {
		return recorded(key,Term,bindingList,u,null);
	}
	
	/**
	 * Performs a DB lookup of for the key, unifying Term with the first
	 * appropriate entry and updating bindingList. This version allows for
	 * backtracking if a non-null backtrackEntry is provided. Note,
	 * backtracking currently does not support concurrent modification. If
	 * the record db is modified, backtracking will fail.
	 *
	 * @param key
	 *                DB Key to use
	 * @param Term
	 *                Term to unify against. Term will be modified with the
	 *                appropriate bindings.
	 * @param bindingList
	 *                BindingList to place unified bindings into
	 * @param u
	 *                Unifier to use.
	 * @param backtrackEntry
	 *                Entry to track backtracking...
	 * @return RecordReference to the record which was unified against.
	 */
	public RecordReference recorded(String key, Term Term, BindingList bindingList, Unifier u, RecordBacktrackEntry backtrackEntry) {

		RecordReference result = null;
		
		RecordList rl = recordMap.get(key);
		if ( rl != null ) {
			result = rl.recorded(key,Term, bindingList, u, backtrackEntry);
		}
		
		return result;
	}
	
	/** Retrieves an instance from the D.B. based upon the reference.
	 * 
	 * @param recordReference Reference to the record.
	 * @param term Term to unify against
	 * @param bindingList BindingList to fill, should be initially empty, may be modified even under failure
	 * @param u Unifier
	 * @return true if the references was valid and we could unify against term
	 */
	public boolean instance(RecordReference recordReference, Term term, BindingList bindingList, Unifier u) {
		boolean result = false;
		
		RecordList rl = recordMap.get(recordReference.key);
		if ( rl != null && rl.completeEntryList.contains(recordReference.recordEntry)) {
			if ( u.unify(recordReference.recordEntry.term, term, bindingList) != null ) {
				result = true;
			}
		}
		
		return result;
	}
	
	private class RecordList {
		private List<RecordEntry> completeEntryList = new LinkedList<>();
		private Map<Pair<String,Integer>,List<RecordEntry>> predicateNameIndex;
		
		public RecordList() {}

		public RecordReference recorded(String key, Term term, BindingList bindingList, Unifier u, RecordBacktrackEntry backtrackEntry) {
			RecordReference result = null;
			
			Iterator<RecordEntry> recordIterator = null;
			if ( backtrackEntry != null && backtrackEntry.recordIterator != null ) {
				recordIterator = backtrackEntry.recordIterator;
			}
			else {
				recordIterator = getIndexedIteratorForTerm(term);
				
			}
			
			bindingList.theta.clear();
			
			while(recordIterator != null && recordIterator.hasNext()) {
				RecordEntry recordEntry = recordIterator.next();
				Term recordedTerm = recordEntry.term;
				BindingList newList = u.unify(term, recordedTerm, bindingList);
				if ( newList != null ) {
					result = referenceMap.getReference(key, recordEntry);
					break;
				}
			}
			
			if ( result != null && backtrackEntry != null ) {
				backtrackEntry.recordIterator = recordIterator;
			}
			
			return result;
		}

		private Iterator<RecordEntry> getIndexedIteratorForTerm(Term term) {
			
			if ( term instanceof LiteralAsTerm ) {
				if(predicateNameIndex == null) {
					// we have no literals as terms so far, so return null
					return null;
				}
				else {
					LiteralAsTerm lat = (LiteralAsTerm) term;
					Pair<String,Integer> key = new Pair<>(lat.itemBeingWrapped.predicateName.name,lat.itemBeingWrapped.numberArgs());
					List<RecordEntry> records = predicateNameIndex.get(key);
					if ( records == null ) {
						// No records with that name, so return null
						return null;
					}
					else {
						// Return an iterator over the records...
						System.out.println("Iterating over " + records);
						return records.iterator();
					}
				}
			}
			else {
				return completeEntryList.iterator();
			}
		}
	}
	
	private static class Pair<S,T> {
		S s;
		T t;
		
		Pair(S s, T t) {
			this.s = s;
			this.t = t;
		}
		
		public boolean equals(Object that) {
			return s == ((Pair)that).s && t == ((Pair)that).t;
		}
		
		public int hashCode() {
			return (s == null ? 0 : s.hashCode()) + (t == null ? 0 : t.hashCode());
		}
	}
}
