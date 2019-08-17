package edu.wisc.cs.will.FOPC;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

//Written by Trevor Walker.

public class RecordHandler {

	private Map<String,RecordList> recordMap = new HashMap<>();
	
	RecordHandler() {
		new RecordReferenceMap();
	}

	/* Retrieves an instance from the D.B. based upon the reference.
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
	
	private static class RecordList {
		private List<RecordEntry> completeEntryList = new LinkedList<>();
		public RecordList() {}

	}

}
