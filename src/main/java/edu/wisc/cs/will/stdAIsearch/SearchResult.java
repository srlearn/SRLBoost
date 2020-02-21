package edu.wisc.cs.will.stdAIsearch;

import java.io.Serializable;

/*
 * Collects the information of interest from a search (e.g., best node found).
 * @author shavlik
 */
public class SearchResult implements Serializable {

	private static final long serialVersionUID = 1L;

	private final boolean goalFound;

	private final String reason;

	SearchResult(boolean goalFound, String reason) {
		this.goalFound = goalFound;
		this.reason = reason;
	}
	
	public boolean goalFound() {
		return goalFound;
	}
	
	public String toString() {
		if (goalFound) {
			return "Search ended successfully.  "   + reason;
		}
		else {
			return "Search ended unsuccessfully.  " + reason;
		}
	}
}
