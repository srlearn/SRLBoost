package edu.wisc.cs.will.FOPC;

//Written by Trevor Walker.

public class RecordEntry {
	Term term;
	
	private int hashCode;

	public String toString() {
		return term.toString();
	}
	
	public boolean equals(Object that) {
		return this == that;
	}
	
	public int hashCode() {
		return hashCode;
	}
}
