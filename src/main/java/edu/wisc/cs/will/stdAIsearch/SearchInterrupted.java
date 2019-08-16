package edu.wisc.cs.will.stdAIsearch;

/**
 * If some code wishes to interrupt a search in the middle, it should throw a new instance of this class.
 * @author shavlik
 */
public class SearchInterrupted extends Exception {

	private static final long serialVersionUID = 1L;

	public SearchInterrupted() {}

	public SearchInterrupted(String message) {
		super(message);
	}

	public SearchInterrupted(Throwable cause) {
		super(cause);
	}

	public SearchInterrupted(String message, Throwable cause) {
		super(message, cause);
	}
}
