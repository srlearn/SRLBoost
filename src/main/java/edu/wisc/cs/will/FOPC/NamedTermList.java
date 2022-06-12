package edu.wisc.cs.will.FOPC;

import java.util.List;

/*
 * Allow a list of arguments to have an accompanying list of names (mainly used for the Bootstrap Learning project, but might have other uses).
 * This is an awkward 'add in' rather than being designed in from scratch, since this is not generally used.
 * 
 * @author shavlik
 */
public class NamedTermList {

    // TODO(hayesall): Probably safe to remove.

	private final List<Term>   terms;

    public NamedTermList(List<Term> terms) {
		this.terms = terms;
	}

	public List<Term> getTerms() {
		return terms;
	}
}
