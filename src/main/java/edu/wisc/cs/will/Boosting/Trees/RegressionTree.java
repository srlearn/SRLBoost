package edu.wisc.cs.will.Boosting.Trees;

import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Sentence;

import java.util.Collection;

public class RegressionTree extends ClauseBasedTree {

	// Meta information about each clause. For e.g. # +ve examples
	// Used for one class classification

	public RegressionTree(WILLSetup setup) {
		super(setup);
	} 

	/*
	 * This function adds the predicates that are used in this tree ie
	 * the parents for the head predicate.
	 * @param preds - Adds the parent predicate to this collection
	 * Duplicate detection is responsibility of the caller
	 */
	public void getParentPredicates(Collection<PredicateName> preds) {
		for (Clause cl : regressionClauses) {

			if (cl == null || cl.negLiterals == null)
				continue;
			// Body literals
			for(Literal lit: cl.negLiterals) {
				if (lit != null) {
					addToPredicates(lit, preds);
				} else {
					preds.add(lit.predicateName);
				}
			}
		}
	}

	private void addToPredicates(Sentence sentenceA,
			Collection<PredicateName> preds) {
		if(sentenceA == null) {
			return;
		}
		for (Literal lit : sentenceA.getNegatedQueryClause().negLiterals) {
			preds.add(lit.predicateName);
		}
	}

}
