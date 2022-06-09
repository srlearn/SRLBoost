package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.ResThmProver.HornClausebase;
import edu.wisc.cs.will.Utils.Utils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class InlineManager {

	private final HandleFOPCstrings  stringHandler;
	private final HornClausebase     hornClauseKnowledgeBase;
	
	private final PredicateName      notPname;
	
	InlineManager(HandleFOPCstrings stringHandler, HornClausebase hornClauseKnowledgeBase) {
        this.stringHandler = stringHandler;
        this.hornClauseKnowledgeBase = hornClauseKnowledgeBase;
        this.notPname = stringHandler.standardPredicateNames.negationByFailure;
    }

	private BindingList literalMatchesDeterminateClause(Literal lit, Clause c, BindingList bindings) {
		if (!c.isDefiniteClause()) { Utils.error("This code only handle definite clauses.  It was given: " + c); }
		Literal head = c.getDefiniteClauseHead();
		return Unifier.UNIFIER.unify(lit, head, bindings);
	}

	// Handle any 'inliners' in this clause.  Return a LIST of clauses,
	// where the FIRST clause is the new version of the provided clause,
	// and the REST of the Clauses (if any) are the SUPPORTING literals in
	// this clause.  (Recall that supporting literals are ones that need to accompany theories.)
	public List<Clause> handleInlinerAndSupportingClauses(Clause c) {
		if (c == null) { return null; }

		if (!c.isDefiniteClause()) { Utils.error("This code only handle definite clauses.  It was given: " + c); }

		List<Clause> results = help_handleInlinerAndSupportingClauses(c, 0);
		if (results == null) { Utils.waitHere("Got no results from in-lining: " + c); return null; }
		VisitedClauses clausesVisited = new VisitedClauses(100000);  // Watch for duplicates in the Supporting Clauses.
		List<Clause>   newResults     = new ArrayList<>(results.size());
		for (Clause c2 : results) {
			Clause newClause = (Clause) getStringHandler().renameAllVariables(c2);
			newResults.add(newClause);
			clausesVisited.addClauseToClosed(getStringHandler(),newClause); // OK to add the 'main clause' here, since it would be odd to have the same clause as a main and supporting clause.
		}
		return newResults;
	}
	private final BindingList blToUse =  new BindingList();
	private List<Clause> help_handleInlinerAndSupportingClauses(Clause c, int depth) {

		if (c == null) { return null; }

		if (depth >  50) { Utils.severeWarning("Are some in-liners calling each other, producing an infinite loop?\n " + c); }
		if (depth > 100) { Utils.error("Seems to be an infinite loop.\n " + c); } // If this passed the severeWarning, and still a problem, simply give up.

        if (!c.isDefiniteClause()) { Utils.error("This code only handle definite clauses.  It was given: " + c); }
		
		List<Literal> newBodyLiterals = new ArrayList<>(c.getLength());
		Set<Clause>   supporters      = null; // Remove duplicates when possible, but might not too look for variants via VisitedClauses instance.
		BindingList   overallBindings = new BindingList(); // Need to keep track of all the bindings necessary to make the in-lines match up.

		if (c.negLiterals != null) for (Literal lit : c.negLiterals) {

			// Here we assume any functions can/will be converted to a literal, e.g., they are inside a FOR-LOOP of some sort.
			// TODO - maybe we need to check the predicateName of lit and treat like we do for NOT (should also handle ONCE, CALL, etc ...), but risky to require names be in a list ...
			if (lit.predicateName != notPname && lit.numberArgs() > 0) for (Term t : lit.getArguments()) if (t instanceof Function) {
				Literal functAtLit = ((Function) t).convertToLiteral(getStringHandler());
				Iterable<Clause> definingClauses = getHornClauseKnowledgeBase().getPossibleMatchingBackgroundKnowledge(functAtLit, blToUse);
				if (definingClauses != null) for (Clause c2 : definingClauses) { // TODO clean up the duplicated code.
					blToUse.theta.clear();
					BindingList bl = literalMatchesDeterminateClause(functAtLit, c2, blToUse);
					if (bl == null) { continue; }
					List<Clause> recurResults = help_handleInlinerAndSupportingClauses(c2.applyTheta(bl.theta), depth + 1);
					if (supporters == null) { supporters = new HashSet<>(1); }
					//	Utils.println("%   supporters = " + recurResults);
					if (Utils.getSizeSafely(recurResults) > 0) { supporters.addAll(recurResults); }
				}
			}

			if (lit.predicateName == notPname) { // We want to leave these as is, but need to collecting any 'supporters' they need.


				Clause clause = getStringHandler().getNegationByFailureContents(lit);
                if ( clause == null ) {
                    Utils.error("Expected term of negation to be Function or SentenceAsTerm.");
                }
                
                if ( clause.getNegLiteralCount() > 0 && clause.getPosLiteralCount() > 0 ) {
                    Utils.error("Negated clause should be composed of either positive literal or negative literal, but not both.");
                }

                if ( clause.getPosLiteralCount() == 0) {
                    // Make sure the negated clauses literals are positive
                    clause = clause.getStringHandler().getClause(clause.getNegativeLiterals(), clause.getPositiveLiterals());
                }

                if (Utils.getSizeSafely(clause.negLiterals) > 0) { Utils.error("Should not have negative literals inside a negation-by-failure.");         }
                if (Utils.getSizeSafely(clause.posLiterals) < 1) { Utils.error("Should have at least one positive literal inside a negation-by-failure."); }

                for (Literal pLit : clause.getPositiveLiterals()) {
					Clause litAsDefiniteClause = stringHandler.getClause(stringHandler.getLiteral(stringHandler.standardPredicateNames.trueName), pLit);
					List<Clause> moreClauses = help_handleInlinerAndSupportingClauses(litAsDefiniteClause, depth+1);
					if ( moreClauses != null && moreClauses.size() > 1 ) {
						for (int i = 1; i < moreClauses.size(); i++) {
							if (supporters == null) { supporters = new HashSet<>(1); }
							supporters.add(moreClauses.get(i));
						}
					}
				}
				newBodyLiterals.add(lit);
			} else { // Simply save.
				newBodyLiterals.add(lit);
			}			
		}
		Clause newClause = getStringHandler().getClause(c.posLiterals, newBodyLiterals, c.getExtraLabel());  // Note we are REUSING THE OLD HEAD.
		List<Clause> newListOfClauses = new ArrayList<>();
		Clause newClauseBound = newClause.applyTheta(overallBindings.theta);
		newListOfClauses.add(newClauseBound);
		if (Utils.getSizeSafely(supporters) < 1) { return newListOfClauses; }
		assert supporters != null;
		newListOfClauses.addAll(supporters); // These do not need to be unified since they are stand-alone.
		return newListOfClauses;		
	}

	private HandleFOPCstrings getStringHandler() {
        return stringHandler;
    }

	public HornClausebase getHornClauseKnowledgeBase() {
        return hornClauseKnowledgeBase;
    }

}
