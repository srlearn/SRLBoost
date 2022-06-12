package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.ResThmProver.HornClausebase;
import edu.wisc.cs.will.Utils.Utils;

import java.util.ArrayList;
import java.util.List;

public class InlineManager {

	private final HandleFOPCstrings  stringHandler;

	private final PredicateName      notPname;
	
	InlineManager(HandleFOPCstrings stringHandler, HornClausebase hornClauseKnowledgeBase) {
        this.stringHandler = stringHandler;
		this.notPname = stringHandler.standardPredicateNames.negationByFailure;
    }

	// Handle any 'inliners' in this clause.  Return a LIST of clauses,
	// where the FIRST clause is the new version of the provided clause,
	// and the REST of the Clauses (if any) are the SUPPORTING literals in
	// this clause.  (Recall that supporting literals are ones that need to accompany theories.)
	public List<Clause> handleInlinerAndSupportingClauses(Clause c) {
		if (c == null) {
			return null;
		}

		if (!c.isDefiniteClause()) {
			Utils.error("This code only handle definite clauses.  It was given: " + c);
		}

		List<Clause> results = help_handleInlinerAndSupportingClauses(c);
		if (results == null) {
			Utils.waitHere("Got no results from in-lining: " + c);
			return null;
		}
		VisitedClauses clausesVisited = new VisitedClauses(100000);  // Watch for duplicates in the Supporting Clauses.
		List<Clause>   newResults     = new ArrayList<>(results.size());
		for (Clause c2 : results) {
			Clause newClause = (Clause) getStringHandler().renameAllVariables(c2);
			newResults.add(newClause);
			clausesVisited.addClauseToClosed(getStringHandler(),newClause); // OK to add the 'main clause' here, since it would be odd to have the same clause as a main and supporting clause.
		}
		return newResults;
	}

	private List<Clause> help_handleInlinerAndSupportingClauses(Clause c) {

		if (c == null) { return null; }

		if (!c.isDefiniteClause()) {
			Utils.error("This code only handle definite clauses.  It was given: " + c);
		}
		
		List<Literal> newBodyLiterals = new ArrayList<>(c.getLength());
		// Remove duplicates when possible, but might not too look for variants via VisitedClauses instance.
		BindingList   overallBindings = new BindingList(); // Need to keep track of all the bindings necessary to make the in-lines match up.

		if (c.negLiterals != null) for (Literal lit : c.negLiterals) {

			// Here we assume any functions can/will be converted to a literal, e.g., they are inside a FOR-LOOP of some sort.
			// TODO - maybe we need to check the predicateName of lit and treat like we do for NOT (should also handle ONCE, CALL, etc ...), but risky to require names be in a list ...
			if (lit.predicateName != notPname && lit.numberArgs() > 0) for (Term t : lit.getArguments()) if (t instanceof Function) {
				// TODO(hayesall): The negation as failure stuff should generally be unavailable now.
				throw new RuntimeException("Deprecated.");
			}

			if (lit.predicateName == notPname) {
				// We want to leave these as is, but need to collecting any 'supporters' they need.
				// TODO(hayesall): More negation as failure stuff that isn't used.
				throw new RuntimeException("Deprecated.");

			} else { // Simply save.
				newBodyLiterals.add(lit);
			}			
		}

		// TODO(hayesall): It *looks* like this takes something out of one list and puts it into another,
		//		might be possible to remove, do some testing.

		Clause newClause = getStringHandler().getClause(c.posLiterals, newBodyLiterals, c.getExtraLabel());  // Note we are REUSING THE OLD HEAD.
		List<Clause> newListOfClauses = new ArrayList<>();
		Clause newClauseBound = newClause.applyTheta(overallBindings.theta);
		newListOfClauses.add(newClauseBound);
		return newListOfClauses;
	}

	private HandleFOPCstrings getStringHandler() {
        return stringHandler;
    }

}
