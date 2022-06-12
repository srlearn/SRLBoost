package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.*;

import java.util.List;
import java.util.Set;

/*
 * @author shavlik
 *
 * A SLD theorem prover.  "SLD" stands for "SL resolution with Definite clauses."
 * 
 * See http://en.wikipedia.org/wiki/SLD_resolution and http://en.wikipedia.org/wiki/Horn_clause or an AI textbook.
 */
public class HornClauseProver extends StateBasedSearchTask<HornSearchNode> {

	private final HornClauseContext context;

	final Set<PredicateName>                predefinedPredicateNamesUsedByChildCollector; // Those in those list are handled by collectChildrenActual.

	public HornClauseProver(HornClauseContext context) {
        this(context, false);
    }
    public HornClauseProver(HornClauseContext context, boolean redoable) {        
        this(context, new DepthFirstSearch(), redoable);
    }
    private HornClauseProver(HornClauseContext context, SearchStrategy searchStrategy, boolean redoable) {
        this.context = context;
        taskName = "HornClauseProver";
        this.redoable = redoable;
        
        HandleFOPCstrings stringHandler = context.getStringHandler();

        predefinedPredicateNamesUsedByChildCollector = stringHandler.standardPredicateNames.buildinPredicates;

		InitHornProofSpace     myInitializer = new InitHornProofSpace(this);
		ProofDone              endTest       = new ProofDone();
		SearchMonitor          monitor       = new SearchMonitor(this); // new ProofMonitor(this); // Use this for more info.
		HornClauseProverChildrenGenerator hornClauseProverChildrenGenerator = new HornClauseProverChildrenGenerator(this, context);

		maxSearchDepth     =   100000;
        setMaxNodesToConsider(1000000);
        setMaxNodesToCreate( 10000000);
        
        verbosity = 0; // Change if debugging odd behavior.

		initalizeStateBasedSearchTask(myInitializer, endTest, monitor, searchStrategy, null, hornClauseProverChildrenGenerator, null);
	}

	private boolean proveSimpleQuery(Literal negatedFact) throws SearchInterrupted {
		((InitHornProofSpace) initializer).loadNegatedSimpleQuery(negatedFact, open);
		return performSearch().goalFound();
	}

	private int countOfWarningsForMaxNodes =   0;
	public boolean proveConjunctiveQuery(List<Literal> negatedConjunctiveQuery) throws SearchInterrupted {
		if (negatedConjunctiveQuery == null) { return false; } // No way to make the empty query true.
		if (Utils.getSizeSafely(negatedConjunctiveQuery) == 1) { return proveSimpleQuery(negatedConjunctiveQuery.get(0)); }
		((InitHornProofSpace) initializer).loadNegatedConjunctiveQuery(negatedConjunctiveQuery, open);

        SearchResult result = performSearch();
		int maxWarningsForMaxNodes = 100;
		if ( result  == SearchMonitor.maxNodesConsideredReached && countOfWarningsForMaxNodes++ < maxWarningsForMaxNodes) {
            Utils.warning( "#" + Utils.comma(countOfWarningsForMaxNodes) + " MaxNodesConsidered reached while proving:\n  " + negatedConjunctiveQuery + ".");
        }

		return result.goalFound();
	}

	public BindingList proveConjunctiveQueryAndReturnBindings(List<Literal> negatedConjunctiveQuery) throws SearchInterrupted {
		if (proveConjunctiveQuery(negatedConjunctiveQuery)) {
			return new BindingList(((ProofDone) terminator).collectQueryBindings());
		}
		return null;
	}

	public HornClausebase getClausebase() {
        return context.getClausebase();
    }

    public HandleFOPCstrings getStringHandler() {
        return context.getStringHandler();
    }


}
