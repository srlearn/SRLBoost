package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.*;

import java.util.ArrayList;
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

	/* Indicates level of output during proof.
     *
     * The traceLevel controls the amount of output generated
     * at each step in the proof.  This is similar to the
     */
    private int                       traceLevel = 0;

    private final PredicateNameAndArityFilter  spyEntries;

	public HornClauseProver(HornClausebase factbase) {
        this(factbase, new DepthFirstSearch());
	}

	private HornClauseProver(HornClausebase factbase, SearchStrategy searchStrategy) {
        this(new DefaultHornClauseContext(factbase), searchStrategy, false);
    }
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

        spyEntries = stringHandler.getSpyEntries();
        
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

	private PredicateName getPredicateNameFromFirstNegatedLiteral(HornSearchNode node) {
		List<Literal> queryLiterals  = node.clause.negLiterals;
		Literal       negatedLiteral = queryLiterals.get(0);
		return negatedLiteral.predicateName;
	}

	private void initialize(List<Literal> negatedConjunctiveQuery) {
        ((InitHornProofSpace) initializer).loadNegatedConjunctiveQuery(negatedConjunctiveQuery, open);
    }

    private void initialize(SLDQuery query) throws IllegalArgumentException {
        initialize(query.getNegatedQueryClause().negLiterals);
    }

    public BindingList prove(SLDQuery query) throws IllegalArgumentException, SearchInterrupted {
        BindingList result = null;

        initialize(query);
        SearchResult sr = performSearch();

        if ( sr.goalFound() ) {
            result = new BindingList(((ProofDone) terminator).collectQueryBindings());
        }

        return result;
    }

	private boolean proveSimpleQuery(Literal negatedFact) throws SearchInterrupted {
		((InitHornProofSpace) initializer).loadNegatedSimpleQuery(negatedFact, open);
		return performSearch().goalFound();
	}

	private BindingList proveSimpleQueryAndReturnBindings(Literal negatedFact) throws SearchInterrupted {

		if (proveSimpleQuery(negatedFact)) {
			return new BindingList(((ProofDone) terminator).collectQueryBindings());
		}
		return null;
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

	public List<Term> getAllUniqueGroundings(Literal query) throws SearchInterrupted {
		Function   queryAsFunction = query.convertToFunction(getStringHandler());
		Variable   var             = getStringHandler().getNewUnamedVariable();
		List<Term> findAllArgList  = new ArrayList<>(3);
		findAllArgList.add(queryAsFunction);
		Clause clause = getStringHandler().getClause(query, false);
		findAllArgList.add(getStringHandler().getSentenceAsTerm(clause, "getAllUniqueGroundings"));
		findAllArgList.add(var);
		Literal allRaw = getStringHandler().getLiteral(getStringHandler().standardPredicateNames.all, findAllArgList);
		BindingList  bl = proveSimpleQueryAndReturnBindings(allRaw);
		if (bl == null) { return null; }
		ConsCell allResults = (ConsCell) bl.lookup(var);
		if (allResults == null) { return null; }
		return allResults.convertConsCellToList();
	}

	public HornClausebase getClausebase() {
        return context.getClausebase();
    }

    public HandleFOPCstrings getStringHandler() {
        return context.getStringHandler();
    }

    public PredicateNameAndArityFilter getSpyEntries() {
        return spyEntries;
    }

    public int getTraceLevel() {
        return traceLevel;
    }

	public void setTraceLevel(int traceLevel) {
        this.traceLevel = traceLevel;
    }


}
