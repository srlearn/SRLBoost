package edu.wisc.cs.will.ResThmProver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConsCell;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArityFilter;
import edu.wisc.cs.will.FOPC.ProcedurallyDefinedPredicateHandler;
import edu.wisc.cs.will.FOPC.SLDQuery;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.ClosedList;
import edu.wisc.cs.will.stdAIsearch.DepthFirstSearch;
import edu.wisc.cs.will.stdAIsearch.ScoringFunction;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchMonitor;
import edu.wisc.cs.will.stdAIsearch.SearchResult;
import edu.wisc.cs.will.stdAIsearch.SearchStrategy;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask;

/**
 * @author shavlik
 *
 * A SLD theorem prover.  "SLD" stands for "SL resolution with Definite clauses."
 * 
 * See http://en.wikipedia.org/wiki/SLD_resolution and http://en.wikipedia.org/wiki/Horn_clause or an AI textbook.
 */
public class HornClauseProver extends StateBasedSearchTask<HornSearchNode> {
	protected static final int debugLevel = 0;  // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).
	
	protected Unifier           unifier = new Unifier();
    private   HornClauseContext context;

	Set<PredicateName>                predefinedPredicateNamesUsedByChildCollector; // Those in those list are handled by collectChildrenActual.

	/** Indicates level of output during proof.
     *
     * The traceLevel controls the amount of output generated
     * at each step in the proof.  This is similar to the
     * debugLevel but instead prints out step by step information.
     *
     * Currently, the following levels exist:
     * 0 - silent.
     * 1 - Literal being expanded and abbreviated expansions.
     * 2 - Literal being expanded and full expansions.
     * 3 - Literal being expanded, full expansions, and all bindings (this is slow...).
     */
    private int                       traceLevel = 0;

    private PredicateNameAndArityFilter  spyEntries;

	public HornClauseProver(HandleFOPCstrings stringHandler) {		
		this(stringHandler, null, null);
	}
	public HornClauseProver(HandleFOPCstrings stringHandler, Theory rules, Collection<? extends Sentence> facts) {
        this(stringHandler, new DefaultHornClausebase(stringHandler, (rules == null ? null : rules.getClauses()), facts), new DepthFirstSearch(), null);
	}
	public HornClauseProver(HandleFOPCstrings stringHandler, Theory rules, Collection<? extends Sentence> facts, SearchStrategy searchStrategy) {
		this(stringHandler, new DefaultHornClausebase(stringHandler, (rules == null ? null : rules.getClauses()), facts), searchStrategy, null);
	}
	public HornClauseProver(HandleFOPCstrings stringHandler, Theory rules, Collection<? extends Sentence> facts, SearchStrategy searchStrategy, ScoringFunction scorer) {
		this(stringHandler, new DefaultHornClausebase(stringHandler, (rules == null ? null : rules.getClauses()), facts), searchStrategy, scorer);
	}
	public HornClauseProver(HandleFOPCstrings stringHandler, Theory rules, Collection<? extends Sentence> facts, ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandler) {
		this(stringHandler, new DefaultHornClausebase(stringHandler, (rules == null ? null : rules.getClauses()), facts, userProcedurallyDefinedPredicateHandler), new DepthFirstSearch(), null);
	}
    public HornClauseProver(HandleFOPCstrings stringHandler, HornClausebase factbase) {
        this(stringHandler, factbase, new DepthFirstSearch(), null);
	}
	public HornClauseProver(HornClausebase factbase, boolean redoable) {
        this(new DefaultHornClauseContext(factbase), new DepthFirstSearch(), null,redoable);
	}
	public HornClauseProver(HandleFOPCstrings stringHandler, HornClausebase factbase, SearchStrategy searchStrategy, ScoringFunction scorer) {
        this(new DefaultHornClauseContext(factbase), searchStrategy, scorer, false);
    }
    public HornClauseProver(HornClauseContext context) {
        this(context, false);
    }
    public HornClauseProver(HornClauseContext context, boolean redoable) {        
        this(context, new DepthFirstSearch(), null, redoable);
    }
    public HornClauseProver(HornClauseContext context, SearchStrategy searchStrategy, ScoringFunction scorer, boolean redoable) {
        this.context = context;
        taskName = "HornClauseProver";
        this.redoable = redoable;
        
        HandleFOPCstrings stringHandler = context.getStringHandler();

        spyEntries = stringHandler.getSpyEntries();
        
        predefinedPredicateNamesUsedByChildCollector = stringHandler.standardPredicateNames.buildinPredicates;

		InitHornProofSpace     myInitializer = new InitHornProofSpace(this);
		ProofDone              endTest       = new ProofDone(this);
		SearchMonitor          monitor       = new SearchMonitor(this); // new ProofMonitor(this); // Use this for more info.
		HornClauseProverChildrenGenerator hornClauseProverChildrenGenerator = new HornClauseProverChildrenGenerator(this, context);
		ClosedList             myClosed      = null;

        maxSearchDepth     =   100000;
        setMaxNodesToConsider(1000000);
        setMaxNodesToCreate( 10000000);
        
        verbosity = 0; // Change if debugging odd behavior.
							
		initalizeStateBasedSearchTask(myInitializer, endTest, monitor, searchStrategy, scorer, hornClauseProverChildrenGenerator, myClosed);
	}

	private PredicateName getPredicateNameFromFirstNegatedLiteral(HornSearchNode node) {
		List<Literal> queryLiterals  = node.clause.negLiterals;
		Literal       negatedLiteral = queryLiterals.get(0);
		return negatedLiteral.predicateName;
	}
	
    @Override
	public void cleanOpen() { // This is used to remove cutMarkers from the front of open.  This is only called from the read-eval-print loop, since some cutMarkers can be in an OPEN that should be empty.  Be careful calling this from elsewhere.
		if (open.isEmpty()) { return; }
		HornSearchNode node = open.popOpenList();
		while (getPredicateNameFromFirstNegatedLiteral(node) == getStringHandler().standardPredicateNames.cutMarker) {
			Utils.println("  discard this no-longer-needed cut marker: " + node);
			if (open.isEmpty()) { return; } // The last item in open was a cutMarkerPred, so don't do another POP.
			node = open.popOpenList();
		}
		open.addToFrontOfOpenList(node); // Need to return the last item popped.
	}

    protected void initialize(List<Literal> negatedConjunctiveQuery ) {
        ((InitHornProofSpace) initializer).loadNegatedConjunctiveQuery(negatedConjunctiveQuery, open);
    }

    protected void initialize(SLDQuery query) throws IllegalArgumentException {
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

	// TODO(?): Clean up the names of these functions.
	public boolean proveSimpleQuery(Literal negatedFact) throws SearchInterrupted {
		((InitHornProofSpace) initializer).loadNegatedSimpleQuery(negatedFact, open);
		return performSearch().goalFound();
	}

	public BindingList proveSimpleQueryAndReturnBindings(Literal negatedFact) throws SearchInterrupted {

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
	
	public BindingList query(FileParser parser, String sentencesAsString) throws SearchInterrupted {
		char lastChar = sentencesAsString.charAt(sentencesAsString.length() - 1);
		
		// Add a terminating period if one isn't there.  Should be safe even if no final period is needed - though add the extra space in case the final item is an integer (alternatively, could use ';'). 
		if (lastChar != '.' && lastChar != ';') { sentencesAsString += " ."; }
		List<Sentence> sentences = parser.readFOPCstream(sentencesAsString);
		if (sentences.size() == 1) { return query(sentences.get(0)); }
		Utils.error("Queries must be conjunctive.  You provided: " + sentencesAsString); return null;
	}
	public BindingList query(Sentence sentence) throws SearchInterrupted {
		List<Literal> negLiterals = convertSentenceToConjunctiveQuery(sentence, getStringHandler());
		
		if (negLiterals.size() == 1) { return proveSimpleQueryAndReturnBindings((negLiterals.get(0))); }
		return proveConjunctiveQueryAndReturnBindings(negLiterals);
	}
	
	public List<Term> getAllUniqueGroundings(Literal query) throws SearchInterrupted {
		Function   queryAsFunction = query.convertToFunction(getStringHandler());
		Variable   var             = getStringHandler().getNewUnamedVariable();
		List<Term> findAllArgList  = new ArrayList<Term>(3);
		findAllArgList.add(queryAsFunction);
		Clause clause = getStringHandler().getClause(query, false);
		findAllArgList.add(getStringHandler().getSentenceAsTerm(clause, "getAllUniqueGroundings"));
		findAllArgList.add(var);
		Literal allRaw = getStringHandler().getLiteral(getStringHandler().standardPredicateNames.all, findAllArgList);
		BindingList  bl = proveSimpleQueryAndReturnBindings(allRaw);
		if (bl == null) { return null; }
		ConsCell allResults = (ConsCell) bl.lookup(var);
		if (debugLevel > 1) { Utils.println("% Have found " + Utils.comma(allResults == null ? 0 : allResults.length()) + " unique groundings of '" + query + "'.\n"); } // % var = " + var + " bl=" + bl); }
		if (allResults == null) { return null; }
		return allResults.convertConsCellToList();
	}
		
	private List<Literal> convertSentenceToConjunctiveQuery(Sentence sentence, HandleFOPCstrings stringHandler) {
		// Need to negate the query since we're doing proofs by negation.
		List<Clause> clauses = sentence.convertForProofByNegation();

		if (clauses == null)     { Utils.error("Cannot convert '" + sentence + "' to a negated conjuntive query for use in resolution theorem proving."); }
		if (clauses.size() != 1) { Utils.error("Should only get ONE clause from '" + sentence + "' but got: " + clauses); }
		return convertSentenceToListOfNegativeLiterals(sentence);
	}

	private List<Literal> convertSentenceToListOfNegativeLiterals(Sentence sentence) {
		// Need to negate the query since we're doing proofs by negation.
		List<Clause> clauses = sentence.convertForProofByNegation();

		if (clauses == null)     { Utils.error("Cannot convert '" + sentence + "' to a negated conjuntive query for use in resolution theorem proving."); }
		if (clauses.size() != 1) { Utils.error("Should only get ONE clause from '" + sentence + "' but got: " + clauses); }
		Clause clause = clauses.get(0);
		List<Literal> posLiterals = clause.posLiterals;
		List<Literal> negLiterals = clause.negLiterals;
	
		if (posLiterals != null && posLiterals.size() > 0) {
			Utils.println(" Can only handle conjunctive queries where all the literals are unnegated. Please try again.");
		}
		return negLiterals;
	}

	// Allow direct use of the procedurally defined stuff.
	public boolean isProcedurallyDefined(PredicateName pName, int arity) {
        if ( getClausebase().getBuiltinProcedurallyDefinedPredicateHandler() != null && getClausebase().getBuiltinProcedurallyDefinedPredicateHandler().canHandle(pName,arity) ) return true;
        if ( getClausebase().getUserProcedurallyDefinedPredicateHandler() != null && getClausebase().getUserProcedurallyDefinedPredicateHandler().canHandle(pName,arity)) return true;
        return false;


    }
	public BindingList evaluateProcedurallyDefined(Literal lit) {
		if (lit == null) { return null; }
		return evaluateProcedurallyDefined(lit, new BindingList());
	}

	private BindingList evaluateProcedurallyDefined(Literal lit, BindingList bl) {
		if (lit == null) { return null; }
		BindingList result = null;
		try {
            ProcedurallyDefinedPredicateHandler handler = null;
            if ( (handler = getClausebase().getBuiltinProcedurallyDefinedPredicateHandler()) != null && handler.canHandle(lit.predicateName, lit.numberArgs()) ) {
                result = handler.handle(context,lit, unifier, bl);
            }
            else if ( (handler = getClausebase().getUserProcedurallyDefinedPredicateHandler()) != null && handler.canHandle(lit.predicateName, lit.numberArgs()) ) {
                result = handler.handle(context,lit, unifier, bl);
            }
		} catch (SearchInterrupted e) {
			Utils.reportStackTrace(e);
			Utils.error("Something when wrong with evaluateProcedurallyDefined(" + lit + ").");
		}
		return result;
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
