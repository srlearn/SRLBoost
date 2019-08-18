package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.SLDQuery;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchResult;

/*
 * @author twalker
 */
public class DefaultProof implements Proof {

    private HornClauseProver prover;
    
    private SearchResult searchResult = null;

    public DefaultProof(HornClauseContext context, SLDQuery query) {
        this(context.getClausebase(), query);
    }

    private DefaultProof(HornClausebase clausebase, SLDQuery query) {
        setupProver(clausebase);

        setQuery(query);
    }

    private void setupProver(HornClausebase clausebase) {
        clausebase.getStringHandler();
        this.prover = new HornClauseProver(clausebase, true);
    }

    private void setQuery(SLDQuery query) {
        prover.initialize(query);
    }

    public BindingList prove()  {
        try {
            if (!isProofComplete()) {
                searchResult = prover.continueSearch(true);

                if ( searchResult.goalFound() ) {
                    return new BindingList(((ProofDone) prover.terminator).collectQueryBindings());
                }
            }
        }
        catch ( SearchInterrupted ignored) {
            
        }
        
        return null;
        
    }

    public BindingList getBindings() {
        if ( searchResult == null ) {
            prove();
        }

        if ( searchResult.goalFound() ) {
            return new BindingList(((ProofDone) prover.terminator).collectQueryBindings());
        }
        else {
            return null;
        }
    }

    public boolean isProofComplete() {
        if ( searchResult == null ) {
            return false;
        }
        else {
            return !searchResult.goalFound() || prover.open.isEmpty();
        }
    }

    public boolean isTrue() {
        if ( searchResult == null ) {
            prove();
        }

        return searchResult.goalFound();
    }

    public HornClauseProver getProver() {
        return prover;
    }




}
