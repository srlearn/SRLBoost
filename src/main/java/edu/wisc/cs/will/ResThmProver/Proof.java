package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;

/*
 * @author twalker
 */
public interface Proof {

    /* Returns true if the most recent prove through the proof succeeded.
     */
    boolean isTrue();

    /* Returns true if there are remaining choice points that could be evaluated.
     */
    boolean isProofComplete();

    /* Returns the binding list for the most recent prove through the proof.
     * If the most recent proof failed, this will return null.
     */
    BindingList getBindings();

    /* Attempts to prove the query, backtracking through remaining choice points if necessary.
     * Return BindingList if prove is successful, or null.
     */
    BindingList prove();

    HornClauseProver getProver();
}
