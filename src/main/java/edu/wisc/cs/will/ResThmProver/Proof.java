package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;

/*
 * @author twalker
 */
public interface Proof {

    /* Attempts to prove the query, backtracking through remaining choice points if necessary.
     * Return BindingList if prove is successful, or null.
     */
    BindingList prove();

}
