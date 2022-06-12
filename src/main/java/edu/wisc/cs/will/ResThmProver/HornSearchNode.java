package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

import java.util.Collection;

/*
 * @author shavlik
 */
public class HornSearchNode extends SearchNode {

    Clause      clause;
	final BindingList bindings;


    HornSearchNode(HornClauseProver task, Clause clause) { // Used for the initial call (i.e., to create the root of the search space).
		super(task);
		this.clause   = clause;
		this.bindings = null; // I don't think there will ever be bindings at the root, but leave a hook in here just in case.
    }
	HornSearchNode(HornSearchNode parentNode, Clause clause, BindingList bindings) {
		super(parentNode);
		this.clause   = clause;
		this.bindings = bindings;
    }

    private BindingList getQueryVariables() {

        BindingList bl;

        if ( getParentNode() != null ) {
            bl = getParentNode().getQueryVariables();
        }
        else {
            Collection<Variable> queryVariables = clause.collectAllVariables();

            bl = new BindingList();

            if ( queryVariables != null ) {
                for (Variable variable : queryVariables) {
                    bl.addBinding(variable, variable);
                }
            }
        }

        return bl;
    }

    BindingList collectQueryBindings() {

        BindingList bl;

        if ( getParentNode() != null ) {
            bl = getParentNode().collectQueryBindings();

            if ( bindings != null && bindings.theta != null ) {
                bl.applyThetaInPlace(bindings.theta);
            }
        }
        else {
            bl = getQueryVariables();
        }

        return bl;

    }

    /* Returns the ParentNode.
     *
     * Jude, I know you don't like getters/setters, but this is a place where they
     * really help.  The HornSearchNode's parent must also be a HornSearchNode.
     * We use the setParentNode method to enforce that restriction.
     * <p>
     * Also, a nice side effect is that Java allows you to change the
     * return type of a overriden method.  SearchNode.getParentNode()
     * returns a SearchNode.  However, here I know that the parentNode
     * is a HornSearchNode, so I change the return type appropriately.
     * Previous to this, you just did the typecast when you used it.  Now,
     * the cast is located just in the getter.
     *
     * @return the parentNode
     */
    @Override
    public HornSearchNode getParentNode() {
        return (HornSearchNode) super.getParentNode();
    }

    boolean isSolution() {
        return ( clause != null && clause.isEmptyClause());
    }

    @Override
	public String toString() {
        return (getParentNode() == null ? "" : "parent -> ") + clause.toString();
	}

}
