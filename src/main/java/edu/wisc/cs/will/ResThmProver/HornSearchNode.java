package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

import java.util.Collection;
import java.util.List;

/*
 * @author shavlik
 */
public class HornSearchNode extends SearchNode {

    private static final long serialVersionUID = -529194347314639209L;
    Clause clause;
	final BindingList bindings;
    final long        parentProofCounter;
    final int         parentExpansionIndex;


	HornSearchNode(HornClauseProver task, Clause clause, long parentProofCounter, int parentExpansionIndex) { // Used for the initial call (i.e., to create the root of the search space).
		super(task);
		this.clause   = clause;
		this.bindings = null; // I don't think there will ever be bindings at the root, but leave a hook in here just in case.
        this.parentProofCounter = parentProofCounter;
        this.parentExpansionIndex = parentExpansionIndex;
	}
	HornSearchNode(HornSearchNode parentNode, Clause clause, BindingList bindings, long parentProofCounter, int parentExpansionIndex) {
		super(parentNode);
		this.clause   = clause;
		this.bindings = bindings;
        this.parentProofCounter = parentProofCounter;
        this.parentExpansionIndex = parentExpansionIndex;
	}

    // Note that the bindings returned by this might look confusing since two different instances of the variable x will print the same,
	// and since they are really two different variables, they may well bind to different things.
    List<Binding> collectBindingsToRoot() {

        List<Binding> bindingList = null;

        if ( getParentNode() != null ) {
            bindingList = getParentNode().collectBindingsToRoot();
        }

        if ( bindings != null ) {
            if ( bindingList == null ) {
                bindingList = bindings.collectBindingsInList();
            }
            else {
                List<Binding> moreBindings = bindings.collectBindingsInList();
                if ( moreBindings != null ) {
                    bindingList.addAll(moreBindings);
                }
            }
        }
		
		return bindingList;
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

    /*
     * Returns the binding for variable, or null if no binding is found.
     */
    Term getBinding(Variable variable) {

        Term result = variable;

        HornSearchNode currentNode = this;

        while(result instanceof Variable && currentNode != null) {
            if ( bindings != null ) {
               Term newResult = bindings.getMapping((Variable)result);
               if ( newResult != null ) {
                   result = newResult;
               }
            }

            currentNode = currentNode.getParentNode();
        }

        return result == variable ? null : result;
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
