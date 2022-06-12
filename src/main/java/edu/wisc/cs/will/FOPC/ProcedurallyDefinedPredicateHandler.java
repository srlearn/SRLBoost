package edu.wisc.cs.will.FOPC;

import java.util.List;
import java.util.Set;

/*
 * This handler manages built-in's like equals, different, <, >, <=, >=, etc.
 * @author twalker
 */
public abstract class ProcedurallyDefinedPredicateHandler {

    protected ProcedurallyDefinedPredicateHandler() {}

    public boolean canHandle(PredicateName predicateName, int arity) {
        return canHandle(new PredicateNameAndArity(predicateName, arity));
    }
    
    private boolean canHandle(PredicateNameAndArity predicateNameAndArity) {
        return false;
    }

    /* Handle evaluation of the literal.
     *
     * canHandle should be called previous to this to determine if this
     * ProcedurallyDefinedPredicateHandler can handle the predicate
     * defined by this literal.
     * @param literal Literal to handle.
     * @param unifier Unifier to use.
     * @param bindingList Binding list, initially empty, that will contain the bindings generated during handling.
     * @return The binding list, or null if evaluation of the literal failed.
     * @throws SearchInterrupted Thrown if an error occurs which interpts the evaluation of the literal.
     */
    public abstract BindingList handle(Literal literal, BindingList bindingList);

    protected boolean confirmAllVarsAreBound(List<Term> args) {
		if (args != null) for (Term arg : args) if (arg instanceof Variable) {
            return false;
		}
		return true;
	}

}
