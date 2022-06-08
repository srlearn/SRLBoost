package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Filter;

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/*
 * @author twalker
 */
class ArityFilter implements Filter<Integer>, Iterable<Integer> {

    /* Indicates that all arities are included in this filter.
     *
     * When this is set to true, all arities are included in the filter.
     * Additionally, when this is set to true, the includedAritySet will
     * be set to null and any attempts to add specific arities results
     * in no change to the arity set.
     * <p>
     * Also, when this is true, attempts to remove arities from the list
     * will result in no change.  Specific arities can not be removed
     * when the includeAllArities wildcare is true.
     */
    private boolean includeAllArities = false;

	private Set includedAritySet = null;

    ArityFilter() {}

    boolean includeElement(Integer arity) {

        boolean result = false;

        if ( includeAllArities ) {
            result = true;
        }
        else if ( includedAritySet != null ) {
            result = includedAritySet.contains(arity);
        }

        return result;
    }

    boolean isIncludeAllArities() {
        return includeAllArities;
    }

    void setIncludeAllArities() {

        if (!this.includeAllArities) {

            includedAritySet = null;

            this.includeAllArities = true;
        }
    }

    void addArity(int arity) {
        if (!includeAllArities) {

            if ( includedAritySet == null ) {
                includedAritySet = new HashSet<Integer>(4);
            }

            includedAritySet.add(arity);
        }
    }

    /* Returns an iterator over all included arities.
     *
     * Note, this does not account for the includeAllArities setting.
     * If includeAllArities is true, the returned iterator will always
     * be empty.
     */
    public Iterator<Integer> iterator() {
        if ( includedAritySet == null ) {
            return Collections.EMPTY_SET.iterator();
        }
        else {
            return includedAritySet.iterator();
        }
    }


}
