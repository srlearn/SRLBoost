package edu.wisc.cs.will.FOPC;

/** Abstract class for User defined literal.
 *
 * <p>This class provides some basic functionality for User Defined Literals, including
 * caching of answers.</p>
 *
 * <p>Generally users should not subclass this directly.  Instead they should subclass
 * on of the subclass based on their needs.</p>
 *
* <p>See {@link UserDefinedLiteral} for help in choosing the correct abstract class
 * to base your user defined literal on.  Must of the book-keeping and Will types
 * are already handled by these classes.
 *
 */
abstract class AbstractUserDefinedLiteral implements UserDefinedLiteral {

    /** Indicates that the UserDefinedLiteral values may be cached.
     * 
     */
    private boolean cachingEnabled = false;

    /** Constructor for AbstractUserDefinedLiteral.
     *
     * @param cachingEnabled Sets cachingEnabled.  Caching should only be used
     * when the literal is deterministic.
     */
    AbstractUserDefinedLiteral(boolean cachingEnabled) {
        setCachingEnabled(cachingEnabled);
    }

    /**
     * @return the cachingEnabled
     */
    boolean isCachingEnabled() {
        return cachingEnabled;
    }

    /** Enables caching of the results of evaluating the literal.
     *
     * Caching should only be enabled on deterministic user defined literals.
     *
     * @param cachingEnabled the cachingEnabled to set
     */
    private void setCachingEnabled(boolean cachingEnabled) {
        if (this.cachingEnabled != cachingEnabled) {

            this.cachingEnabled = cachingEnabled;
        }
    }
}
