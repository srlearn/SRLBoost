package edu.wisc.cs.will.FOPC;

/** This is just an interface to simplify the proof definitions.
 *
 * Both sentences and terms support this interface, but not all sentences
 * and term are legal SLD queries.
 *
 * @author twalker
 */
public interface SLDQuery {
    /** Returns a Horn goal clause (clause with only negative literals).
     *
     * @return a Horn goal clause.
     * @throws IllegalArgumentException An illegal argument exception is thrown
     * if the SLDQuery can not be converted to a legal SLD query clause.
     */
    Clause getNegatedQueryClause() throws IllegalArgumentException;
}
