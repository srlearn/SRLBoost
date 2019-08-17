package edu.wisc.cs.will.FOPC;

/**
 *
 * @author twalker
 */
public interface Implication {
    Sentence getAntecedent() throws IllegalStateException ;
    Sentence getConsequence() throws IllegalStateException;
}
