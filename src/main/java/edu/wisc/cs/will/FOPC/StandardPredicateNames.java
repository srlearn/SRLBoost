package edu.wisc.cs.will.FOPC;

import java.util.HashSet;
import java.util.Set;

/*
 * @author twalker
 */
public class StandardPredicateNames {

    public final PredicateName trueName;

    public final PredicateName cut;

    public final PredicateName cutMarker;

    public final PredicateName negationByFailure;

    public final Set<PredicateName> buildinPredicates;

    StandardPredicateNames(HandleFOPCstrings stringHandler) {


        boolean hold = stringHandler.cleanFunctionAndPredicateNames;
        stringHandler.cleanFunctionAndPredicateNames = false;

        trueName = stringHandler.getPredicateName("true");
        cut = stringHandler.getPredicateName("!");
        cutMarker = stringHandler.getPredicateName("cutMarker");
        negationByFailure = stringHandler.getPredicateName("\\+");

        negationByFailure.setContainsCallable();

        buildinPredicates = new HashSet<>(4);
        buildinPredicates.add(trueName);
        buildinPredicates.add(cut);
        buildinPredicates.add(cutMarker);
        buildinPredicates.add(negationByFailure);

        stringHandler.cleanFunctionAndPredicateNames = hold;
    }
}
