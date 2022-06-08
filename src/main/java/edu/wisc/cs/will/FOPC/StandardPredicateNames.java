/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.FOPC;

import java.util.HashSet;
import java.util.Set;

/*
 * @author twalker
 */
public class StandardPredicateNames { // A few FUNCTION names also appear here; for instance, sometimes we need to convert a literal to a function.

    public final PredicateName var;

    public final PredicateName number;

    public final PredicateName list;

    final PredicateName compound;

    public final PredicateName is;

    final PredicateName halt;

    public final PredicateName sort;

    final FunctionName pullOutNthArgFunction;

    public final PredicateName print;

    public final PredicateName write; // A synonym for 'print.'

    public final PredicateName waitHere;

    public final PredicateName wait; // A synonym for 'waitHere.'

    final PredicateName findAllCollector;

    final PredicateName allCollector;

    final PredicateName bagOfCollector;

    final PredicateName setOfCollector;

    public final PredicateName length;

    final PredicateName countProofsCollector;

    final PredicateName countUniqueBindingsCollector;

    public final PredicateName implicit_call;

    public final PredicateName trueName;

    public final PredicateName falseName;

    public final PredicateName fail;

    public final PredicateName repeat;

    public final PredicateName once;

    public final PredicateName call;

    public final PredicateName cut;

    public final PredicateName cutMarker;

    public final PredicateName findAll;

    public final PredicateName all;

    public final PredicateName setOf;

    public final PredicateName bagOf;

    public final PredicateName countProofs;

    public final PredicateName countUniqueBindings;

    public final PredicateName then;

    public final PredicateName negationByFailure;

    public final FunctionName negationByFailureAsFunction;

    public final PredicateName spy;

    public final PredicateName consCell;

    final FunctionName plusFunction;  // TODO build in a hash table of synonyms?

    final FunctionName minusFunction;

    final FunctionName timesFunction;

    final FunctionName divideFunction;

    final FunctionName intDivFunction;

    final FunctionName intFunction;

    final FunctionName modFunction;

    final FunctionName minFunction;

    final FunctionName maxFunction;

    final FunctionName minus2Function;

    final PredicateName unify2;

    public final PredicateName unify;

    final PredicateName ununifiable;

    final PredicateName ununifiable2;

    public final PredicateName equal;

    final PredicateName equal2;

    final PredicateName diff;

    final PredicateName notEqual;

    public final PredicateName ground;

    final PredicateName copyTerm;

    public final PredicateName gt;  // Prefix versions of these comparators haven't been provided.

    public final PredicateName lt;

    final PredicateName gte;   // gte = greater-than-or-equal

    public final PredicateName lte;   // lte = less-than-or-equal

    public final Set<PredicateName> buildinPredicates;

    StandardPredicateNames(HandleFOPCstrings stringHandler) {


        boolean hold = stringHandler.cleanFunctionAndPredicateNames;
        stringHandler.cleanFunctionAndPredicateNames = false;

        var = stringHandler.getPredicateName("var");
        number = stringHandler.getPredicateName("number");
        list = stringHandler.getPredicateName("list");
        compound = stringHandler.getPredicateName("compound");
        is = stringHandler.getPredicateName("is");
        halt = stringHandler.getPredicateName("halt");
        unify = stringHandler.getPredicateName("unify");
        unify2 = stringHandler.getPredicateName("=");
        ununifiable = stringHandler.getPredicateName("notUnify");
        ununifiable2 = stringHandler.getPredicateName("\\=");
        equal = stringHandler.getPredicateName("equal");
        equal2 = stringHandler.getPredicateName("==");
        diff = stringHandler.getPredicateName("diff");
        notEqual = stringHandler.getPredicateName("\\==");
        // not                 = stringHandler.getPredicateName("\\+");  // Note that there is also negationByFailure
        ground = stringHandler.getPredicateName("ground");
        copyTerm = stringHandler.getPredicateName("copy_term");
        gt = stringHandler.getPredicateName(">");  // Prefix versions of these comparators haven't been provided.
        lt = stringHandler.getPredicateName("<");
        gte = stringHandler.getPredicateName(">=");   // gte = greater-than-or-equal
        lte = stringHandler.getPredicateName("=<");   // lte = less-than-or-equal
        print = stringHandler.getPredicateName("print");
        write = stringHandler.getPredicateName("write"); // A synonym for 'print.'
        waitHere = stringHandler.getPredicateName("waitHere");
        wait = stringHandler.getPredicateName("wait"); // A synonym for 'waitHere.'
        findAllCollector = stringHandler.getPredicateName("findAllCollector");
        allCollector = stringHandler.getPredicateName("allCollector");
        bagOfCollector = stringHandler.getPredicateName("bagofCollector");
        setOfCollector = stringHandler.getPredicateName("setofCollector");
        length = stringHandler.getPredicateName("length");
        countProofsCollector = stringHandler.getPredicateName("countProofsCollector");
        countUniqueBindingsCollector = stringHandler.getPredicateName("countUniqueBindingsCollector");
        implicit_call = stringHandler.getPredicateName("implicit_call");
        trueName = stringHandler.getPredicateName("true");
        falseName = stringHandler.getPredicateName("false");
        fail = stringHandler.getPredicateName("fail");
        repeat = stringHandler.getPredicateName("repeat");
        once = stringHandler.getPredicateName("once");
        call = stringHandler.getPredicateName("call");
        cut = stringHandler.getPredicateName("!");
        cutMarker = stringHandler.getPredicateName("cutMarker");
        findAll = stringHandler.getPredicateName("findAll");
        all = stringHandler.getPredicateName("all");
        setOf = stringHandler.getPredicateName("setOf");
        bagOf = stringHandler.getPredicateName("bagOf");
        countProofs = stringHandler.getPredicateName("countProofs");
        countUniqueBindings = stringHandler.getPredicateName("countUniqueBindings");
        then = stringHandler.getPredicateName("then");
        negationByFailure = stringHandler.getPredicateName("\\+");
        sort = stringHandler.getPredicateName("sort");

        negationByFailureAsFunction = stringHandler.getFunctionName("\\+");
        plusFunction = stringHandler.getFunctionName("+"); // If another 'in-fix' operator is added to this list, need to edit FileParser.java.
        minusFunction = stringHandler.getFunctionName("-");
        minus2Function = stringHandler.getFunctionName("minus");
        timesFunction = stringHandler.getFunctionName("*");
        divideFunction = stringHandler.getFunctionName("/");   // Note that in essence 'true' division, rather than integer division, is used.
        intDivFunction = stringHandler.getFunctionName("/@"); // In ISO Prolog, this is '//' but that is a comment indicator to us.

        intFunction = stringHandler.getFunctionName("integer"); // Allow the user to force integer results.
        modFunction = stringHandler.getFunctionName("mod"); // Use Java's definition of mod.  Don't use a single-character symbol due to confusion between Java and Prolog.
        minFunction = stringHandler.getFunctionName("min");
        maxFunction = stringHandler.getFunctionName("max");
        FunctionName isFunction = stringHandler.getFunctionName("is");
        FunctionName unifyFunction = stringHandler.getFunctionName("unify");
        FunctionName unify2Function = stringHandler.getFunctionName("=");
        FunctionName ununifiableFunction = stringHandler.getFunctionName("notUnify");
        FunctionName ununifiable2Function = stringHandler.getFunctionName("\\=");
        FunctionName equalFunction = stringHandler.getFunctionName("equal");
        FunctionName equal2Function = stringHandler.getFunctionName("==");
        FunctionName notEqualFunction = stringHandler.getFunctionName("\\==");
        // Prefix versions of these comparators haven't been provided.
        FunctionName gtFunction = stringHandler.getFunctionName(">");  // Prefix versions of these comparators haven't been provided.
        FunctionName gt2Function = stringHandler.getFunctionName("gt");
        FunctionName ltFunction = stringHandler.getFunctionName("<");
        FunctionName lt2Function = stringHandler.getFunctionName("lt");
        // gte = greater-than-or-equal
        FunctionName gteFunction = stringHandler.getFunctionName(">=");   // gte = greater-than-or-equal
        FunctionName gte2Function = stringHandler.getFunctionName("gte");
        // lte = less-than-or-equal
        FunctionName lteFunction = stringHandler.getFunctionName("=<");   // lte = less-than-or-equal
        FunctionName lte2Function = stringHandler.getFunctionName("<=");
        FunctionName lte3Function = stringHandler.getFunctionName("lte");
        // Equal numbers.
        FunctionName equalNumbersFunction = stringHandler.getFunctionName("=:=");  // Equal numbers.
        // Not equal numbers.
        FunctionName notEqualNumbersFunction = stringHandler.getFunctionName("=\\="); // Not equal numbers.
        FunctionName equalDotDotFunction = stringHandler.getFunctionName("=..");
        pullOutNthArgFunction = stringHandler.getFunctionName("pullOutNthArg");

        spy = stringHandler.getPredicateName("spy");

        consCell = stringHandler.getPredicateName("consCell");


        is.printUsingInFixNotation = true;
        unify2.printUsingInFixNotation = true;
        ununifiable2.printUsingInFixNotation = true;
        equal2.printUsingInFixNotation = true;
        notEqual.printUsingInFixNotation = true;
        gt.printUsingInFixNotation = true;
        lt.printUsingInFixNotation = true;
        gte.printUsingInFixNotation = true;
        lte.printUsingInFixNotation = true;

        isFunction.printUsingInFixNotation = true;
        plusFunction.printUsingInFixNotation = true;
        minusFunction.printUsingInFixNotation = true;
        timesFunction.printUsingInFixNotation = true;
        divideFunction.printUsingInFixNotation = true;
        intDivFunction.printUsingInFixNotation = true;
        unify2Function.printUsingInFixNotation = true;
        ununifiable2Function.printUsingInFixNotation = true;
        equal2Function.printUsingInFixNotation = true;
        notEqualFunction.printUsingInFixNotation = true;
        gtFunction.printUsingInFixNotation = true;
        ltFunction.printUsingInFixNotation = true;
        gteFunction.printUsingInFixNotation = true;
        lteFunction.printUsingInFixNotation = true;
        lte2Function.printUsingInFixNotation = true;
        equalNumbersFunction.printUsingInFixNotation = true;
        notEqualNumbersFunction.printUsingInFixNotation = true;
        equalDotDotFunction.printUsingInFixNotation = true;

        call.setContainsCallable(1);
        negationByFailure.setContainsCallable(1);
        once.setContainsCallable(1);

        buildinPredicates = new HashSet<>(32);
        buildinPredicates.add(trueName);
        buildinPredicates.add(falseName);
        buildinPredicates.add(fail);
        buildinPredicates.add(repeat);
        buildinPredicates.add(once);
        buildinPredicates.add(call);
        buildinPredicates.add(implicit_call);
        buildinPredicates.add(cut);
        buildinPredicates.add(cutMarker);
        buildinPredicates.add(findAll);
        buildinPredicates.add(all);
        buildinPredicates.add(setOf);
        buildinPredicates.add(bagOf);
        buildinPredicates.add(countProofs);
        buildinPredicates.add(countUniqueBindings);
        buildinPredicates.add(then);
        buildinPredicates.add(negationByFailure);

        buildinPredicates.add(spy);

        stringHandler.cleanFunctionAndPredicateNames = hold;
    }
}
