package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.ResThmProver.AssertRetractListener;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClausebase;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author twalker
 */
public class AdviceProcessor {

    private final List<RelevantModeInformation> relevantModes = new ArrayList<>();

    private final HandleFOPCstrings stringHandler;

    private final LearnOneClause learnOneClause;

    private List<PruningRule> pruningRules = null;

    public AdviceProcessor(HornClauseContext context, LearnOneClause learnOneClause) {

        this.stringHandler = context.getStringHandler();
        this.learnOneClause = learnOneClause;

        setupRelevantClauseListener(context);

        context.getStringHandler().setStringsAreCaseSensitive(true);
        HandleFOPCstrings.VarIndicator oldVI = context.getStringHandler().getVariableIndicatorNoSideEffects();
        context.getStringHandler().setVariableIndicator(HandleFOPCstrings.VarIndicator.uppercase);

        Clause memberPruneCondition = context.getFileParser().parseDefiniteClause("prune(ExistingLiteral, AddedLiteral) :- member(Iter1,List1)=ExistingLiteral, member(Iter2,List2)=AddedLiteral, List1 == List2, Iter2 = Iter1.");
        PruneDuplicatesIfTrueRule memberPruneRule = new PruneDuplicatesIfTrueRule(memberPruneCondition);
        addPruningRule(memberPruneRule);

        Clause compositeNamePruneCondition = context.getFileParser().parseDefiniteClause("prune(ExistingLiteral, AddedLiteral) :- ilField_Composite_name(W,Name1,Symbol1,S)=ExistingLiteral, ilField_Composite_name(W,Name2,Symbol2,S)=AddedLiteral, Symbol1 == Symbol2, Name2 = Name1.");
        PruneDuplicatesIfTrueRule compositeNamePruneRule = new PruneDuplicatesIfTrueRule(
                compositeNamePruneCondition);
        addPruningRule(compositeNamePruneRule);

        Clause sameAsCondition1 = context.getFileParser().parseDefiniteClause("prune(AddedLiteral) :- sameAsIL(W,X,X,S)=AddedLiteral.");

        PruneIfTrueRule sameAsPrune1 = new PruneIfTrueRule(sameAsCondition1);

        addPruningRule(sameAsPrune1);

        Clause forEachInChainPruneCondition = context.getFileParser().parseDefiniteClause("prune(Literal, Literal).");
        PruneDuplicatesIfTrueRule forEachInChainPruneRule = new PruneDuplicatesIfTrueRule(
                forEachInChainPruneCondition);
        addPruningRule(forEachInChainPruneRule);

        context.getStringHandler().setVariableIndicator(oldVI);
    }

    private void addGroundedAdvice(Example example, Clause relevanceClause, RelevanceStrength relevanceStrength) {

        RelevantClauseInformation rci = new RelevantClauseInformation(example, relevanceClause);
        rci.setRelevanceFromPositiveExample(true);
        rci.setOriginalRelevanceStrength(relevanceStrength);
    }

    private void addRelevantMode(Example example, Literal mode, RelevanceStrength relevanceStrength) {

        RelevantModeInformation rfi = new RelevantModeInformation(example, mode, relevanceStrength);

        if (!relevantModes.contains(rfi)) {
            relevantModes.add(rfi);
        }
    }

    public HornClauseContext getContext() {
        return learnOneClause.getContext();
    }

    private void addPruningRule(PruningRule rule) {
        if (pruningRules == null) {
            pruningRules = new ArrayList<>();
        }
        pruningRules.add(rule);
    }

    private void setupRelevantClauseListener(HornClauseContext context) {
        RelevantClauseListener relevantClauseListener = new RelevantClauseListener();
        context.getClausebase().addAssertRetractListener(relevantClauseListener, stringHandler.getPredicate("relevant_clause", 3));

        context.getClausebase().addAssertRetractListener(relevantClauseListener, stringHandler.getPredicate("relevant_unsplitable_index", 1));

        context.getClausebase().addAssertRetractListener(relevantClauseListener, stringHandler.getPredicate("relevant_feature", 3));

        context.getClausebase().addAssertRetractListener(relevantClauseListener, stringHandler.getPredicate("relevant_mode", 3));
    }

    public class RelevantClauseListener implements AssertRetractListener {

        @Override
        public void clauseAsserted(HornClausebase context, DefiniteClause clause) {

            if (!clause.isDefiniteClauseFact()) {
                Utils.waitHere("Illegal relevantClause specification '" + clause + "'.  Must be fact of form relevant_clause(Example, Clause, RelevantStrength.");
            }

            Literal lit = clause.getDefiniteClauseFactAsLiteral();

            switch (lit.predicateName.name) {
                case "relevant_clause":

                    try {
                        Literal relevantLiteral = ((Function) lit.getArgument(0)).convertToLiteral(stringHandler);
                        Sentence s = ((SentenceAsTerm) lit.getArgument(1)).sentence;
                        RelevanceStrength strength = RelevanceStrength.valueOf(((StringConstant) lit.getArgument(2)).getBareName().toUpperCase());

                        Clause relevantClause;
                        if (s instanceof Literal) {
                            Example Example = new Example((Literal) s);
                            relevantClause = stringHandler.getClause(Example, true);
                        } else {
                            relevantClause = (Clause) s;
                        }

                        addGroundedAdvice(new Example(relevantLiteral), relevantClause, strength);
                    } catch (ClassCastException castException) {
                        Utils.waitHere(castException + "\nIllegal relevantClause specification '" + clause + "'.\nMust be fact of form: relevant_clause(Example, Clause, RelevantStrength.");
                    }
                    break;
                case "relevant_unsplitable_index":
                    try {
                        NumericConstant indexConstant = (NumericConstant) lit.getArgument(0);
                        indexConstant.value.intValue();

                    } catch (ClassCastException castException) {
                        Utils.waitHere(castException + "\nIllegal relevantClause specification '" + clause + "'.  Must be fact of form relevant_clause(Example, Clause, RelevantStrength.");
                    }
                    break;
                case "relevant_feature": {
                    new Example((Function) lit.getArgument(0));

                    String nameAndArityString = ((StringConstant) lit.getArgument(1)).getBareName();
                    int index = nameAndArityString.indexOf("/");
                    String name = nameAndArityString.substring(0, index);
                    String arityString = nameAndArityString.substring(index + 1);
                    int arity = Integer.parseInt(arityString);

                    stringHandler.getPredicate(name, arity);
                    RelevanceStrength.valueOf(((StringConstant) lit.getArgument(2)).getBareName().toUpperCase());
                    break;
                }
                case "relevant_mode": {
                    Example relevantLiteral = new Example((Function) lit.getArgument(0));
                    Literal mode = lit.getArgument(1).asLiteral();
                    RelevanceStrength strength = RelevanceStrength.valueOf(((StringConstant) lit.getArgument(2)).getBareName().toUpperCase());

                    addRelevantMode(relevantLiteral, mode, strength);
                    break;
                }
            }

        }

        @Override
        public void clauseRetracted() {
            throw new UnsupportedOperationException("Not supported yet.");
        }
    }
}
