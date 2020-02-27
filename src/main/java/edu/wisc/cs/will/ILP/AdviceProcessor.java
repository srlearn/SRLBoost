package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.ILP.ActiveAdvice.ModeInfo;
import edu.wisc.cs.will.ResThmProver.AssertRetractListener;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClausebase;
import edu.wisc.cs.will.Utils.LinkedMapOfSets;
import edu.wisc.cs.will.Utils.MapOfSets;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;
import java.util.Map.Entry;

/*
 * @author twalker
 */
public class AdviceProcessor {

    private final List<RelevantFeatureInformation> relevantFeatures = new ArrayList<>();

    private final List<RelevantModeInformation> relevantModes = new ArrayList<>();

    private final HornClauseContext context;

    private final HandleFOPCstrings stringHandler;

    private final LearnOneClause learnOneClause;

    private Set<PredicateNameAndArity> assertedRelevanceModes = new HashSet<>();

    private Set<PredicateNameAndArity> assertedRelevanceClauses = new HashSet<>();

    private MutuallyExclusiveModeConstraint constraint = null;

    private List<PruningRule> pruningRules = null;

    public AdviceProcessor(HornClauseContext context, LearnOneClause learnOneClause) {

        this.context = context;
        this.stringHandler = context.getStringHandler();
        this.learnOneClause = learnOneClause;

        setupRelevantClauseListener(this.context);

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

    /* Returns the active advice for the given examples and relevanceStrength without asserting/retracting.
     */
    private ActiveAdvice getActiveAdvice(RelevanceStrength relevanceStrength, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {
        ActiveAdvice activeAdvice = new ActiveAdvice(stringHandler);

        processRelevantClauses(relevanceStrength);

        processRelevantFeatures(activeAdvice, relevanceStrength, positiveExamples, negativeExamples);

        processRelevantModes(activeAdvice, relevanceStrength, positiveExamples, negativeExamples);

        return activeAdvice;
    }

    /* Generalizes the relevance statements and asserts the clauses and relevance into the context.
     *
     * The positiveExamples and negativeExample collections are required to determine
     */
    ActiveAdvice processAdvice(RelevanceStrength relevanceStrength, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {

        retractRelevanceAdvice();

        ActiveAdvice activeAdvice = getActiveAdvice(relevanceStrength, positiveExamples, negativeExamples);

        assertRelevanceAdvice(activeAdvice, relevanceStrength);
        
        return activeAdvice;
    }

    private void processRelevantClauses(RelevanceStrength relevanceStrength) {
        // TODO(@hayesall): `allClauses.isEmpty()` always appears to be true when I run on each data set.
        Utils.print("% [AdviceProcessor]  Generated 0 clauses at relevance level " + relevanceStrength + ".");
        Utils.print("\n");
    }

    private void processRelevantFeatures(ActiveAdvice activeAdvice, RelevanceStrength relevanceStrength, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {

        MapOfSets<Example, RelevantFeatureInformation> exampleToAdviceMap = createExampleToAdviceMap(relevantFeatures);

        // Update the ground examples relevanceFromPositiveExample/negative status according to the positiveExample/negativeExamples lists.
        // This will also remove any relevance that is not associate with an current relevanceFromPositiveExample or negative example.
        MapOfSets<Example, RelevantFeatureInformation> activeExampleToAdviceMap = createActiveExampleMap(exampleToAdviceMap, positiveExamples, negativeExamples, relevanceStrength);

        // Filter out duplicate relevance statements that exist on multiple examples.
        MapOfSets<Example, RelevantFeatureInformation> filteredGroundedRelevance = filterDuplicateRelevance(activeExampleToAdviceMap);

        for (Set<RelevantFeatureInformation> set : filteredGroundedRelevance.values()) {
            for (RelevantFeatureInformation rfi : set) {
                activeAdvice.addFeatureRelevance(rfi.getRelevanceStrength());

            }
        }
    }

    private void processRelevantModes(ActiveAdvice activeAdvice, RelevanceStrength relevanceStrength, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {

        MapOfSets<Example, RelevantModeInformation> exampleToAdviceMap = createExampleToAdviceMap(relevantModes);


        // Update the ground examples relevanceFromPositiveExample/negative status according to the positiveExample/negativeExamples lists.
        // This will also remove any relevance that is not associate with an current relevanceFromPositiveExample or negative example.
        MapOfSets<Example, RelevantModeInformation> activeExampleToAdviceMap = createActiveExampleMap(exampleToAdviceMap, positiveExamples, negativeExamples, relevanceStrength);


        // Filter out duplicate relevance statements that exist on multiple examples.
        MapOfSets<Example, RelevantModeInformation> filteredGroundedRelevance = filterDuplicateRelevance(activeExampleToAdviceMap);


        for (Set<RelevantModeInformation> set : filteredGroundedRelevance.values()) {
            for (RelevantModeInformation rmi : set) {
                rmi.getPredicateNameAndArity();
                rmi.getSignature();
                rmi.getTypeSpecs();
                RelevanceStrength rs = rmi.getRelevanceStrength();

                if ( relevanceStrength == null || relevanceStrength.isEqualOrWeaker(rs) ) {
                    activeAdvice.addAdviceMode(this, rmi);
                }
            }
        }
    }

    private <T extends RelevantInformation> MapOfSets<Example, T> filterDuplicateRelevance(MapOfSets<Example, T> activeExampleToAdviceMap) {

        Map<T, T> positiveGeneralizedRelevance = new HashMap<>();
        Map<T, T> negativeGeneralizedRelevance = new HashMap<>();

        boolean save = AllOfFOPC.renameVariablesWhenPrinting;
        AllOfFOPC.renameVariablesWhenPrinting = true;

        for (Map.Entry<Example, Set<T>> entry : activeExampleToAdviceMap.entrySet()) {
            for (T rci : entry.getValue()) {

                T generalizedRCI = (T) rci.getGeneralizeRelevantInformation();

                if (!generalizedRCI.isValidAdvice(this)) {

                }
                else {

                    Map<T, T> appropriateList = rci.isRelevanceFromPositiveExample() ? positiveGeneralizedRelevance : negativeGeneralizedRelevance;

                    boolean addIt = false;
                    if (getIndexOfSubsumedRelevanceClauseInformation(appropriateList.keySet(), generalizedRCI) == -1) {

                        addIt = true;

                    }

                    if (addIt) {
                        // First remove any RCI that the new one subsums.
                        for (Iterator<Entry<T, T>> it = appropriateList.entrySet().iterator(); it.hasNext();) {
                            Entry<T, T> e = it.next();
                            RelevantInformation relevantInformation = e.getKey();
                            if (generalizedRCI.subsumes(relevantInformation)) {
                                it.remove();
                            }
                        }

                        appropriateList.put(generalizedRCI, rci);
                    }
                }
            }
        }

        MapOfSets<Example, T> uniqueGroundRelevance = new LinkedMapOfSets<>();

        for (Entry<T, T> entry : positiveGeneralizedRelevance.entrySet()) {
            uniqueGroundRelevance.put(null, entry.getValue());
        }

        for (Entry<T, T> entry : negativeGeneralizedRelevance.entrySet()) {
            uniqueGroundRelevance.put(null, entry.getValue());
        }

        uniqueGroundRelevance.values();

        AllOfFOPC.renameVariablesWhenPrinting = save;


        return uniqueGroundRelevance;
    }

    private <T extends RelevantInformation> MapOfSets<Example, T> createExampleToAdviceMap(List<T> relevantInformationList) {
        MapOfSets<Example, T> exampleToAdviceSetMap = new LinkedMapOfSets<>();

        for (T rci : relevantInformationList) {
            exampleToAdviceSetMap.put(null, rci);
        }

        return exampleToAdviceSetMap;
    }

    private HandleFOPCstrings getStringHandler() {
        return learnOneClause.getStringHandler();
    }

    private <T extends RelevantInformation> MapOfSets<Example, T> createActiveExampleMap(MapOfSets<Example, T> exampleToAdviceMap, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples, RelevanceStrength minimumRelevance) {

        MapOfSets<Example, T> result = new LinkedMapOfSets<>();

        for (Example example : positiveExamples) {
            Example newExample = example.copy(false);
            Set<T> set = exampleToAdviceMap.getValues(newExample);
            if (set != null) {
                for (T rci : set) {

                    if (rci.isValidAdvice(this)) {
                        rci = (T) rci.copy();
                        rci.setRelevanceFromPositiveExample(true);
                        if (rci.getRelevanceStrength().isEqualOrStronger(minimumRelevance)) {
                            result.put(newExample, rci);
                        }
                    }
                }
            }
        }

        for (Example example : negativeExamples) {
            Example newExample = example.copy(false);
            Set<T> set = exampleToAdviceMap.getValues(newExample);
            if (set != null) {
                for (T rci : set) {
                    if (rci.isValidAdvice(this)) {
                        rci = (T) rci.copy();
                        rci.setRelevanceFromPositiveExample(false);
                        if (rci.getRelevanceStrength().isEqualOrStronger(minimumRelevance)) {
                            result.put(newExample, rci);
                        }
                    }
                }
            }
        }

        return result;
    }

    private int getIndexOfSubsumedRelevanceClauseInformation(Collection<? extends RelevantInformation> list, RelevantInformation info) {

        int index = -1;

        int count = 0;

        for (RelevantInformation rci : list) {
            if (rci.subsumes(info)) {

                index = count;
                break;
            }
            count++;
        }
        return index;
    }

    void retractRelevanceAdvice() {
        if (assertedRelevanceModes.size() > 0) {
            if (learnOneClause != null && constraint != null) {
                learnOneClause.removeModeConstraint(constraint);
                constraint = null;
            }
            for (PredicateNameAndArity predicateNameAndArity : assertedRelevanceModes) {
                stringHandler.removePredicateWithKnownModes(predicateNameAndArity);
                if (learnOneClause != null) {
                    learnOneClause.removeBodyMode(predicateNameAndArity);
                }
            }
        }

        if (assertedRelevanceClauses.size() > 0) {
            for (PredicateNameAndArity predicateNameAndArity : assertedRelevanceClauses) {
                context.getClausebase().retractAllClausesForPredicate(predicateNameAndArity);
            }
            assertedRelevanceClauses = new HashSet<>();
        }

        else if (Utils.getSizeSafely(assertedRelevanceModes) > 0) {
            Utils.println("% [AdviceProcessor] retractRelevanceAdvice: there are " + Utils.comma(assertedRelevanceModes) + " assertedRelevanceModes to retract.");
        }
        assertedRelevanceModes = new HashSet<>();
        assertedRelevanceClauses = new HashSet<>();
    }

    private void assertRelevanceAdvice(ActiveAdvice activeAdvice, RelevanceStrength minimumStrength) {

        for (ActiveAdvice.RelevanceInfo relevanceInfo : activeAdvice.getFeatureRelevances()) {
            if (relevanceInfo.strength.isEqualOrStronger(minimumStrength)) {
                PredicateNameAndArity pnaa = relevanceInfo.predicate;
                pnaa.getPredicateName().getRelevance(pnaa.getArity());
                getStringHandler().setRelevance(pnaa.getPredicateName(), pnaa.getArity(), relevanceInfo.strength);
            }
        }

        for (ModeInfo modeInfo : activeAdvice.getModes()) {
            if (modeInfo.strength.isEqualOrStronger(minimumStrength)) {
                if (assertedRelevanceModes.contains(modeInfo.predicate)) {
                    System.out.println("Doh!");
                }
                stringHandler.recordModeWithTypes(modeInfo.predicate, modeInfo.signature, modeInfo.specs, 1, Integer.MAX_VALUE, false);
                if (!Double.isNaN(modeInfo.cost)) {
                    modeInfo.predicate.setCost(modeInfo.cost);
                }
                if (learnOneClause != null) {
                    learnOneClause.addBodyMode(modeInfo.predicate);
                }
                stringHandler.setRelevance(modeInfo.predicate.getPredicateName(), modeInfo.predicate.getArity(), modeInfo.strength);
                assertedRelevanceModes.add(modeInfo.predicate);
                if (!modeInfo.predicate.isInlined()) {
                    modeInfo.predicate.markAsSupportingPredicate(true);
                }
            }
        }

        for (Map.Entry<PredicateNameAndArity, Set<ActiveAdvice.ClauseInfo>> entry : activeAdvice.getClauses().entrySet()) {
            if (!context.getClausebase().checkForPossibleMatchingBackgroundKnowledge(entry.getKey().getPredicateName(), entry.getKey().getArity())) {
                for (ActiveAdvice.ClauseInfo clauseInfo : entry.getValue()) {
                    if (clauseInfo.strength.isEqualOrStronger(minimumStrength)) {

                        context.assertDefiniteClause(clauseInfo.getClause());

                        assertedRelevanceClauses.add(clauseInfo.getClause().getDefiniteClauseHead().getPredicateNameAndArity());

                    }
                }
            }
        }

        for (List<Clause> list : activeAdvice.getSupportClauses().values()) {
            for (Clause clause : list) {
                if (!context.getClausebase().checkForPossibleMatchingBackgroundKnowledge(clause.getDefiniteClauseHead().predicateName, clause.getDefiniteClauseHead().getArity())) {

                    context.assertDefiniteClause(clause);

                    assertedRelevanceClauses.add(clause.getDefiniteClauseHead().getPredicateNameAndArity());

                }
            }
        }


        applyModeConstraint();

    }

    private void applyModeConstraint() {

        if (learnOneClause != null) {
            if (constraint != null) {
                learnOneClause.removeModeConstraint(constraint);
            }
            constraint = new MutuallyExclusiveModeConstraint(assertedRelevanceModes);
            learnOneClause.addModeConstraint(constraint);
        }
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
