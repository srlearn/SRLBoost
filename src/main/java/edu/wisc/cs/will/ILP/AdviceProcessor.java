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

    /* Original Relevance statements, prior to generalization.
     *
     * This list contains the original relevance statements prior to generalization.
     * groundedRelevance is a bit of a misnomer, since the relevance may contain variables.
     */
    private final List<RelevantClauseInformation> relevantClauses = new ArrayList<>();

    private final List<RelevantFeatureInformation> relevantFeatures = new ArrayList<>();

    private final List<RelevantModeInformation> relevantModes = new ArrayList<>();

    private final HornClauseContext context;

    private final HandleFOPCstrings stringHandler;

    private final LearnOneClause learnOneClause;

    private int anonymousClauseIndex = 0;

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
        PruneDuplicatesIfTrueRule memberPruneRule = new PruneDuplicatesIfTrueRule(context.getStringHandler().getPredicate("member", 2), memberPruneCondition);
        addPruningRule(memberPruneRule);

        Clause compositeNamePruneCondition = context.getFileParser().parseDefiniteClause("prune(ExistingLiteral, AddedLiteral) :- ilField_Composite_name(W,Name1,Symbol1,S)=ExistingLiteral, ilField_Composite_name(W,Name2,Symbol2,S)=AddedLiteral, Symbol1 == Symbol2, Name2 = Name1.");
        PruneDuplicatesIfTrueRule compositeNamePruneRule = new PruneDuplicatesIfTrueRule(context.getStringHandler().getPredicate("ilField_Composite_name", 4), compositeNamePruneCondition);
        addPruningRule(compositeNamePruneRule);

        Clause sameAsCondition1 = context.getFileParser().parseDefiniteClause("prune(AddedLiteral) :- sameAsIL(W,X,X,S)=AddedLiteral.");
        PruneIfTrueRule sameAsPrune1 = new PruneIfTrueRule(context.getStringHandler().getPredicate("sameAsIL", 4), sameAsCondition1);
        addPruningRule(sameAsPrune1);

        Clause forEachInChainPruneCondition = context.getFileParser().parseDefiniteClause("prune(Literal, Literal).");
        PruneDuplicatesIfTrueRule forEachInChainPruneRule = new PruneDuplicatesIfTrueRule(context.getStringHandler().getPredicate("forEachIn_chain", 7), forEachInChainPruneCondition);
        addPruningRule(forEachInChainPruneRule);

        context.getStringHandler().setVariableIndicator(oldVI);
    }

    /* Returns the active advice for the given examples and relevanceStrength without asserting/retracting.
     */
    private ActiveAdvice getActiveAdvice(RelevanceStrength relevanceStrength, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {
        ActiveAdvice activeAdvice = new ActiveAdvice(stringHandler);

        processRelevantClauses(activeAdvice, relevanceStrength, positiveExamples, negativeExamples);

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

    private void processRelevantClauses(ActiveAdvice activeAdvice, RelevanceStrength relevanceStrength, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {


        // First, make sure that the world/state variable positions are included
        // in the unsplitable set.

        // Filter out duplicate relevance statements that exist on multiple examples.
        MapOfSets<Example, RelevantClauseInformation> filteredGroundedPerPieceMap = createFilteredGroundedPerPieceMap(positiveExamples, negativeExamples);

        // Create the generalized, split, per piece map.
        MapOfSets<Example, RelevantClauseInformation> generalizedPerPieceMap = createPerPieceMap(filteredGroundedPerPieceMap);

        // Create the generalized, split, per example map.
        MapOfSets<Example, RelevantClauseInformation> generalizedPerExampleMap = createPerExampleMap(filteredGroundedPerPieceMap);

        // When we generate clauses, we always generate mega first, then per-single-example, then per-piece.
        // That way, if duplicates occur, the highest relevance levels will be kept.
        List<Clause> megaClauses = generateMegaCombinations(activeAdvice, generalizedPerExampleMap);
        List<Clause> allClauses = new ArrayList<>(megaClauses);

        List<Clause> singleExampleClauses = generateActiveAdviceForRCIs(activeAdvice, generalizedPerExampleMap, "single_example_advice", relevanceStrength, RelevanceStrength.VERY_STRONGLY_RELEVANT, RelevanceStrength.VERY_STRONGLY_RELEVANT_NEG);
        allClauses.addAll(singleExampleClauses);

        List<Clause> singlePieceClauses = generateActiveAdviceForRCIs(activeAdvice, generalizedPerPieceMap, "single_piece_advice", relevanceStrength, RelevanceStrength.STRONGLY_RELEVANT, RelevanceStrength.STRONGLY_RELEVANT_NEG);
        allClauses.addAll(singlePieceClauses);

        if (allClauses.isEmpty()) {
            Utils.print("% [AdviceProcessor]  Generated 0 clauses at relevance level " + relevanceStrength + ".");
            Utils.print("\n");
        }
        else {
            Utils.print("% [AdviceProcessor]  Generated " + allClauses.size() + " clause(s) at relevance level " + relevanceStrength + ":\n");

            boolean first = true;
            for (Clause clause : allClauses) {
                if (!first) {
                    Utils.print("\n");
                }
                first = false;

                RelevanceStrength strongestStrength = RelevanceStrength.getWeakestRelevanceStrength();
                for (ModeInfo modeInfo : activeAdvice.getModeInfo(clause.getDefiniteClauseHead().getPredicateNameAndArity())) {
                    RelevanceStrength rs = modeInfo.strength;
                    if (rs.isStronger(strongestStrength)) {
                        strongestStrength = rs;
                    }
                }

                PrettyPrinterOptions ppo = new PrettyPrinterOptions();
                ppo.setMaximumLiteralsPerLine(1);
                ppo.setSentenceTerminator("");
                ppo.setMaximumIndentationAfterImplication(10);
                ppo.setNewLineAfterImplication(true);

                String s = PrettyPrinter.print(clause, "% [AdviceProcessor]   ", ppo);

                Utils.print(s + "  " + strongestStrength);
            }

            Utils.print("\n\n");
        }

    }

    private MapOfSets<Example, RelevantClauseInformation> createFilteredGroundedPerPieceMap(List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {
        //   ex1 : adviceA
        //   ex1 : adviceB
        //   ex2 : adviceC
        //
        // We get the map:
        //   ex1 => { adviceA, adviceB }
        //   ex2 => { adviceC }
        MapOfSets<Example, RelevantClauseInformation> exampleToAdviceMap = createExampleToAdviceMap(relevantClauses);

        // This will also remove any relevance that is not associate with an current relevanceFromPositiveExample or negative example.
        MapOfSets<Example, RelevantClauseInformation> activeExampleToAdviceMap = createActiveExampleMap(exampleToAdviceMap, positiveExamples, negativeExamples, RelevanceStrength.getWeakestRelevanceStrength());

        return filterDuplicateRelevance(activeExampleToAdviceMap);
    }

    private MapOfSets<Example, RelevantClauseInformation> createPerPieceMap(MapOfSets<Example, RelevantClauseInformation> filteredGroundedPerPieceMap) {

        MapOfSets<Example, RelevantClauseInformation> generalizedPerPieceMap = createExampleToGeneralizedMap(filteredGroundedPerPieceMap);
        //Tag the possible set of output variables on the PerPiece map
        collectOutputVariables(generalizedPerPieceMap);

        return createExampleToSplitVariableMap(generalizedPerPieceMap);
    }

    private MapOfSets<Example, RelevantClauseInformation> createPerExampleMap(MapOfSets<Example, RelevantClauseInformation> filteredGroundedPerPieceMap) {
        MapOfSets<Example, RelevantClauseInformation> grounedPerExampleAdviceMap = createExampleToPerExampleAdviceMap(filteredGroundedPerPieceMap);

        MapOfSets<Example, RelevantClauseInformation> generalizedPerExampleConjunctiveMap = createExampleToGeneralizedMap(grounedPerExampleAdviceMap);
        //Tag the possible set of output variables on the PerExample map
        collectOutputVariables(generalizedPerExampleConjunctiveMap);

        // That way, if duplicates occur, the highest relevance levels will be kept.
        return createExampleToSplitVariableMap(generalizedPerExampleConjunctiveMap);
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
                activeAdvice.addFeatureRelevance(rfi.getPredicateNameAndArity(), rfi.getRelevanceStrength());

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
            uniqueGroundRelevance.put(entry.getValue().getExample(), entry.getValue());
        }

        for (Entry<T, T> entry : negativeGeneralizedRelevance.entrySet()) {
            uniqueGroundRelevance.put(entry.getValue().getExample(), entry.getValue());
        }

        uniqueGroundRelevance.values();

        AllOfFOPC.renameVariablesWhenPrinting = save;


        return uniqueGroundRelevance;
    }

    private <T extends RelevantInformation> MapOfSets<Example, T> createExampleToAdviceMap(List<T> relevantInformationList) {
        MapOfSets<Example, T> exampleToAdviceSetMap = new LinkedMapOfSets<>();

        for (T rci : relevantInformationList) {
            exampleToAdviceSetMap.put(rci.getExample(), rci);
        }

        return exampleToAdviceSetMap;
    }

    private HandleFOPCstrings getStringHandler() {
        return learnOneClause.getStringHandler();
    }

    private void collectOutputVariables(MapOfSets<Example, RelevantClauseInformation> rciMap) {

        for (Set<RelevantClauseInformation> set : rciMap.values()) {
            for (RelevantClauseInformation rci : set) {
                // We assume at this point that the rci only contains clauses

                Sentence s = SentenceCompressor.getCompressedSentence(rci.getSentence());

                if (s instanceof Clause) {
                    Clause clause = (Clause) s;
                    if (clause.getPosLiteralCount() > 0) {
                        Literal lastLiteral = clause.getPosLiteral(clause.getPosLiteralCount() - 1);

                        if (lastLiteral.getArity() > 2) {
                            Variable outputVariable = null;

                            // We are going to cheat here and assume that the last argument
                            // of the last literal is the "State" argument and therefore is
                            // not an output variable.  This should really be based upon the
                            // HandleFOPCstrings.locationOfStateArg...but that would require
                            // that I look up that argument location in the example head and
                            // then trace that argument to determine where it occurs in
                            // the last literal.
                            //
                            // We make the same assumption for the "World" argument too.
                            // Hence we iteration from argity-2 to 1
                            for (int i = lastLiteral.getArity() - 2; i > 0; i--) {
                                Term arg = lastLiteral.getArgument(i);
                                if (arg instanceof Variable) {
                                    outputVariable = (Variable) arg;
                                    break;
                                }
                            }

                            if (outputVariable != null) {
                                rci.addOutputVariable(outputVariable);
                            }
                        }
                    }
                }
                else {
                    Utils.warning("Error collecting advice output variables.  Expected a clause.  Got:\n" + rci.getSentence());
                }

            }
        }
    }

    private MapOfSets<Example, RelevantClauseInformation> createExampleToPerExampleAdviceMap(MapOfSets<Example, RelevantClauseInformation> exampleToAdviceMap) {
        MapOfSets<Example, RelevantClauseInformation> exampleToConjunctionMap = new LinkedMapOfSets<>();

        for (Map.Entry<Example, Set<RelevantClauseInformation>> entry : exampleToAdviceMap.entrySet()) {
            RelevantClauseInformation conjunct = null;

            for (RelevantClauseInformation anRCI : entry.getValue()) {
                if (anRCI.isContainsAllAdvicePieces()) {
                    if (conjunct == null) {
                        conjunct = anRCI;
                    }
                    else {
                        conjunct = conjunct.getConjunction(anRCI);
                    }
                }
            }

            if (conjunct != null) {
                exampleToConjunctionMap.put(entry.getKey(), conjunct);
            }
            else {
                Utils.warning("No advice with all pieces exists for example " + entry.getKey() + ".");
            }
        }

        return exampleToConjunctionMap;
    }

    private MapOfSets<Example, RelevantClauseInformation> createExampleToGeneralizedMap(MapOfSets<Example, RelevantClauseInformation> exampleToGroundedConjunctiveMap) {
        MapOfSets<Example, RelevantClauseInformation> result = new LinkedMapOfSets<>();

        for (Map.Entry<Example, Set<RelevantClauseInformation>> entry : exampleToGroundedConjunctiveMap.entrySet()) {
            Example example = entry.getKey();
            Set<RelevantClauseInformation> groundAdviceForExample = entry.getValue();

            for (RelevantClauseInformation rci : groundAdviceForExample) {
                RelevantClauseInformation newRCI = rci.getGeneralizeRelevantInformation();

                result.put(example, newRCI);
            }
        }

        return result;
    }

    private MapOfSets<Example, RelevantClauseInformation> createExampleToSplitVariableMap(MapOfSets<Example, RelevantClauseInformation> exampleToGeneralizedConjunctiveMap) {

        new LinkedMapOfSets<>();
        MapOfSets<Example, RelevantClauseInformation> result;

        // Don't split for now...
        result = exampleToGeneralizedConjunctiveMap;

        return result;
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

    private List<Clause> generateMegaCombinations(ActiveAdvice activeAdvice, MapOfSets<Example, RelevantClauseInformation> exampleToSplitVariableMap) {

        Map<Example, RelevantClauseInformation> singleExampleConjunctMap = new HashMap<>();

        for (Map.Entry<Example, Set<RelevantClauseInformation>> entry : exampleToSplitVariableMap.entrySet()) {
            RelevantClauseInformation conjunct = null;
            for (RelevantClauseInformation anRCI : entry.getValue()) {
                if (anRCI.isContainsAllAdvicePieces()) {
                    if (conjunct == null) {
                        conjunct = anRCI;
                    }
                    else {
                        conjunct = conjunct.getConjunction(anRCI);
                    }
                }
            }

            if (conjunct != null) {
                conjunct = conjunct.getCompressed();
                singleExampleConjunctMap.put(entry.getKey(), conjunct);
            }
            else {
                Utils.warning("No advice with all pieces exists for example " + entry.getKey() + ".");
            }
        }

        RelevantClauseInformation comboPosAND = null;
        RelevantClauseInformation comboPosOR = null;
        RelevantClauseInformation comboNotPosOR = null;
        RelevantClauseInformation comboNegAND = null;
        RelevantClauseInformation comboNegOR = null;
        RelevantClauseInformation comboNotNegOR = null;

        for (RelevantClauseInformation rci : singleExampleConjunctMap.values()) {
            if (rci.isRelevanceFromPositiveExample()) {
                if (comboPosAND == null) {
                    comboPosAND = rci;
                }
                else {
                    comboPosAND = comboPosAND.getConjunction(rci);
                }

                if (comboPosOR == null) {
                    comboPosOR = rci;
                }
                else {
                    comboPosOR = comboPosOR.getDisjunction(rci);
                }

                if (comboNotPosOR == null) {
                    comboNotPosOR = rci.getNegationByFailure();
                }
                else {
                    comboNotPosOR = comboNotPosOR.getConjunction(rci.getNegationByFailure());
                }
            }
            else {
                if (comboNegAND == null) {
                    comboNegAND = rci;
                }
                else {
                    comboNegAND = comboNegAND.getConjunction(rci);
                }

                if (comboNegOR == null) {
                    comboNegOR = rci;
                }
                else {
                    comboNegOR = comboNegOR.getDisjunction(rci);
                }

                if (comboNotNegOR == null) {
                    comboNotNegOR = rci.getNegationByFailure();
                }
                else {
                    comboNotNegOR = comboNotNegOR.getConjunction(rci.getNegationByFailure());
                }
            }
        }

        if (comboPosAND != null) {
            comboPosAND = comboPosAND.getCompressed();
        }

        if (comboNegAND != null) {
            comboNegAND = comboNegAND.getCompressed();
        }

        List<Clause> assertedClauses = new ArrayList<>();

        RelevantClauseInformation rule;
        RelevantClauseInformation that;

        String predSuffix = "";
        if (!getStringHandler().getInventedPredicateNameSuffix().isEmpty()) {
            predSuffix = getStringHandler().getInventedPredicateNameSuffix();
            if (!predSuffix.startsWith("_")) {
                predSuffix = "_" + predSuffix;
            }
        }

        // At this point, either comboPosAND or comboNegAND must be non-null (possibly both will be non-null).
        // Thus, our logic can reflect that. Also, if comboPosAND != null, then comboNegatedPosOR != null, and
        // if comboNegAND != null, then comboNegatedNegOR != null.

        if (comboPosAND != null) {
            // Below all 8 rules are generated.  However, if the Negative combos are null, only four 
            // will be unique.  I could adjust the logic here, but they
            rule = comboPosAND.getConjunction(comboNotNegOR);
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_posAnd_notNegOr" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            rule = comboPosAND.getNegationByFailure().getConjunction(comboNegAND);
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_notPosAnd_negAnd" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            rule = comboPosOR.getConjunction(comboNotNegOR);
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_posOr_notNegOr" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            rule = comboNotPosOR.getConjunction(comboNegAND);
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_notPosOr_negAnd" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            if (comboNegAND != null) {
                rule = comboPosAND.getConjunction(comboNegAND.getNegationByFailure());
                rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
                activeAdvice.addAdviceClause(this, "mega_posAnd_notNegAnd" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

                rule = comboPosAND.getNegationByFailure().getConjunction(comboNegOR);
                rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
                activeAdvice.addAdviceClause(this, "mega_negPosAnd_negOr" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

                that = comboNegAND.getNegationByFailure();
                rule = comboPosOR.getConjunction(that);
                rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
                activeAdvice.addAdviceClause(this, "mega_posOr_notNegAnd" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

                rule = comboNotPosOR.getConjunction(comboNegOR);
                rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
                activeAdvice.addAdviceClause(this, "mega_negPosOr_negOr" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);
            }

        }
        else if (comboNegAND != null) {
            // At this point, the positive combos will null.  Thus, there are only four negative rules to generate.
            // corresponding directly to comboNegAND and comboNegatedNegOR, since the other four will be
            // redundant.
            rule = comboNegAND.getNegationByFailure();
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_posAnd_notNegAnd" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            rule = comboNegAND;
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_notPosAnd_negAnd" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            rule = comboNotNegOR;
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_posAnd_notNegOr" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            rule = comboNegOR;
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_negPosAnd_negOr" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);
        }

        return assertedClauses;
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

    private List<Clause> generateActiveAdviceForRCIs(ActiveAdvice activeAdvice, MapOfSets<Example, RelevantClauseInformation> rcis, String namePrefix, RelevanceStrength minimumRelevanceStrength, RelevanceStrength positiveClauseStrength, RelevanceStrength negativeClauseStrength) {

        List<Clause> clauses = new ArrayList<>();
        String name;

        String predSuffix = "";
        if (!getStringHandler().getInventedPredicateNameSuffix().isEmpty()) {
            predSuffix = getStringHandler().getInventedPredicateNameSuffix();
            if (!predSuffix.startsWith("_")) {
                predSuffix = "_" + predSuffix;
            }
        }

        for (Set<RelevantClauseInformation> set : rcis.values()) {
            for (RelevantClauseInformation rci : set) {
                if (positiveClauseStrength.isEqualOrStronger(minimumRelevanceStrength)) {
                    name = namePrefix + (anonymousClauseIndex++) + predSuffix;
                    rci.setRelevanceStrength(positiveClauseStrength);
                    activeAdvice.addAdviceClause(this, name, rci, clauses);

                    if (negativeClauseStrength.isEqualOrStronger(minimumRelevanceStrength)) {
                        RelevantClauseInformation not = rci.getNegationByFailure();
                        not.setRelevanceStrength(negativeClauseStrength);
                        name = "not_" + name;
                        activeAdvice.addAdviceClause(this, name, not, clauses);
                    }
                }
            }
        }

        return clauses;
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

        relevantClauses.add(rci);
    }

    private void addRelevantMode(Example example, Literal mode, RelevanceStrength relevanceStrength) {

        RelevantModeInformation rfi = new RelevantModeInformation(example, mode, relevanceStrength);

        if (!relevantModes.contains(rfi)) {
            relevantModes.add(rfi);
        }
    }

    boolean isOutputArgumentsEnabled() {
        return false;
    }

    public HornClauseContext getContext() {
        return learnOneClause.getContext();
    }

    boolean isInliningEnabled() {
        return true;
    }

    boolean isRemoveDuplicateDeterminatesEnabled() {
        return true;
    }

    boolean isVerifyAllPredicateExist() {
        return true;
    }

    boolean isVerifyInputsToFunctionsAsPredAreBoundEnabled() {
        return true;
    }

    boolean isRemoveDoubleNegationEnabled() {
        return true;
    }

    List<PruningRule> getPruningRules() {
        return pruningRules;
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
