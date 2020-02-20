package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;
import edu.wisc.cs.will.FOPC.visitors.ReplaceLiteralsVisitor;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.MapOfSets;

import java.util.*;

/*
 * @author twalker
 */
class NonOperationalExpander {

    private static final CollectNonOperationalLiteralsVisitor COLLECT_NON_OPERATIONAL_LITERALS_VISITOR = new CollectNonOperationalLiteralsVisitor();

    private NonOperationalExpander() {}

    static List<? extends Sentence> getExpandedSentences(HornClauseContext context, Sentence sentence) {

        List<Sentence> results;

        CollectorData collectorData = new CollectorData();

        sentence.accept(COLLECT_NON_OPERATIONAL_LITERALS_VISITOR, collectorData);

        if (collectorData.literals.isEmpty()) {
            results = Collections.singletonList(sentence);
        }
        else {
            List<Clause> expansionCombinations = getNonOperationalCombinations(collectorData.literals, new ExpansionData2(context));

            results = new ArrayList<>();

            for (Clause clause : expansionCombinations) {
                Map<Literal, Literal> replacementMap = getNonOperationalExpansionMap(collectorData.literals, clause.getPositiveLiterals());

                Sentence newSentence = sentence.accept(ReplaceLiteralsVisitor.REPLACE_LITERALS_VISITOR, replacementMap);

                results.add(newSentence);
            }
        }

        return results;
    }

    private static Map<Literal, Literal> getNonOperationalExpansionMap(List<Literal> nonOperationalLiterals, List<Literal> operationalLiterals) {

        Map<Literal, Literal> map = new HashMap<>();

        for (int i = 0; i < nonOperationalLiterals.size(); i++) {
            Literal nonOp = nonOperationalLiterals.get(i);
            Literal op = operationalLiterals.get(i);

            map.put(nonOp, op);
        }

        return map;

    }

    private static List<Clause> getNonOperationalCombinations(List<Literal> nonOps, ExpansionData2 data) {

        List<Clause> result = Collections.EMPTY_LIST;

        if (!nonOps.isEmpty()) {

            List<Literal> firstLiteralExpansion;

            Literal firstLiteral = nonOps.get(0);

            Literal existingMapping = data.getExistingMapping(firstLiteral);

            if (existingMapping != null) {

                firstLiteralExpansion = Collections.singletonList(firstLiteral.getStringHandler().getLiteral(existingMapping, firstLiteral.getArguments()));
            }
            else {
                firstLiteralExpansion = new ArrayList<>();
                Set<PredicateNameAndArity> operationalExpansions = firstLiteral.getPredicateName().getOperationalExpansions(firstLiteral.getArity());

                for (PredicateNameAndArity operationalPredicateNameAndArity : operationalExpansions) {
                    firstLiteralExpansion.add(firstLiteral.getStringHandler().getLiteral(operationalPredicateNameAndArity.getPredicateName(), firstLiteral.getArguments()));
                }
            }

            result = new ArrayList<>();

            for (Literal aFirstExpansion : firstLiteralExpansion) {
                ExpansionData2 newData = new ExpansionData2(data);
                newData.addExistingMapping(firstLiteral, aFirstExpansion);

                List<Clause> restOfExpansions = getNonOperationalCombinations(nonOps.subList(1, nonOps.size()), newData);

                if (restOfExpansions.isEmpty()) {
                    result.add(firstLiteral.getStringHandler().getClause(aFirstExpansion, null));
                }
                else {
                    for (Clause aRestExpansion : restOfExpansions) {
                        List<Literal> newArgs = new ArrayList<>();
                        newArgs.add(aFirstExpansion);
                        newArgs.addAll(aRestExpansion.getPositiveLiterals());

                        result.add(firstLiteral.getStringHandler().getClause(newArgs, null));
                    }
                }
            }

        }

        return result;
    }

    private static class CollectNonOperationalLiteralsVisitor extends DefaultFOPCVisitor<CollectorData> {

        @Override
        public Sentence visitLiteral(Literal literal, CollectorData data) {
            if (literal.getPredicateNameAndArity().isNonOperational()) {
                data.literals.add(literal);
            }
            else if (literal.getStringHandler().isNegationByFailure(literal)) {
                super.visitLiteral(literal, data);
            }

            return null;
        }

        @Override
        public Term visitFunction(Function function, CollectorData data) {
            if (function.getPredicateNameAndArity().isNonOperational()) {
                data.literals.add(function.asLiteral());
            }
            else if (function.getStringHandler().isNegationByFailure(function)) {
                super.visitFunction(function, data);
            }

            return null;
        }
    }

    private static class CollectorData {

        List<Literal> literals = new ArrayList<>();

    }

    private static class ExpansionData2 {

        HornClauseContext context;

        ExpansionData2 parent;

        MapOfSets<PredicateNameAndArity, ExistingExpansion> existingExpansionsMap;

        ExpansionData2(HornClauseContext context) {
            this.context = context;
        }

        ExpansionData2(ExpansionData2 parent) {
            this.parent = parent;
        }

        Literal getExistingMapping(LiteralOrFunction nonOperationLiteral) {
            Literal result = null;

            if (existingExpansionsMap != null) {

                PredicateNameAndArity pnaa = nonOperationLiteral.getPredicateNameAndArity();

                Set<TermAndIndex> set = getFreeTermSet(nonOperationLiteral);

                Set<ExistingExpansion> existingExpansions = existingExpansionsMap.getValues(pnaa);

                if (existingExpansions != null) {
                    for (ExistingExpansion existingExpansion : existingExpansions) {
                        if (existingExpansion.termAndIndices.equals(set)) {
                            // We found an existing expansion, so create a literal and return it.
                            result = nonOperationLiteral.getStringHandler().getLiteral(existingExpansion.expansion.getPredicateName(), nonOperationLiteral.getArguments());
                            break;
                        }
                    }
                }

            }

            if (result == null && parent != null) {
                result = parent.getExistingMapping(nonOperationLiteral);
            }

            return result;
        }

        void addExistingMapping(LiteralOrFunction fromNonOperational, LiteralOrFunction toOperational) {
            if (existingExpansionsMap == null) {
                existingExpansionsMap = new MapOfSets<>();
            }

            existingExpansionsMap.put(fromNonOperational.getPredicateNameAndArity(), new ExistingExpansion(toOperational.getPredicateNameAndArity(), getFreeTermSet(toOperational)));
        }

        private Set<TermAndIndex> getFreeTermSet(LiteralOrFunction literal) {
            Set<TermAndIndex> set = new HashSet<>();

            List<Term> arguments = literal.getArguments();

            for (int i = 0; i < arguments.size(); i++) {
                Term t = arguments.get(i);

                if (!t.isGrounded()) {
                    set.add(new TermAndIndex(t, i));
                }
            }

            return set;
        }
    }

    private static class ExistingExpansion {

        PredicateNameAndArity expansion;

        Set<TermAndIndex> termAndIndices;

        ExistingExpansion(PredicateNameAndArity expansion, Set<TermAndIndex> termAndIndices) {
            this.expansion = expansion;
            this.termAndIndices = termAndIndices;
        }

        @Override
        public String toString() {
            return "ExistingExpansion{" + "expansion=" + expansion + "termAndIndices=" + termAndIndices + '}';
        }
    }

    private static class TermAndIndex {

        Term term;

        int index;

        TermAndIndex(Term term, int index) {
            this.term = term;
            this.index = index;
        }

        @Override
        public boolean equals(Object obj) {
            if (obj == null) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            final TermAndIndex other = (TermAndIndex) obj;
            if (!Objects.equals(this.term, other.term)) {
                return false;
            }
            return this.index == other.index;
        }

        @Override
        public int hashCode() {
            int hash = 5;
            hash = 37 * hash + (this.term != null ? this.term.hashCode() : 0);
            hash = 37 * hash + this.index;
            return hash;
        }

        @Override
        public String toString() {
            return term + "@" + index;
        }
    }
}
