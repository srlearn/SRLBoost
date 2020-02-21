package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;
import edu.wisc.cs.will.FOPC.visitors.DefiniteClauseCostAggregator;
import edu.wisc.cs.will.FOPC.visitors.DuplicateDeterminateRemover;
import edu.wisc.cs.will.FOPC.visitors.Inliner;
import edu.wisc.cs.will.Utils.LinkedMapOfSets;
import edu.wisc.cs.will.Utils.MapOfLists;
import edu.wisc.cs.will.Utils.MapOfSets;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;


/*
 * @author twalker
 */
public class ActiveAdvice {

    private static final CNFClauseCollector CLAUSE_COLLECTOR = new CNFClauseCollector();

    private final HandleFOPCstrings stringHandler;

    private final MapOfSets<PredicateNameAndArity, ModeInfo> adviceModes = new MapOfSets<>();

    private final MapOfSets<PredicateNameAndArity, ClauseInfo> clauses = new LinkedMapOfSets<>();

    private final MapOfLists<PredicateNameAndArity, Clause> supportClauses = new MapOfLists<>();

    private final Map<PredicateNameAndArity, RelevanceInfo> adviceFeaturesAndStrengths = new LinkedHashMap<>();

    ActiveAdvice(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;
    }

    void addAdviceClause(AdviceProcessor ap, String name, RelevantClauseInformation rci, List<Clause> clauses) throws IllegalArgumentException {

        if (ap.isInliningEnabled()) {
            rci = rci.getInlined(ap.getContext());
        }

        // When removing double negation by failures
        // and removing duplicate determinates, we have to iteration
        // back and forth since each simplification may result
        // in additional simplications by the other visitor.
        while (true) {
            RelevantClauseInformation start = rci;
            if (ap.isRemoveDoubleNegationEnabled()) {
                rci = rci.removeDoubleNegations();
            }

            if (ap.isRemoveDuplicateDeterminatesEnabled()) {
                rci = rci.removeDuplicateDeterminates();
            }

            rci = rci.applyPruningRules(ap);

            if (start.isEquivalentUptoVariableRenaming(rci)) {
                break;
            }
        }

        MapOfLists<PredicateNameAndArity, Clause> supportClausesForExpansions = new MapOfLists<>();
        List<RelevantClauseInformation> expandedRCIs = rci.expandNonOperationalPredicates(ap.getContext());

        // We will add all of the support clauses...just for the hell of it...
        for (Map.Entry<PredicateNameAndArity, List<Clause>> entry : supportClausesForExpansions.entrySet()) {
            if (!supportClauses.containsKey(entry.getKey())) {
                supportClauses.addAllValues(entry.getKey(), entry.getValue());
            }
        }

        int count = 0;
        for (RelevantClauseInformation expandedRCI : expandedRCIs) {
            String expandedName = name;
            if (expandedRCIs.size() != 1) {
                expandedName = name + "_op" + (count++);
            }

            expandedRCI = expandedRCI.getCompressed();
            Sentence sentence = expandedRCI.getSentence();

            Sentence cnf = sentence.getConjunctiveNormalForm();  // This may still have AND connectives.
            Sentence compressedCNF = SentenceCompressor.getCompressedSentence(cnf);

            // Determine the final output variables...
            determineOutputVariables(ap, rci, compressedCNF);

            compressedCNF.collectAllVariables();

            Example example = expandedRCI.example;
            List<TypeSpec> exampleTypeSpecs = example.getTypeSpecs();

            PredicateName pn = stringHandler.getPredicateName(expandedName);
            RelevanceStrength rs = expandedRCI.getFinalRelevanceStrength();

            List<Term> headArguments = new ArrayList<>();
            List<TypeSpec> headSpecList = new ArrayList<>();

            // Create the head arguments.
            // Only add terms that are actually used in the body somewhere...
            for (int i = 0; i < example.getArity(); i++) {
                Term term = example.getArgument(i);
                headArguments.add(term);
                headSpecList.add(exampleTypeSpecs.get(i));
            }

            Literal head = stringHandler.getLiteral(pn, headArguments);
            PredicateNameAndArity predicateNameAndArity = head.getPredicateNameAndArity();

            Sentence impliedSentence = stringHandler.getConnectedSentence(compressedCNF, ConnectiveName.IMPLIES, head);
            List<Clause> impliedClauses = impliedSentence.convertToClausalForm();

            boolean duplicate = false;

            // Check for duplicate clauses.
            // We don't check disjunct clause cause it is hard once we have converted
            // to clausal form.  Unfortunatedly, we don't store the non-clausal implied sentence,
            // so we can't check for duplicates before clausal convertion.
            if (impliedClauses.size() == 1) {
                Clause theNewClause = impliedClauses.get(0);
                assert clauses != null;
                for (Clause existing : clauses) {
                    if (areClausesEqualUptoHeadAndVariableRenaming(existing, theNewClause)) {
                        duplicate = true;
                        break;
                    }
                }
            }

            if (!duplicate) {
                RelevanceStrength strength = expandedRCI.getFinalRelevanceStrength();

                if (expandedRCI.getTypeSpecList() != null) {  // TODO SHOULD WE BE DOING THE setRelevance, add, mark, assert above if this fails?

                    List<Term> signature = new ArrayList<>();
                    for (int i = 0; i < head.getArity(); i++) {
                        signature.add(stringHandler.getStringConstant("constant"));
                    }

                    headSpecList = new ArrayList<>(expandedRCI.getTypeSpecList());

                    ModeInfo mi = addModeAndRelevanceStrength(predicateNameAndArity, signature, headSpecList, rs);

                    double contentsCost = 0;
                    double cost = strength.defaultCost();

                    for (Clause clause : impliedClauses) {
                        // Calculate the average cost over all literals in the clause and across clauses for ORs.
                        contentsCost = DefiniteClauseCostAggregator.PREDICATE_COST_AGGREGATOR.getAggregateCost(DefiniteClauseCostAggregator.AggregationMode.MEAN, clause) / impliedClauses.size();

                        addClause(clause, strength);

                        if (clauses != null) {
                            clauses.add(clause);
                        }
                    }

                    mi.cost = cost + 1e-5 * contentsCost;
                }
            }
        }
    }

    void addAdviceMode(AdviceProcessor ap, RelevantModeInformation rci) {
        PredicateNameAndArity pnaa = rci.getPredicateNameAndArity();

        // If these contain non-operations, we need to expand them just
        // like we do during addAdviceClause.

        ConnectedSentence implication = rci.getSentence(ap.getContext());
        Sentence body = implication.getSentenceA();
        Literal head = ((DefiniteClause) implication.getSentenceB()).getDefiniteClauseHead();


        if (ap.isInliningEnabled()) {
            body = Inliner.getInlinedSentence(body, ap.getContext());
        }
        if (ap.isRemoveDuplicateDeterminatesEnabled()) {
            body = DuplicateDeterminateRemover.removeDuplicates(body);
        }

        List<? extends Sentence> expansions = NonOperationalExpander.getExpandedSentences(ap.getContext(), body);

        if (expansions.size() == 1 && expansions.get(0).equals(body)) {
            // No sentences...
            addModeAndRelevanceStrength(pnaa, rci.getSignature(), rci.getTypeSpecs(), rci.getRelevanceStrength());
        }
        else {
            // We actually did some expansions here...
            int opIndex = 0;
            for (Sentence anExpansion : expansions) {
                anExpansion = SentenceCompressor.getCompressedSentence(anExpansion);
                anExpansion = anExpansion.getConjunctiveNormalForm();  // This may still have AND connectives.
                anExpansion = SentenceCompressor.getCompressedSentence(anExpansion); // We might need to compress again.  This should probably be built into getCNF();

                Sentence newImpliedSentence = stringHandler.getConnectedSentence(anExpansion, ConnectiveName.IMPLIES, head);
                List<Clause> impliedClauses = newImpliedSentence.convertToClausalForm();

                PredicateName newName = newImpliedSentence.getStringHandler().getPredicateName(pnaa.getPredicateName().name + "_op" + (opIndex++));

                // Finally, assemble the new clause...
                for (Clause newClause : impliedClauses) {
                    Literal newHead = ap.getContext().getStringHandler().getLiteral(newName, head.getArguments());
                    newClause = newClause.getStringHandler().getClause(Collections.singletonList(newHead), newClause.getNegativeLiterals());

                    ap.getContext().assertDefiniteClause(newClause);

                }

                addModeAndRelevanceStrength(new PredicateNameAndArity(newName, head.getArity()), rci.getSignature(), rci.getTypeSpecs(), rci.getRelevanceStrength());
            }
        }

    }

    private void addClause(Clause clause, RelevanceStrength strength) {
        clauses.put(clause.getDefiniteClauseHead().getPredicateNameAndArity(), new ClauseInfo(clause, strength));
    }

    public MapOfSets<PredicateNameAndArity, ClauseInfo> getClauses() {
        return clauses;
    }

    void addFeatureRelevance(PredicateNameAndArity key, RelevanceStrength value) {
        adviceFeaturesAndStrengths.put(key, new RelevanceInfo(key, value));
    }

    private ModeInfo addModeAndRelevanceStrength(PredicateNameAndArity predicate, List<Term> signature, List<TypeSpec> headSpecList, RelevanceStrength relevanceStrength) {
        ModeInfo mi = new ModeInfo(predicate, signature, headSpecList, relevanceStrength);

        Set<ModeInfo> existingModeInfos = adviceModes.getValues(predicate);

        boolean add = true;
        if (existingModeInfos != null) {
            for (Iterator<ModeInfo> it = existingModeInfos.iterator(); it.hasNext();) {
                ModeInfo modeInfo = it.next();
                if (modeInfo.equals(mi)) {
                    if (modeInfo.strength.isWeaker(relevanceStrength)) {
                        it.remove();
                    }
                    else {
                        add = false;
                    }
                    break;
                }
            }
        }
        if (add) {
            adviceModes.put(predicate, mi);
        }


        return mi;
    }

    Set<ModeInfo> getModeInfo(PredicateNameAndArity key) {
        return adviceModes.getValues(key);
    }

    public Iterable<ModeInfo> getModes() {
        return adviceModes;
    }

    Collection<RelevanceInfo> getFeatureRelevances() {
        return adviceFeaturesAndStrengths.values();
    }

    MapOfLists<PredicateNameAndArity, Clause> getSupportClauses() {
        return supportClauses;
    }

    private boolean areClausesEqualUptoHeadAndVariableRenaming(Clause clause1, Clause clause2) {

        Literal newHead1 = clause1.getStringHandler().getLiteral("head", clause1.getDefiniteClauseHead().getArguments());
        clause1 = clause1.getStringHandler().getClause(Collections.singletonList(newHead1), clause1.getNegativeLiterals());

        Literal newHead2 = clause2.getStringHandler().getLiteral("head", clause2.getDefiniteClauseHead().getArguments());
        clause2 = clause2.getStringHandler().getClause(Collections.singletonList(newHead2), clause2.getNegativeLiterals());

        return clause1.isEquivalentUptoVariableRenaming(clause2, new BindingList()) != null;
    }

    private void determineOutputVariables(AdviceProcessor ap, RelevantClauseInformation rci, Sentence cnf) {

        Variable outputVariable = null;

        if (ap.isOutputArgumentsEnabled()) {
            List<Clause> separatedClauses = CLAUSE_COLLECTOR.getClauses(cnf);

            Set<Variable> allPossibleOutputVariables = rci.getOutputVariables();

            for (Clause clause : separatedClauses) {
                Variable last = getLastOutputVariable(clause, allPossibleOutputVariables);
                if (last != null) {
                    if (outputVariable == null) {
                        outputVariable = last;
                    }
                    else if (!last.equals(outputVariable)) {
                        outputVariable = null;
                        Utils.println("% [AdviceProcessor] Unable to match last output variables in OR-ed clause.");
                        break;
                    }
                }
            }

            if (outputVariable != null) {
                rci.getExample().collectAllVariables();
            }
            // If the output variable is already in the example head, just ignore it
            // since it will be added naturally anyway.
        }
    }

    /* Returns the variable, from a set of possible variables, that occurs last in a clause.
     */
    private Variable getLastOutputVariable(Clause clause, Set<Variable> possibleLastVariables) {

        for (int i = clause.getPosLiteralCount() - 1; i >= 0; i--) {
            Literal literal = clause.getPosLiteral(i);
            for (int j = literal.getArity() - 1; j >= 0; j--) {
                Term term = literal.getArgument(j);

                if (term instanceof Variable) {
                    Variable v = (Variable) term;
                    if (possibleLastVariables.contains(v)) {
                        return v;
                    }
                }
            }
        }

        return null;
    }

    @Override
    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();

        stringBuilder.append("ActiveAdvice:\n");
        stringBuilder.append("  Advice Clauses:\n");

        for (Set<ClauseInfo> set : clauses.values()) {
            for (ClauseInfo clauseInfo : set) {
                stringBuilder.append(clauseInfo).append(".\n\n");
            }
        }

        stringBuilder.append("  Advice Modes:\n");

        for (ModeInfo modeInfo : adviceModes) {
            stringBuilder.append("    ").append(modeInfo).append(".\n");
        }

        return stringBuilder.toString();
    }

    public static class ModeInfo {

        final PredicateNameAndArity predicate;

        final List<Term> signature;

        final List<TypeSpec> specs;

        final RelevanceStrength strength;

        double cost = Double.NaN;

        ModeInfo(PredicateNameAndArity predicate, List<Term> signature, List<TypeSpec> specs, RelevanceStrength strength) {
            this.predicate = predicate;
            this.signature = signature;
            this.specs = specs;
            this.strength = strength;
        }

        @Override
        public String toString() {
            return predicate.getPredicateName().name + "(" + Utils.toString(specs, ", ") + "), " + strength;
        }

        @Override
        public boolean equals(Object obj) {
            if (obj == null) {
                return false;
            }
            return getClass() == obj.getClass();
        }

        @Override
        public int hashCode() {
            int hash = 3;
            hash = 37 * hash + (this.signature != null ? this.signature.hashCode() : 0);
            hash = 37 * hash + (this.specs != null ? this.specs.hashCode() : 0);
            hash = 37 * hash + (this.strength != null ? this.strength.hashCode() : 0);
            return hash;
        }
    }

    static class RelevanceInfo {

        final PredicateNameAndArity predicate;

        final RelevanceStrength strength;

        RelevanceInfo(PredicateNameAndArity predicate, RelevanceStrength strength) {
            this.predicate = predicate;
            this.strength = strength;
        }
    }

    public static class ClauseInfo {

        private Clause clause;

        final RelevanceStrength strength;

        ClauseInfo(Clause clause, RelevanceStrength strength) {
            this.setClause(clause);
            this.strength = strength;
        }

        @Override
        public boolean equals(Object obj) {
            if (obj == null) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            final ClauseInfo other = (ClauseInfo) obj;
            if (this.getClause() != other.getClause() && (this.getClause() == null || !this.getClause().equals(other.getClause()))) {
                return false;
            }
            return this.strength == other.strength;
        }

        @Override
        public int hashCode() {
            int hash = 3;
            hash = 37 * hash + (this.getClause() != null ? this.getClause().hashCode() : 0);
            hash = 37 * hash + (this.strength != null ? this.strength.hashCode() : 0);
            return hash;
        }

        void setClause(Clause clause) {
			this.clause = clause;
		}

		public Clause getClause() {
			return clause;
		}

		@Override
        public String toString() {
            return getClause().toPrettyString("    ", Integer.MAX_VALUE, new BindingList()) + ", " + strength;
        }
    }

    public static class CNFClauseCollector extends DefaultFOPCVisitor<List<Clause>> {

        List<Clause> getClauses(Sentence compressCNFSentence) {
            List<Clause> list = new ArrayList<>();

            compressCNFSentence.accept(this, list);

            return list;
        }

        @Override
        public Sentence visitClause(Clause clause, List<Clause> data) {

            data.add(clause);

            return super.visitClause(clause, data);
        }
    }
}
