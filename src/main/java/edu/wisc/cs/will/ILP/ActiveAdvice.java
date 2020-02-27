package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.*;
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
class ActiveAdvice {

    private final HandleFOPCstrings stringHandler;

    private final MapOfSets<PredicateNameAndArity, ModeInfo> adviceModes = new MapOfSets<>();

    private final MapOfSets<PredicateNameAndArity, ClauseInfo> clauses = new LinkedMapOfSets<>();

    private final MapOfLists<PredicateNameAndArity, Clause> supportClauses = new MapOfLists<>();

    private final Map<PredicateNameAndArity, RelevanceInfo> adviceFeaturesAndStrengths = new LinkedHashMap<>();

    ActiveAdvice(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;
    }

    void addAdviceMode(AdviceProcessor ap, RelevantModeInformation rci) {
        PredicateNameAndArity pnaa = rci.getPredicateNameAndArity();

        // If these contain non-operations, we need to expand them just
        // like we do during addAdviceClause.

        ConnectedSentence implication = rci.getSentence(ap.getContext());
        Sentence body = implication.getSentenceA();
        Literal head = ((DefiniteClause) implication.getSentenceB()).getDefiniteClauseHead();

        body = Inliner.getInlinedSentence(body, ap.getContext());
        body = DuplicateDeterminateRemover.removeDuplicates(body);

        // TODO(@hayesall): `ap.getContext()` is the only use for `getExpandedSentences()`
        List<? extends Sentence> expansions = NonOperationalExpander.getExpandedSentences(body);

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

    public MapOfSets<PredicateNameAndArity, ClauseInfo> getClauses() {
        return clauses;
    }

    void addFeatureRelevance(RelevanceStrength value) {
        adviceFeaturesAndStrengths.put(null, new RelevanceInfo(value));
    }

    private void addModeAndRelevanceStrength(PredicateNameAndArity predicate, List<Term> signature, List<TypeSpec> headSpecList, RelevanceStrength relevanceStrength) {
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

        final double cost = Double.NaN;

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

        RelevanceInfo(RelevanceStrength strength) {
            this.predicate = null;
            this.strength = strength;
        }
    }

    public static class ClauseInfo {

        private Clause clause;

        final RelevanceStrength strength;

        ClauseInfo(Clause clause, RelevanceStrength strength) {
            // TODO(@hayesall): Constructor is never used.
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

}
