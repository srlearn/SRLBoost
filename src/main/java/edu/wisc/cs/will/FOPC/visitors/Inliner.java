package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;

import java.util.*;

/*
 * @author twalker
 */
public class Inliner {

    private static final InlinerVisitor INLINER_VISITOR = new InlinerVisitor();

    /* Returns the lined version of the sentence.
     *
     * If supportClauses is non-null, the support clauses encountered (including the
     * clauses mark as inlined but can't be inlined for some reason) will be placed into
     * the supportClauses map.
     */
    public static Sentence getInlinedSentence(Sentence sentence, HornClauseContext context) {
        return sentence.accept(INLINER_VISITOR, new InlineData(context));
    }

    private static class InlinerVisitor extends DefaultFOPCVisitor<InlineData> {

        @Override
        public Clause visitClause(Clause clause, InlineData data) {

            // We have to make some assumptions as to what kinds of clauses
            // we might encountere here.

            // 0. An empty clause.
            //    Return the original clause.
            // 1. A clause with positive literals and no negative literals.
            //      Inline all the positive literals.
            // 2. A clause with negative literals and no positive literals.
            //      Inline all the negative literals.
            // 3. A definite rule.
            //      Inline the body, leave the head.
            // 4. A mix of positive literals and negative literals.
            //      Throw an Unsupport exception.

            Clause result;

            if (clause.getPosLiteralCount() > 0 && clause.getNegLiteralCount() == 0) {

                List<Literal> expandedLiterals = new ArrayList<>();
                for (Literal literal : clause.getPositiveLiterals()) {
                    Clause expansion = (Clause) literal.accept(this, data);
                    expandedLiterals.addAll(expansion.getPositiveLiterals());
                }

                result = clause.getStringHandler().getClause(expandedLiterals, null);
            }
            else if ((clause.getPosLiteralCount() == 0 && clause.getNegLiteralCount() > 0) || clause.isDefiniteClauseRule()) {
                // We can catch both case 2 & 3 here.  In the case of two, the head will just be null.

                List<Literal> expandedLiterals = new ArrayList<>();
                for (Literal literal : clause.getNegativeLiterals()) {
                    Clause expansion = (Clause) literal.accept(this, data);
                    // Note: even though we are expanding negative literals,
                    // the visitLiteral method will return the expansions
                    // of the literal as the positive literals arguments
                    // of a Clause.  Essentially, it is just using the
                    // clause as a container to return the literals.
                    expandedLiterals.addAll(expansion.getPositiveLiterals());
                }

                result = clause.getStringHandler().getClause(clause.getPositiveLiterals(), expandedLiterals);
            }
            else {
                // Case 4.  Just throw an exception.
                throw new UnsupportedOperationException("Inline literals of a clause with 1 or more positive literals and 0 or more negative literals is not supported.");
            }

            return result;
        }

        /* Returns a clause containing the expanded literals.
         *
         * This clause will always contain the expanded literals
         * as positive literals, not negative literals.
         */
        @Override
        public Clause visitLiteral(Literal literal, InlineData data) {

            Clause result;

            if (literal.predicateName.equals(literal.getStringHandler().standardPredicateNames.negationByFailure)) {
                result = literal.getStringHandler().getClause(handleNegationByFailure(literal, data).asLiteral(), null);
            }
            else {
                if (literal.predicateName.isContainsCallable(literal.getArity())) {
                    List<Term> newTerms = new ArrayList<>();
                    for (Term term : literal.getArguments()) {
                        Term newTerm = term.accept(this, data);
                        newTerms.add(newTerm);
                    }

                    literal = literal.getStringHandler().getLiteral(literal, newTerms);
                }

                List<Literal> newBodyLiterals = inlinePredicate(literal, data);

                result = literal.getStringHandler().getClause(newBodyLiterals, null);
            }

            return result;
        }

        @Override
        public Term visitFunction(Function function, InlineData data) {
            Term result;

            PredicateNameAndArity pnaa = function.getPredicateNameAndArity();

            if (pnaa.getPredicateName().equals(function.getStringHandler().standardPredicateNames.negationByFailure)) {
                result = handleNegationByFailure(function, data);
            }
            else {
                if (function.getPredicateName().isContainsCallable(function.getArity())) {
                    List<Term> newTerms = new ArrayList<>();
                    for (Term term : function.getArguments()) {
                        Term newTerm = term.accept(this, data);
                        newTerms.add(newTerm);
                    }

                    function = function.getStringHandler().getFunction(function, newTerms);
                }

                List<Literal> newBodyLiterals = inlinePredicate(function, data);

                if ( newBodyLiterals.size() == 1 ) {
                    result = newBodyLiterals.get(0).asFunction();
                }
                else {
                    result = function.getStringHandler().getSentenceAsTerm( function.getStringHandler().getClause(newBodyLiterals, null), "");
                }
            }

            return result;
        }

        Function handleNegationByFailure(LiteralOrFunction function, InlineData data) {
            // If the function is a negation-by-failure we can iterated into the arguments...

            // Because we are inconsistent as to how we treat negation-by-failure,
            // we use the handy methods in the stringHandler to extract the body
            // and reconstruct it later.

            Clause contents = function.getStringHandler().getNegationByFailureContents(function.asLiteral());

            Clause newContents = (Clause) contents.accept(this, data);

            return function.getStringHandler().getNegationByFailure(newContents).asFunction();
        }

        List<Literal> inlinePredicate(LiteralOrFunction literalToInline, InlineData data) {

            PredicateNameAndArity pnaa = literalToInline.getPredicateNameAndArity();

            List<Literal> result = Collections.singletonList(literalToInline.asLiteral());

            if (data.canInline(pnaa)) {
                
                List<DefiniteClause> definitions = data.getClauseDefinitions(pnaa);
                if (definitions == null || definitions.size() != 1) {
                    data.addDoNotInlinePredicate(pnaa);
                }
                else {
                    DefiniteClause definition = definitions.get(0);

                    if (definition.isDefiniteClauseRule()) {

                        // Make sure we don't expand this literal within
                        // its own body.
                        InlineData newData = new InlineData(data);
                        newData.addDoNotInlinePredicate(pnaa);

                        Literal head = definition.getDefiniteClauseHead();
                        List<Literal> body = definition.getDefiniteClauseBody();

                        BindingList bl = Unifier.UNIFIER.unify(head, literalToInline.asLiteral());

                        result = new ArrayList<>();

                        for (Literal bodyLiteral : body) {
                            Clause inlinedBody = (Clause) bodyLiteral.accept(this, data);
                            inlinedBody = inlinedBody.applyTheta(bl);

                            result.addAll(inlinedBody.getPositiveLiterals());
                        }
                    }
                }
            }
            return result;
        }
    }

    public static class InlineData {

        InlineData parent;

        HornClauseContext context;

        Collection<? extends DefiniteClause> additionalInlinableClauses;

        Set<PredicateNameAndArity> doNotInlineSet;

        InlineData(HornClauseContext context) {
            this.context = context;
            this.additionalInlinableClauses = null;
        }

        InlineData(InlineData parent) {
            this.parent = parent;
        }

        /* Returns whether a predicate can be inlined.
         *
         * Returns true if the predicate is in the inlineSet but is not in
         * the doNotInlineSet.
         */
        boolean canInline(PredicateNameAndArity aPredicate) {
            boolean result = aPredicate.isInlined() && !doNotInline(aPredicate);

            if (!result) {
                result = (findAdditionalInlinableClause(aPredicate) != null);
            }

            return result;
        }

        List<DefiniteClause> getClauseDefinitions(PredicateNameAndArity pnaa) {
            List<DefiniteClause> result = null;

            HornClauseContext c = getContext();
            if ( c != null ) {
                result = c.getClausebase().getAssertions(pnaa);
            }

            if ( result == null ) {
                result = findAdditionalInlinableClause(pnaa);
            }

            return result;
        }

        /* Returns whether a predicate can not be inlined.
         *
         * Returns true if the predicate is in the doNotInlineSet.  Only
         * considers the doNotInlineSet, so a false return value does not
         * indicate the literal can be inlined.
         */
        private boolean doNotInline(PredicateNameAndArity aPredicate) {
            boolean result = false;
            if (doNotInlineSet != null && doNotInlineSet.contains(aPredicate)) {
                result = true;
            }
            else if (parent != null) {
                result = parent.doNotInline(aPredicate);
            }
            return result;
        }

        void addDoNotInlinePredicate(PredicateNameAndArity aPredicate) {
            if (doNotInlineSet == null) {
                doNotInlineSet = new HashSet<>();
            }
            doNotInlineSet.add(aPredicate);
        }

        List<DefiniteClause> findAdditionalInlinableClause(PredicateNameAndArity pnaa) {

            List<DefiniteClause> result = null;

            if ( additionalInlinableClauses != null ) {
                for (DefiniteClause aClause : additionalInlinableClauses) {
                    if ( aClause.getDefiniteClauseHead().getPredicateNameAndArity().equals(pnaa) ) {
                        if ( result == null ) {
                            result = new LinkedList<>();
                        }
                        result.add(aClause);
                    }
                }
            }

            return result;
        }
        
        public HornClauseContext getContext() {
            if (parent != null) {
                return parent.getContext();
            }
            return context;
        }
    }

    private Inliner() {}
}
