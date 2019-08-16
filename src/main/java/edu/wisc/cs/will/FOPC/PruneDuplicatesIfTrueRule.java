package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.ElementAndPath;
import edu.wisc.cs.will.FOPC.visitors.ElementFinder;
import edu.wisc.cs.will.FOPC.visitors.ElementPath;
import edu.wisc.cs.will.FOPC.visitors.ElementRemover;
import edu.wisc.cs.will.ResThmProver.DefaultProof;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.ResThmProver.Proof;
import edu.wisc.cs.will.Utils.Filter;
import java.util.List;

/**
 * @author twalker
 */
public class PruneDuplicatesIfTrueRule implements PruningRule {
 
    private PredicateNameAndArity prunedPredicate;

    private DefiniteClause condition;

    public PruneDuplicatesIfTrueRule(PredicateNameAndArity prunedPredicate, Clause condition) {
        this.prunedPredicate = prunedPredicate;
        this.condition = condition;

        if ( this.condition.getDefiniteClauseHead().getArity() != 2 ) {
            throw new IllegalArgumentException("Pruning rule for duplicates requires form:  prune(ExistingLiteral, AddedLiteral) :- body.");
        }
    }


    public Sentence pruneElement(HornClauseContext context, Sentence sentence, ElementPath pathToPrune, SentenceOrTerm element) {

        if (element instanceof LiteralOrFunction && ((LiteralOrFunction) element).getPredicateNameAndArity().equals(prunedPredicate)) {

            List<ElementAndPath> matchingLiterals = ElementFinder.findElements(new PruneIfTrueElementFilter(pathToPrune, element), sentence);

            for (ElementAndPath existingEAP : matchingLiterals) {
                Term existingTerm = existingEAP.getElement().asTerm();
                BindingList bl = new BindingList();

                Term t0 = condition.getDefiniteClauseHead().getArgument(0);
                Term t1 = condition.getDefiniteClauseHead().getArgument(1);

                bl = Unifier.UNIFIER.unify(t0, existingTerm, bl);

                if ( bl == null ) continue;

                bl = Unifier.UNIFIER.unify(t1, element.asTerm(), bl);

                if ( bl == null ) continue;

                Clause c = context.getStringHandler().getClause( condition.getDefiniteClauseBody(), null);
                c = c.applyTheta(bl);
                
                Proof p = new DefaultProof(context, c);
                BindingList newBindings = p.prove();

                if (newBindings != null) {
                    // The condition is true, so apply the bindings to the sentence remove this literal.
                    sentence = sentence.applyTheta(newBindings);
                    sentence = ElementRemover.removeElement(sentence, pathToPrune);
                    break;
                }
            }
        }

        return sentence;
    }

    private class PruneIfTrueElementFilter implements Filter<ElementAndPath> {

        ElementPath pathToPrune;

        SentenceOrTerm element;

        PruneIfTrueElementFilter(ElementPath pathToPrune, SentenceOrTerm element) {
            this.pathToPrune = pathToPrune;
            this.element = element;
        }

        public boolean includeElement(ElementAndPath elementAndPathToInclude) {
            SentenceOrTerm elementToInclude = elementAndPathToInclude.getElement();
            ElementPath pathToInclude = elementAndPathToInclude.getPath();

            if (elementToInclude != element && pathToInclude.compareTo(pathToPrune) < 0) {
                if (elementToInclude instanceof LiteralOrFunction) {
                    LiteralOrFunction literalOrFunction = (LiteralOrFunction) elementToInclude;
                    return literalOrFunction.getPredicateNameAndArity().equals(prunedPredicate);
                }
            }

            return false;
        }
    }
}
