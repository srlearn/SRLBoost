package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/*
 * @author twalker
 */
public class PredicateCollector {

    private static final PredicateCollectorVisitor PREDICATE_COLLECTOR_VISITOR = new PredicateCollectorVisitor();

    public static Set<PredicateNameAndArity> collectPredicates(Sentence sentence, HornClauseContext context) {

        PredicateCollectorData data = new PredicateCollectorData(context);
        
        sentence.accept(PREDICATE_COLLECTOR_VISITOR, data);

        return data.predicates;
    }

    private static class PredicateCollectorVisitor extends DefaultFOPCVisitor<PredicateCollectorData> {

        PredicateCollectorVisitor() {
            super(false);
        }

        @Override
        public Term visitFunction(Function function, PredicateCollectorData data) {

            PredicateNameAndArity pnaa = function.getPredicateNameAndArity();

            data.predicates.add(pnaa);

            processBackgroundRules(pnaa, data);

            if ( pnaa.getContainsCallable() ) {
                super.visitFunction(function, data);
            }

            return null;
        }

        @Override
        public Sentence visitLiteral(Literal literal, PredicateCollectorData data) {

            PredicateNameAndArity pnaa = literal.getPredicateNameAndArity();

            data.predicates.add(pnaa);

            processBackgroundRules(pnaa, data);

            if ( pnaa.getContainsCallable() ) {
                super.visitLiteral(literal, data);
            }

            return null;
        }

        private void processBackgroundRules(PredicateNameAndArity pnaa, PredicateCollectorData data) {

            if ( data.context != null && !data.closedList.contains(pnaa)) {
                data.closedList.add(pnaa);

                List<DefiniteClause> clauses = data.context.getClausebase().getAssertions(pnaa);

                if ( clauses != null ) {
                    for (DefiniteClause clause : clauses) {
                        List<Literal> literals = clause.getDefiniteClauseBody();
                        if ( literals != null ) {
                            for (Literal literal : literals) {
                                literal.accept(this, data);
                            }
                        }
                    }
                }
            }
        }
    }

    private static class PredicateCollectorData {
        Set<PredicateNameAndArity> predicates = new HashSet<>();
        HornClauseContext context;
        
        // Set of background knowledge predicates that have already been expanded.
        Set<PredicateNameAndArity> closedList = new HashSet<>();

        PredicateCollectorData(HornClauseContext context) {
            this.context = context;
        }


    }

    private PredicateCollector() {}
}
