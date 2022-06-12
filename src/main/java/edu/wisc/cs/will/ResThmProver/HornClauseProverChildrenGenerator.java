package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.ChildrenNodeGenerator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

/*
 * @author shavlik
 *
 */
public class HornClauseProverChildrenGenerator extends ChildrenNodeGenerator<HornSearchNode> {

    private final HornClauseContext context;

    private final BindingList bindingList; // Use this repeatedly to save some "new'ing."

    private long maxOpen = 0;

    private final Unifier unifier;

    /* Literal that tracks where we need to cut to when encountered.
     *
     * The cutLiteral is created the first time a cut is encountered
     * for a given Literal expansion.  It holds a copy of the
     * appropriate CutMarkerNode.
     * <p>
     * As clauses are added to the list of negated literals, their
     * actual cut Literals (if any) are replaced by this special Literal.
     * <p>
     * During SLD resolution, if this CutLiteral is expanded,
     * the nodes of the task's openList will popped until the
     * appropriate CutMarkerNode is encountered.  The CutMarkerNode is
     * not removed during this process since multiple cut in the same clause
     * could result in multiple clearing of the open list.
     * <p>
     * The cutLiteral is reset to null at the beginning of each literal
     * expansion via the resetCutMarkerAndCounters() method.
     */
    private CutLiteral cutLiteral = null;

    /* Search Node holding the place to be cut to when a cut is encountered.
     *
     * The cutMarkerNode is created the first time a cut is encountered
     * for a given Literal expansion.  It is held by the corresponding
     * CutLiteral.
     * <p>
     * When a cut literal is expanded, all nodes between the head of the
     * task's open list and the CutMarkerNode are removed.  The CutMarkerNode
     * is not removed during this process.
     * <P>
     * When expanded during SLD resolution, the cutMarkerNode is simply
     * discarded.
     * <p>
     * The cutMarkerNode is reset to null at the beginning of each literal
     * expansion via the resetCutMarkerAndCounters() method.
     *
     */
    private CutMarkerNode cutMarkerNode = null;

    /* Tracks whether the cutMarker has already been added during the expansion of the current literal.
     *
     * Only want to add CutMarkerNode per expansion of a single literal.
     * <p>
     * The cutMarkerAdded is reset to false at the beginning of each literal
     * expansion via the resetCutMarkerAndCounters() method.
     */
    private boolean cutMarkerAdded;

    /* Tracks the expansion we are on.
     *
     * Use getNextExpansion() to get the next expansion.
     * <P>
     * The nextExpansion is reset to 0 by resetCutMarkerAndCounters() at
     * the beginning of each collectChildren call.
     */
    private int nextExpansion;

    /* Tracks the current proof step counter.
     *
     * Each time a literal is evaluated (it's expanded to include it's children),
     * this counter is increased by 1.
     * <P>
     * Since the children generator can remain around over the course of many proofs,
     * this number can get quite large.  The HornClauseProver could probably reset
     * this number occasionally if this become a problem.
     */
    static long proofCounter = 0;

    HornClauseProverChildrenGenerator(HornClauseProver task, HornClauseContext context) {
        super(task);

        this.context = context;

        // Reuse this since for many cases the result will be the empty binding list or null.
        bindingList = new BindingList();
        unifier = Unifier.UNIFIER;

        HandleFOPCstrings stringHandler = context.getStringHandler();

    }

    @Override
    public List<HornSearchNode> collectChildren(HornSearchNode hornSearchNode) throws RuntimeException {

        // TODO(hayesall): I pulled a bunch of spy and trace calls out of here. I don't think `printVariableCounters` does anything now.

        boolean oldPrintVars = getStringHandler().printVariableCounters;

        // Do the actual work right here...
        List<HornSearchNode> result = collectChildrenActual(hornSearchNode);

        maxOpen = Math.max(getTask().open.size(), maxOpen);

        getStringHandler().printVariableCounters = oldPrintVars;

        proofCounter++;
        return result;
    }

    private List<HornSearchNode> collectChildrenActual(HornSearchNode hornSearchNode) throws RuntimeException {


        // Grab the first negated literal in this node, and find all "rules" in the theory that unify with it.
        // Each "resolvent" is a new node.  E.g., if node = (!P v !A v ... v !H) and the theory contains (P v !R v ... !Z)
        // then resolving P and !P produces (!A v ... v !H v !R v ... !Z) where theta=unify(P, P') is applied to the result.

        resetCutMarkerAndCounters();

        List<Literal> queryLiterals = hornSearchNode.clause.negLiterals;
        Literal negatedLiteral = queryLiterals.get(0);
        HornClauseProver thisTask = (HornClauseProver) this.task;
        PredicateName negatedLiteralPredName = negatedLiteral.predicateName;

        List<HornSearchNode> children = null;  // Collect the children nodes.

        boolean noPredArgMatchFound;

        if (thisTask.predefinedPredicateNamesUsedByChildCollector.contains(negatedLiteralPredName)) {
            // TODO(hayesall): These should not be reachable
            throw new RuntimeException("This code should not be reachable.");
        }

        // TODO(hayesall): Each of these refer to a ProcedurallyDefinedPredicateHandler, or a "user provided" version.

        // See if there is a special procedurally defined predicate, and if so, call its handler.
        int arity = negatedLiteral.numberArgs();
        ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandlerInstance = getClausebase().getUserProcedurallyDefinedPredicateHandler();
        if (userProcedurallyDefinedPredicateHandlerInstance != null && userProcedurallyDefinedPredicateHandlerInstance.canHandle(negatedLiteralPredName, arity)) {
            if (bindingList.theta.size() > 0) {
                bindingList.theta.clear();
            } // Revert to the empty binding list.
            BindingList theta = userProcedurallyDefinedPredicateHandlerInstance.handle(negatedLiteral, bindingList);
            if (theta != null) {
                HornSearchNode newNode = createChildWithNoNewLiterals(hornSearchNode, queryLiterals, theta.copy());

                children = new ArrayList<>(1);
                children.add(newNode);
                return children;
            }
            return null;  // If the procedurally defined predicate failed, then this search path has failed.
        }

        // If we get here, there is no special handling to do.  Just look the literal up in the clause base and
        // handle it appropriately.

        // Use a newer style of background/fact lookup that is hopefully faster.
        boolean predIsInBackgroundKnowledge = getClausebase().checkForPossibleMatchingBackgroundKnowledge(negatedLiteralPredName, arity);
        boolean predIsInFacts = getClausebase().checkForPossibleMatchingFacts(negatedLiteralPredName, arity);

        noPredArgMatchFound = (!predIsInBackgroundKnowledge && !predIsInFacts);

        // Handle the cases where there are only facts, only background knowledge, and where
        // the two are mixed together...
        if (predIsInFacts && !predIsInBackgroundKnowledge) {
            children = createChildrenForFactsOnly(hornSearchNode, negatedLiteral, queryLiterals);
        }
        else if (predIsInFacts || predIsInBackgroundKnowledge) {
            children = createChildrenForMixedBackgroundAndFacts(hornSearchNode, negatedLiteral, queryLiterals);
        }

        if (noPredArgMatchFound && !negatedLiteralPredName.canBeAbsent(arity)) {
            Utils.waitHereErr("There is no fact nor clause nor built-in predicate matching: '" + negatedLiteralPredName + "/" + arity + "'.\n  Possibly a typo?  If not, add to the BK file:   okIfUnknown: " + negatedLiteralPredName + "/" + arity + ".");

            negatedLiteralPredName.setCanBeAbsent(arity);
        }
        if (cutMarkerNode != null) {
            assert children != null;
            children.add(children.size(), cutMarkerNode);
        }
        return children;
    }

    private List<HornSearchNode> createChildrenForFactsOnly(HornSearchNode hornSearchNode, Literal negatedLiteral, List<Literal> queryLiterals) {
        List<HornSearchNode> children = null;

        negatedLiteral.numberArgs();

        Iterable<Literal> matchingFacts = getClausebase().getPossibleMatchingFacts(negatedLiteral, null);

        if (matchingFacts != null) {
            for (Literal fact : matchingFacts) {

                BindingList theta = unify(negatedLiteral, fact, new BindingList());

                if (theta != null && fact.containsFreeVariablesAfterSubstitution(theta)) { // If any variables in the fact are unbound, need to rename then rebind.
                    // TAW: I don't think that facts are supposed to have free variables.  However,
                    // TAW: we only print a warning and don't restrict it, so I guess we need to do this step.
                    Utils.println("Since variables in the fact remain after unification, need to rename '" + fact + "'.");
                    fact = (Literal) fact.copyAndRenameVariables();
                    bindingList.theta.clear();
                    theta = unify(negatedLiteral, fact, new BindingList());
                }

                if (theta != null) {
                    HornSearchNode newNode = createChildWithNoNewLiterals(hornSearchNode, queryLiterals, theta);

                    if (children == null) {
                        children = new ArrayList<>();
                    }
                    children.add(newNode); // Do NOT return here.
                }
            }
        }

        return children;
    }

    private List<HornSearchNode> createChildrenForMixedBackgroundAndFacts(HornSearchNode hornSearchNode, Literal negatedLiteral, List<Literal> queryLiterals) {
        List<HornSearchNode> children = null;

        negatedLiteral.numberArgs();

        Collection<DefiniteClause> possibleMatchingAssertions = getClausebase().getPossibleMatchingAssertions(negatedLiteral, null);

        if (possibleMatchingAssertions != null) {

            for (DefiniteClause definiteClause : possibleMatchingAssertions) {  //Utils.println("Consider: " + clause);
                Literal ruleHead = definiteClause.getDefiniteClauseHead();

                BindingList theta = unify(negatedLiteral, ruleHead, new BindingList());

                if (theta != null && !definiteClause.isDefiniteClauseFact() && definiteClause.containsFreeVariablesAfterSubstitution(theta)) { // If any variables in the clause are unbound (even in the BODY!), need to rename then rebind.
                    definiteClause = (DefiniteClause) definiteClause.getDefiniteClauseAsClause().copyAndRenameVariables();
                    ruleHead = definiteClause.getDefiniteClauseHead();

                    // We have to rebind theta since the clause is a copy...
                    theta = unify(negatedLiteral, ruleHead, new BindingList());
                    if (theta == null) {
                        Utils.println("Since variables in the new clause remain after unification, need to rename '" + definiteClause + "'.");
                        Utils.println("  renamed clause: " + definiteClause.getDefiniteClauseAsClause().toPrettyString("     ", Integer.MAX_VALUE, null));
                        Utils.println("  negatedLiteral= " + negatedLiteral);
                        Utils.println("  ruleHead      = " + ruleHead);
                        Utils.println("  theta         = " + null);
                        Utils.error("What happened to theta???");
                    }
                }

                if (theta != null) {
                    List<Literal> ruleBody = definiteClause.getDefiniteClauseBody();

                    if (definiteClause.isDefiniteClauseRule()) {
                        Clause clause = definiteClause.getDefiniteClauseAsClause();
                        if (!cutMarkerAdded && clause.getBodyContainsCut()) {
                            createCutMarkerNode(hornSearchNode, negatedLiteral);
                        }
                        if (clause.getBodyContainsCut()) {
                            ruleBody = markCutsInClauseWithCurrentCutMarker(ruleBody);
                        }
                    }

                    HornSearchNode newNode;
                    if (ruleBody == null) {
                        newNode = createChildWithNoNewLiterals(hornSearchNode, queryLiterals, theta);
                    }
                    else {
                        newNode = createChildWithMultipleNewLiterals(hornSearchNode, ruleBody, queryLiterals, theta);
                    }

                    if (children == null) {
                        children = new ArrayList<>();
                    }
                    children.add(newNode);
                }
            }
        }

        return children;
    }

    private BindingList unify(Literal lit1, Literal lit2, BindingList bindingList) {
        return unifier.unify(lit1, lit2, bindingList);
    }

    private void resetCutMarkerAndCounters() {
        cutMarkerAdded = false;
        cutLiteral     = null;
        cutMarkerNode  = null; 

        nextExpansion = 0;
    }

    private void createCutMarkerNode(HornSearchNode hornSearchNode, Literal literalBeingCut) {
        if (!cutMarkerAdded) {
            cutMarkerAdded = true;
            cutMarkerNode = new CutMarkerNode(hornSearchNode, literalBeingCut, proofCounter);
            cutLiteral    = new CutLiteral(getStringHandler(), cutMarkerNode);
        }
    }

    /*
     * Create a new list, where all the cuts are replaced by new cuts that have the argument cutMarkerLiteralAsTerm.
     */
    private List<Literal> markCutsInClauseWithCurrentCutMarker(List<Literal> ruleBody) {
        List<Literal> newRuleBody = new ArrayList<>(ruleBody.size());
        for (Literal lit : ruleBody) {
            if (lit.predicateName == getStringHandler().standardPredicateNames.cut) {
            	if (cutLiteral == null) { Utils.waitHere(); }
                newRuleBody.add(cutLiteral);
            }
            else {
                newRuleBody.add(lit);
            }
        }
        return newRuleBody;
    }

    private int getNextExpansion() {
        return nextExpansion++;
    }

    @Override
    public void clearAnySavedInformation() {
        // We want the theory to persist across searches.
    }

    private HandleFOPCstrings getStringHandler() {
        return context.getStringHandler();
    }

    private HornClausebase getClausebase() {
        return context.getClausebase();
    }

    private HornClauseProver getTask() {
        return (HornClauseProver) task;
    }

    private List<Literal> getQueryRemainder(List<Literal> queryLiterals, BindingList bindingList) {
        int querySize = queryLiterals.size();
        List<Literal> queryRemainder = new LinkedList<>();

        if (querySize > 0) {

            for (int i = 1; i < querySize; i++) {
                Literal lit = queryLiterals.get(i);
                if (bindingList != null) {
                    lit = lit.applyTheta(bindingList.theta);
                }
                queryRemainder.add(lit);
            }
        }
        return queryRemainder;
    }

    private HornSearchNode createChildWithMultipleNewLiterals(HornSearchNode hornSearchNode, List<Literal> newLiterals, List<Literal> queryLiterals, BindingList bindingList) {

        int expansion = getNextExpansion();

        List<Literal> newQueryLiterals = getQueryRemainder(queryLiterals, bindingList);

        if (bindingList != null) {
            bindingList = bindingList.copy();
        }

        if (newLiterals != null) {
            for (int i = newLiterals.size() - 1; i >= 0; i--) {
                Literal newLit = newLiterals.get(i);
                if (bindingList != null) {
                    newLit = newLit.applyTheta(bindingList.theta);
                }
                newQueryLiterals.add(0, newLit);
            }
        }

        return new HornSearchNode(hornSearchNode, getStringHandler().getClause(newQueryLiterals, false), bindingList);
    }

    private HornSearchNode createChildWithNoNewLiterals(HornSearchNode hornSearchNode, List<Literal> queryLiterals, BindingList bindingList) {
        int expansion = getNextExpansion();

        if (bindingList != null) {
            bindingList = bindingList.copy();
        }

        List<Literal> newQueryLiterals = getQueryRemainder(queryLiterals, bindingList);

        return new HornSearchNode(hornSearchNode, getStringHandler().getClause(newQueryLiterals, false), bindingList);
    }

    protected static class CutMarkerNode extends HornSearchNode {

        private final CutMarkerLiteral cutMarkerLiteral;

        CutMarkerNode(HornSearchNode parentNode, Literal literalBeingCut, long proofCounterOfCutClause) {
            super(parentNode, null, null);

            this.cutMarkerLiteral = new CutMarkerLiteral(literalBeingCut.getStringHandler(), literalBeingCut, proofCounterOfCutClause);
            this.clause = literalBeingCut.getStringHandler().getClause(null, this.cutMarkerLiteral);
        }

        CutMarkerNode(HornClauseProver task, Literal literalBeingCut, long proofCounterOfCutClause) {
            super(task, null);

            this.cutMarkerLiteral = new CutMarkerLiteral(literalBeingCut.getStringHandler(), literalBeingCut, proofCounterOfCutClause);
            this.clause = literalBeingCut.getStringHandler().getClause(null, this.cutMarkerLiteral);
        }

        @Override
        public String toString() {
            return cutMarkerLiteral.toString();
        }

        Literal getLiteralBeingCut() {
            return cutMarkerLiteral.getLiteralBeingCut();
        }

        long getProofCounterOfCutClause() {
            return cutMarkerLiteral.getProofCounterOfCutClause();
        }
    }

    protected static class CutMarkerLiteral extends Literal {

        /* Head of the clause that contained the cut.
         *
         * This is just for debugging purpose, never used in the actual resolution.
         *
         */
        private final Literal literalBeingCut;

        private final long proofCounterOfCutClause;

        CutMarkerLiteral(HandleFOPCstrings stringHandler, Literal literalBeingCut, long proofCounterOfCutClause) {
            super(stringHandler, stringHandler.standardPredicateNames.cutMarker);
            this.literalBeingCut = literalBeingCut;
            this.proofCounterOfCutClause = proofCounterOfCutClause;
        }

        @Override
        public String toString(int precedenceOfCaller) {
            return "CutMarker [Cut of [" + getProofCounterOfCutClause() + ".*] " + literalBeingCut + "]";
        }

        Literal getLiteralBeingCut() {
            return literalBeingCut;
        }

        long getProofCounterOfCutClause() {
            return proofCounterOfCutClause;
        }
    }

    protected static class CutLiteral extends Literal {

        /** Head of the clause that contained the cut.
         *
         */
        private final CutMarkerNode cutMarkerNode;

        CutLiteral(HandleFOPCstrings stringHandler, CutMarkerNode cutMarkerNode) {
            super(stringHandler, stringHandler.standardPredicateNames.cut);
            this.cutMarkerNode = cutMarkerNode;
        }

        @Override
        public String toString(int precedenceOfCaller) {
            return "! [Cut to marker [" + cutMarkerNode.getProofCounterOfCutClause() + ".*] " + cutMarkerNode.getLiteralBeingCut() + "]";
        }

        @Override
        public String toPrettyString() {
            return toString();
        }

        @Override
        public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
            return toString();
        }

        @Override
        public String toString(int precedenceOfCaller, BindingList bindingList) {
            return toString();
        }
    }

}
