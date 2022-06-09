package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.ChildrenNodeGenerator;
import edu.wisc.cs.will.stdAIsearch.OpenList;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

import java.util.*;

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

    /* Caches a failLiteral locally.
     */
    private final Literal failLiteral;

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

        failLiteral = stringHandler.getLiteral(stringHandler.standardPredicateNames.fail);

        PrettyPrinterOptions prettyPrintOptions = new PrettyPrinterOptions();
        prettyPrintOptions.setMaximumConsCells(5);
        prettyPrintOptions.setMultilineOutputEnabled(false);
        prettyPrintOptions.setSentenceTerminator("");
        prettyPrintOptions.setRenameVariables(false);

    }

    @Override
    public List<HornSearchNode> collectChildren(HornSearchNode hornSearchNode) throws SearchInterrupted, RuntimeException {

        // TODO(hayesall): I pulled a bunch of spy and trace calls out of here. I don't think `printVariableCounters` does anything now.

        boolean oldPrintVars = getStringHandler().printVariableCounters;

        // Do the actual work right here...
        List<HornSearchNode> result = collectChildrenActual(hornSearchNode);

        maxOpen = Math.max(getTask().open.size(), maxOpen);

        getStringHandler().printVariableCounters = oldPrintVars;

        proofCounter++;
        return result;
    }

    private List<HornSearchNode> collectChildrenActual(HornSearchNode hornSearchNode) throws SearchInterrupted {


        // Grab the first negated literal in this node, and find all "rules" in the theory that unify with it.
        // Each "resolvent" is a new node.  E.g., if node = (!P v !A v ... v !H) and the theory contains (P v !R v ... !Z)
        // then resolving P and !P produces (!A v ... v !H v !R v ... !Z) where theta=unify(P, P') is applied to the result.

        resetCutMarkerAndCounters();

        HandleFOPCstrings stringHandler = context.getStringHandler();


        List<Literal> queryLiterals = hornSearchNode.clause.negLiterals;
        Literal negatedLiteral = queryLiterals.get(0);
        HornClauseProver thisTask = (HornClauseProver) this.task;
        PredicateName negatedLiteralPredName = negatedLiteral.predicateName;

        List<HornSearchNode> children = null;  // Collect the children nodes.

        boolean noPredArgMatchFound;

        if (thisTask.predefinedPredicateNamesUsedByChildCollector.contains(negatedLiteralPredName)) {

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.falseName || negatedLiteralPredName == stringHandler.standardPredicateNames.fail) {
                if (negatedLiteral.numberArgs() != 0) {
                    Utils.error("Cannot have arguments to the 'false' predicate.  You have: '" + negatedLiteral + "'");
                }
                return null;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.trueName) { // Could have this be procedurally defined, but duplicate code here for simplicity.
                if (negatedLiteral.numberArgs() != 0) {
                    Utils.error("Cannot have arguments to the 'true' predicate.  You have: '" + negatedLiteral + "'");
                }
                children = new ArrayList<>(1);
                children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.repeat) {
                if (negatedLiteral.numberArgs() != 0) {
                    Utils.error("Cannot have arguments to the 'repeat' predicate.  You have: '" + negatedLiteral + "'");
                }
                children = new ArrayList<>(1);
                children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, null));
                children.add(hornSearchNode); // In a repeat, we backtrack to this same node.  'Repeat' can be viewed as: 'repeat. repeat :- repeat.'
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.cutMarker) {
                return null; // Don't want this to succeed.
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.cut) {

                popOpenUptoThisCutMarker(negatedLiteral); // Discard everything up this cut's marker.
                // Add the remainder of this query following the cut.
                children = new ArrayList<>(1);
                children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.negationByFailure) {
                // Convert '\+ P' to
                //    dummy :- P, !, false.
                //    dummy :- true.

                Clause negationContents = stringHandler.getNegationByFailureContents(negatedLiteral);

                if (negationContents == null) {
                    Utils.error("Expected term of negation to be Function or SentenceAsTerm.");
                }

                if (negationContents.getNegLiteralCount() == 0) {
                    negationContents = stringHandler.getClause(negationContents.getNegativeLiterals(), negationContents.getPositiveLiterals());
                }

                createCutMarkerNode(hornSearchNode, negatedLiteral);

                List<Literal> expandedNotLiterals = new LinkedList<>();
                if (negationContents.getNegativeLiterals() != null) {
                    expandedNotLiterals.addAll(negationContents.getNegativeLiterals());
                }
                if (cutLiteral == null) { Utils.waitHere(); }
                expandedNotLiterals.add(cutLiteral);
                expandedNotLiterals.add(failLiteral);

                HornSearchNode negationSucessNode = createChildWithMultipleNewLiterals(hornSearchNode, expandedNotLiterals, queryLiterals, null);
                HornSearchNode negationFailedNode = createChildWithMultipleNewLiterals(hornSearchNode, null, queryLiterals, null);

                children = new ArrayList<>(3);

                children.add(negationSucessNode);
                children.add(negationFailedNode);
                children.add(cutMarkerNode);

                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.then) {
                // Convert 'if P then Q else R' - note there is no backtracking across P due to the cut.
                //    if(P,Q,R) :- P, !, Q.
                //    if(P,Q,R) :- R. [note that R is optional]
                throw new UnsupportedOperationException();

            }

            // Handle "call(X)" by pulling out X and adding it back in.
            if (negatedLiteralPredName == stringHandler.standardPredicateNames.call || negatedLiteralPredName == stringHandler.standardPredicateNames.implicit_call) { //Utils.println("% CALL!");
                if (negatedLiteral.numberArgs() != 1) {
                    Utils.error("Must have ONE argument to the 'call' predicate.  You have: '" + negatedLiteral + "'");
                }
                Clause callBody = negatedLiteral.getArgument(0).asClause();

                HornSearchNode newNode = createChildWithMultipleNewLiterals(hornSearchNode, callBody.getPositiveLiterals(), queryLiterals, null);
                children = new ArrayList<>(1);
                children.add(newNode);
                return children;
            }

            // Here is the definition for once: once(G) :- call(G), !.
            if (negatedLiteralPredName == stringHandler.standardPredicateNames.once) {
                if (negatedLiteral.numberArgs() != 1) {
                    Utils.error("Must have ONE argument to the 'once' predicate.  You have: '" + negatedLiteral + "'");
                }
                // Need to convert the body of the once() to clause form (this is now done at parse time) and add a cut at the end.  BE SURE THE CLAUSE IS MARKED AS CONTAINING A CUT!
                // Then need to add this internal clause to
                SentenceAsTerm onceBody = (SentenceAsTerm) negatedLiteral.getArgument(0); // Count on these being the proper type, so that casting works.
                Clause clauseBody = (Clause) onceBody.sentence;

                if (cutMarkerNode != null) {
                    Utils.error("cutMarkerLiteral should be null here!");
                }
                createCutMarkerNode(hornSearchNode, negatedLiteral);

                List<Literal> expandedOnceLiterals = new LinkedList<>();
                if (clauseBody.negLiterals != null) {
                    expandedOnceLiterals.addAll(clauseBody.negLiterals);
                }
                Utils.println("once: Adding a cut marker.");  if (cutLiteral == null) { Utils.waitHere(); }
                expandedOnceLiterals.add(cutLiteral);

                HornSearchNode expandedOnceNode = createChildWithMultipleNewLiterals(hornSearchNode, expandedOnceLiterals, queryLiterals, null);
                children = new ArrayList<>(2);
                children.add(expandedOnceNode);
                children.add(cutMarkerNode); // Want the cut to be the OLDEST item in OPEN among these children.
                return children;
            }

            // Handle a findAll (and all, setOf, bagOf, etc)
            if (negatedLiteralPredName == stringHandler.standardPredicateNames.findAll || negatedLiteralPredName == stringHandler.standardPredicateNames.all
                    || negatedLiteralPredName == stringHandler.standardPredicateNames.setOf || negatedLiteralPredName == stringHandler.standardPredicateNames.bagOf
                    || negatedLiteralPredName == stringHandler.standardPredicateNames.countProofs || negatedLiteralPredName == stringHandler.standardPredicateNames.countUniqueBindings) {
                Term term, list;
                Clause goal;
                if (negatedLiteralPredName == stringHandler.standardPredicateNames.countProofs || negatedLiteralPredName == stringHandler.standardPredicateNames.countUniqueBindings) {
                    if (negatedLiteral.numberArgs() != 2) {
                        Utils.error("Must have TWO arguments to the '" + negatedLiteralPredName + "' predicate.  You have: '" + negatedLiteral + "'");
                    }
                    term = negatedLiteral.getArgument(0); // Only needed for countUniqueBindings(), but stick in here anyway so internal rep's consistent across these variants.
                    goal = (Clause) ((SentenceAsTerm) term).sentence;
                    list = negatedLiteral.getArgument(1);
                }
                else {
                    if (negatedLiteral.numberArgs() != 3) {
                        Utils.error("Must have THREE arguments to the '" + negatedLiteralPredName + "' predicate.  You have: '" + negatedLiteral + "'");
                    }
                    term = negatedLiteral.getArgument(0);
                    goal = (Clause) ((SentenceAsTerm) negatedLiteral.getArgument(1)).sentence;
                    list = negatedLiteral.getArgument(2);
                }
                PredicateName collectorPred = getStringHandler().getPredicateName(negatedLiteralPredName + "Collector");
                // Collect ALL proofs of goal, which must be a literal or a conjunct - actually, a clause with only negative literals.
                // And for each proof, save 'term' (which presumably shares variables with 'goal') in a list.
                // Unify this list with 'list' as the final step.  EXCEPTION: the count* variants return the LENGTH of this list.
                ObjectAsTerm answersList = getStringHandler().getObjectAsTerm(getStringHandler().getNil(), false); // Need to WRAP this since we'll be "cons'ing" to the front and we need something to hold the resulting consCell.
                List<Term> collectorArgs = new ArrayList<>(2); // This will collect all the answers.
                collectorArgs.add(term);
                collectorArgs.add(answersList);
                List<Term> resultArgs = new ArrayList<>(3); // This will return once all the answers have been collected. The 3rd argument is simply there so that we can easily differentiate the two.
                resultArgs.add(list);
                resultArgs.add(answersList);
                resultArgs.add(term); // Might as well put something useful here ..
                Literal collector = getStringHandler().getLiteral(collectorPred, collectorArgs);

                List<Literal> collectorLiterals = new LinkedList<>();
                if (goal.negLiterals != null) {
                    collectorLiterals.addAll(goal.negLiterals);
                }
                collectorLiterals.add(collector);

                Literal answerLiteral = getStringHandler().getLiteral(collectorPred, resultArgs);

                HornSearchNode collectNode = createChildWithMultipleNewLiterals(hornSearchNode, collectorLiterals, queryLiterals, null);
                HornSearchNode answerNode = createChildWithSingleNewLiteral(hornSearchNode, answerLiteral, queryLiterals);

                children = new ArrayList<>(1);
                children.add(collectNode);
                children.add(answerNode);
                return children;
            }
        }

        // See if there is a special procedurally defined predicate, and if so, call its handler.
        int arity = negatedLiteral.numberArgs();
        ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandlerInstance = getClausebase().getUserProcedurallyDefinedPredicateHandler();
        if (userProcedurallyDefinedPredicateHandlerInstance != null && userProcedurallyDefinedPredicateHandlerInstance.canHandle(negatedLiteralPredName, arity)) {
            if (bindingList.theta.size() > 0) {
                bindingList.theta.clear();
            } // Revert to the empty binding list.
            BindingList theta = userProcedurallyDefinedPredicateHandlerInstance.handle(context, negatedLiteral, unifier, bindingList);
            if (theta != null) {
                HornSearchNode newNode = createChildWithNoNewLiterals(hornSearchNode, queryLiterals, theta.copy());

                children = new ArrayList<>(1);
                children.add(newNode);
                return children;
            }
            return null;  // If the procedurally defined predicate failed, then this search path has failed.
        }
        // See if this is a built-in (into the ResolutionTheoremProver) predicate that needs to be handled by special code.
        ProcedurallyDefinedPredicateHandler builtinProcedurallyDefinedPredicateHandlerInstance = getClausebase().getBuiltinProcedurallyDefinedPredicateHandler();
        if (builtinProcedurallyDefinedPredicateHandlerInstance.canHandle(negatedLiteralPredName, arity)) {
            if (bindingList.theta.size() > 0) {
                bindingList.theta.clear();
            } // Revert to the empty binding list.
            BindingList theta = builtinProcedurallyDefinedPredicateHandlerInstance.handle(context, negatedLiteral, unifier, bindingList);
            if (theta != null) {

                HornSearchNode newNode = createChildWithNoNewLiterals(hornSearchNode, queryLiterals, theta);

                children = new ArrayList<>(1);
                children.add(newNode);
                return children;
            }
            return null;  // If the built-in procedurally defined predicate failed, then this search path has failed.
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

    private void popOpenUptoThisCutMarker(Literal cutLiteral) {

        CutMarkerNode markerNode = ((CutLiteral) cutLiteral).cutMarkerNode;

        OpenList<HornSearchNode> openList = getTask().open;

        while (!openList.isEmpty() && openList.peek() != markerNode) {
            openList.popOpenList();
        }

        if (openList.isEmpty()) {
            Utils.error("Pop'ed all of OPEN but did not find: '" + markerNode + "'");
        }

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

        return new HornSearchNode(hornSearchNode, getStringHandler().getClause(newQueryLiterals, false), bindingList, proofCounter, expansion);
    }

    private HornSearchNode createChildWithSingleNewLiteral(HornSearchNode hornSearchNode, Literal newLiteral, List<Literal> queryLiterals) {

        int expansion = getNextExpansion();

        List<Literal> newQueryLiterals = getQueryRemainder(queryLiterals, null);

        if (newLiteral != null) {
            newQueryLiterals.add(0, newLiteral);
        }

        return new HornSearchNode(hornSearchNode, getStringHandler().getClause(newQueryLiterals, false), null, proofCounter, expansion);
    }

    private HornSearchNode createChildWithNoNewLiterals(HornSearchNode hornSearchNode, List<Literal> queryLiterals, BindingList bindingList) {
        int expansion = getNextExpansion();

        if (bindingList != null) {
            bindingList = bindingList.copy();
        }

        List<Literal> newQueryLiterals = getQueryRemainder(queryLiterals, bindingList);

        return new HornSearchNode(hornSearchNode, getStringHandler().getClause(newQueryLiterals, false), bindingList, proofCounter, expansion);
    }

    protected static class CutMarkerNode extends HornSearchNode {

        private final CutMarkerLiteral cutMarkerLiteral;

        CutMarkerNode(HornSearchNode parentNode, Literal literalBeingCut, long proofCounterOfCutClause) {
            super(parentNode, null, null, proofCounterOfCutClause, -1);

            this.cutMarkerLiteral = new CutMarkerLiteral(literalBeingCut.getStringHandler(), literalBeingCut, proofCounterOfCutClause);
            this.clause = literalBeingCut.getStringHandler().getClause(null, this.cutMarkerLiteral);
        }

        CutMarkerNode(HornClauseProver task, Literal literalBeingCut, long proofCounterOfCutClause) {
            super(task, null, proofCounterOfCutClause, -1);

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
