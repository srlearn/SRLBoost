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

    private BindingList bindingList; // Use this repeatedly to save some "new'ing."

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

    private final PrettyPrinterOptions prettyPrintOptions;

    HornClauseProverChildrenGenerator(HornClauseProver task, HornClauseContext context) {
        super(task);

        this.context = context;

        // Reuse this since for many cases the result will be the empty binding list or null.
        bindingList = new BindingList();
        unifier = Unifier.UNIFIER;

        HandleFOPCstrings stringHandler = context.getStringHandler();

        failLiteral = stringHandler.getLiteral(stringHandler.standardPredicateNames.fail);

        prettyPrintOptions = new PrettyPrinterOptions();
        prettyPrintOptions.setMaximumConsCells(5);
        prettyPrintOptions.setMultilineOutputEnabled(false);
        prettyPrintOptions.setSentenceTerminator("");
        prettyPrintOptions.setRenameVariables(false);

    }

    @Override
    public List<HornSearchNode> collectChildren(HornSearchNode hornSearchNode) throws SearchInterrupted {

        List<HornSearchNode> result = null;


        if (hornSearchNode instanceof FailedTraceNode) {
            FailedTraceNode failedTraceNode = (FailedTraceNode) hornSearchNode;

            BindingList localVarBindings = getLocalBindings(failedTraceNode.failedLiteral, failedTraceNode);

            String litString = PrettyPrinter.print(failedTraceNode.failedLiteral, "", "", prettyPrintOptions, localVarBindings);

            Utils.println(String.format("          [%d.%d] failed: %s", failedTraceNode.parentProofCounter, failedTraceNode.parentExpansionIndex, litString));
            Utils.println("\n--------------------------------------------------------------------------------\n");
        }

        else {

            // This is some debugging code.  Please do not delete me.
            boolean oldPrintVars = getStringHandler().printVariableCounters;

            List<Literal> queryLiterals = hornSearchNode.clause.negLiterals;

            Literal literalBeingExpanded = queryLiterals.get(0);

            while (literalBeingExpanded instanceof StackTraceLiteral) {
                StackTraceLiteral trace = (StackTraceLiteral) literalBeingExpanded;

                Literal traceLiteral = trace.getTraceLiteral();
                if (getTask().getTraceLevel() >= 2 || isSpyLiteral(traceLiteral)) {
                    
                    BindingList localVarBindings = null;

                    if (getTask().getTraceLevel() >= 3 || isSpyLiteral(traceLiteral)) {
                        localVarBindings = getLocalBindings(traceLiteral, hornSearchNode);
                    }

                    String litString = PrettyPrinter.print(traceLiteral, "", "", prettyPrintOptions, localVarBindings);

                    Utils.println(String.format("          [%d.%d] returned: %s", trace.getProofCounter(), trace.getExpansion(), litString));

                    Utils.println("\n--------------------------------------------------------------------------------\n");
                    
                }

                queryLiterals.remove(0);

                // If we got rid of the last literal, then this was a successful proof.
                // Return an empty child.
                if (queryLiterals.isEmpty()) {
                    return Collections.singletonList(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, null));
                }
                else {
                    literalBeingExpanded = queryLiterals.get(0);
                }
            }

            // Enable spy points...
            if (getTask().getTraceLevel() == 0 && getTask().getSpyEntries().includeElement(literalBeingExpanded.predicateName, literalBeingExpanded.numberArgs())) {
                /* Indicates the default spy level that should be set when a spy point is hit.
                 *
                 * 1: Tracing enabled.  Minimum to get anything.
                 * 2: Tracing of subliterals.
                 * 3: Detail tracing of subliterals including bindings.
                 * 4: Everything plus a printout of the openlist (don't do this).
                 */
                int defaultSpyLevel = 1;
                if (getTask().getTraceLevel() < defaultSpyLevel) {
                    Utils.println("Spy point encountered on " + literalBeingExpanded.predicateName + "/" + literalBeingExpanded.numberArgs() + ".  Enabling tracing.");
                    getTask().setTraceLevel(defaultSpyLevel);
                }
            }

            BindingList printBindings = tracePrefix(hornSearchNode, literalBeingExpanded, prettyPrintOptions);

            // Do the actual work right here...
            result = collectChildrenActual(hornSearchNode);

            if (result != null && (getTask().getTraceLevel() >= 2 || isSpyLiteral(literalBeingExpanded))) {
                result.add(new FailedTraceNode(getTask(), literalBeingExpanded, hornSearchNode.parentProofCounter, hornSearchNode.parentExpansionIndex));
            }
            
            maxOpen = Math.max(getTask().open.size(), maxOpen);

            traceSuffix(hornSearchNode, result, queryLiterals, literalBeingExpanded, printBindings, prettyPrintOptions);

            getStringHandler().printVariableCounters = oldPrintVars;

            proofCounter++;
        }
        return result;
    }

    private BindingList getLocalBindings(Literal traceLiteral, HornSearchNode hornSearchNode) {
        BindingList localVarBindings = new BindingList();
        Collection<Variable> freeVars = traceLiteral.collectFreeVariables(null);
        for (Variable freeVar : freeVars) {
            Term freeBinding = hornSearchNode.getBinding(freeVar);
            if (freeBinding != null) {
                localVarBindings.addBinding(freeVar, freeBinding);
            }
        }
        return localVarBindings;
    }

    private BindingList tracePrefix(HornSearchNode hornSearchNode, Literal firstQueryLiteral, PrettyPrinterOptions ppo) {
        try {
            if (getTask().getTraceLevel() >= 2 || (getTask().getTraceLevel() >= 1 && isSpyLiteral(firstQueryLiteral))) {

                getStringHandler().printVariableCounters = true;

                BindingList printBindings = getLocalBindings(firstQueryLiteral, hornSearchNode);


                String headerString = String.format("[%6d] Collecting expansions of [%d.%d]: ", proofCounter, hornSearchNode.parentProofCounter, hornSearchNode.parentExpansionIndex);
                String litString = PrettyPrinter.print(firstQueryLiteral, "", PrettyPrinter.spaces(headerString.length() + 2), ppo, printBindings);

                Utils.println(headerString + litString);

                if (getTask().getTraceLevel() >= 3) {
                    List<Binding> bindings = hornSearchNode.collectBindingsToRoot();
                    if (bindings != null) {
                        bindings.sort(Comparator.comparingLong(o -> o.var.counter));
                    }

                    Utils.println("  Initial bindings: " + bindings);
                }

                if (getTask().getTraceLevel() >= 4) {
                    Utils.println("  OpenList: ");
                    for (int i = 0; i < getTask().open.size(); i++) {
                        Utils.println("    " + getTask().open.get(i));
                    }
                }

                return printBindings;
            }
        } catch (Throwable e) {
            Utils.println("Error occurred while tracing: " + e.toString() + ".");
        }

        return null;
    }

    private void traceSuffix(HornSearchNode lastExpandedNode, List<HornSearchNode> list, List<Literal> queryLiterals, Literal negatedLiteral, BindingList printBindings, PrettyPrinterOptions ppo) {
        try {

            if (getTask().getTraceLevel() >= 2 || (getTask().getTraceLevel() >= 1 && isSpyLiteral(negatedLiteral))) {
                if (list == null) {
                    HornSearchNode nextOpenNode = task.open.peekFirst();
                    String literalString = PrettyPrinter.print(negatedLiteral, "", "", ppo, printBindings);
                    if (nextOpenNode == null) {
                        Utils.println("          [" + lastExpandedNode.parentProofCounter + "." + lastExpandedNode.parentExpansionIndex + "] failed: " + literalString + ".  No remaining open.  Failing proof.");
                    }
                    else {
                        Utils.println("          [" + lastExpandedNode.parentProofCounter + "." + lastExpandedNode.parentExpansionIndex + "] failed: " + literalString + ".  Backtracking to expansion [" + nextOpenNode.parentProofCounter + "." + nextOpenNode.parentExpansionIndex + "].");
                    }
                }
                else {
                    Literal nextLiteral = queryLiterals.size() > 1 ? queryLiterals.get(1) : null;

                    int expansionCount = list.size();
                    if (list.get(expansionCount - 1) instanceof FailedTraceNode) {
                        expansionCount--;
                    }

                    String headerString = "           Found " + expansionCount + " expansions:";
                    Utils.println(headerString);
                    for (int expansion = 0; expansion < expansionCount; expansion++) {
                        HornSearchNode searchNode = list.get(expansion);

                        StringBuilder sb = new StringBuilder();
                        Clause c = searchNode.clause;

                        if (searchNode.bindings != null) {
                            Set<Variable> printVars = new HashSet<>(printBindings.getVariables());
                            for (Variable variable : printVars) {
                                Term reverseBinding = searchNode.bindings.lookup(variable);
                                if (reverseBinding instanceof Variable) {
                                    printBindings.addBinding((Variable) reverseBinding, variable);
                                }
                            }
                        }

                        if (negatedLiteral.predicateName == getStringHandler().standardPredicateNames.negationByFailure && searchNode.parentExpansionIndex == 0) {
                            String clauseString = PrettyPrinter.print(c, "", "", ppo, printBindings);
                            sb.append(clauseString);
                        }
                        else if (searchNode.parentExpansionIndex == -1) {
                            sb.append("cutMarker");
                        }
                        else {
                            int maxNewCount = c.getNegLiteralCount() - (queryLiterals.size() - 1);

                            int realLiteralCount = 0;  // count ignoring StackTraceLiterals
                            for (int i = 0; i < c.getNegLiteralCount(); i++) {
                                Literal lit = c.getNegLiteral(i);
                                if (!(lit instanceof StackTraceLiteral)) {

                                    if (realLiteralCount > 0) {
                                        sb.append(" ^ ");
                                    }
                                    if (realLiteralCount < maxNewCount && c.negLiterals.get(i) != nextLiteral) {

                                        String clauseString = PrettyPrinter.print(c.negLiterals.get(i), "", "", ppo, printBindings);
                                        sb.append(clauseString);
                                    }
                                    else {
                                        if (realLiteralCount == 0) {
                                            sb.append("true ^ ");
                                        }
                                        sb.append("REST");
                                        realLiteralCount++;
                                        break;
                                    }

                                    realLiteralCount++;
                                }
                            }

                            if (realLiteralCount == 0) {
                                sb.append("true (proof successful)");
                            }
                        }
                        Utils.println(String.format("             [%d.%d] %s", searchNode.parentProofCounter, searchNode.parentExpansionIndex, sb.toString()));

                        if (getTask().getTraceLevel() >= 2 || isSpyLiteral(negatedLiteral)) {

                            int bindingCount = 0;

                            StringBuilder stringBuilder = new StringBuilder();

                            stringBuilder.append("{");

                            Collection<Variable> freeVars = lastExpandedNode.clause.collectFreeVariables(null);
                            boolean first = true;
                            for (Variable freeVar : freeVars) {



                                Term to = searchNode.getBinding(freeVar);

                                if (to != null && !(to instanceof Variable)) {
                                    String from = PrettyPrinter.print(freeVar, "", "", ppo, null);
                                    Term printBinding = printBindings.getMapping(freeVar);
                                    if (printBinding != null) {
                                        from = ((StringConstant) printBinding).getBareName();
                                    }

                                    if (!first) {
                                        stringBuilder.append(", ");
                                    }

                                    stringBuilder.append(from).append(" => ").append(PrettyPrinter.print(to, "", "", ppo, printBindings));
                                    first = false;
                                    bindingCount++;
                                }
                            }

                            stringBuilder.append("}");
                            if (bindingCount > 0) {
                                Utils.println(String.format("                     with: %s.", stringBuilder.toString()));
                            }
                        }

                    }
                }

                
                Utils.println("           OpenList size =  "+ getTask().open.size() + ".  Max Open = " + maxOpen + ".");
                
                Utils.println("\n--------------------------------------------------------------------------------\n");
            }
        } catch (Throwable e) {
            Utils.println("Error occurred while tracing: " + e.toString() + ".");
        }
    }

    private boolean isSpyLiteral(Literal traceLiteral) {
        return getStringHandler().spyEntries.includeElement(traceLiteral.predicateName, traceLiteral.getArity());
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

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.spy) {

                for (int i = 0; i < negatedLiteral.numberArgs(); i++) {

                    Term arg = negatedLiteral.getArgument(i);
                    PredicateNameAndArity predicateNameArity = getPredicateNameAndArity(arg);

                    if (predicateNameArity != null) {
                        getTask().getSpyEntries().addLiteral(predicateNameArity);
                    }
                }

                children = new ArrayList<>(1);
                children.add(createChildWithMultipleNewLiterals(hornSearchNode, null, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.nospy) {

                for (int i = 0; i < negatedLiteral.numberArgs(); i++) {

                    Term arg = negatedLiteral.getArgument(i);
                    PredicateNameAndArity predicateNameArity = getPredicateNameAndArity(arg);

                    if (predicateNameArity != null) {
                        getTask().getSpyEntries().removeLiteral(predicateNameArity);
                    }
                }

                children = new ArrayList<>(1);
                children.add(createChildWithMultipleNewLiterals(hornSearchNode, null, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.nospyall) {

                getTask().getSpyEntries().clear();

                children = new ArrayList<>(1);
                children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.trace) {

                if (negatedLiteral.numberArgs() != 1) {
                    Utils.error("trace must have 1 argument.  You have: '" + negatedLiteral + "'");
                }

                Term arg1 = negatedLiteral.getArgument(0);
                if (!(arg1 instanceof NumericConstant)) {
                    Utils.error("trace/1 argument must be a number.");
                }

                assert arg1 instanceof NumericConstant;
                NumericConstant numericConstant = (NumericConstant) arg1;
                int traceLevel = numericConstant.value.intValue();

                getTask().setTraceLevel(traceLevel);

                children = new ArrayList<>(1);
                children.add(createChildWithMultipleNewLiterals(hornSearchNode, null, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.notrace) {

                if (negatedLiteral.numberArgs() != 0) {
                    Utils.error("notrace must have 0 arguments.  You have: '" + negatedLiteral + "'");
                }

                getTask().setTraceLevel(0);

                children = new ArrayList<>(1);
                children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.retract) {

                if (negatedLiteral.numberArgs() != 1) {
                    Utils.error("retract must have 1 arguments.  You have: '" + negatedLiteral + "'");
                }

                boolean successful = false;

                Sentence termAsSentence = negatedLiteral.getArgument(0).asSentence();
                if (termAsSentence instanceof DefiniteClause) {
                    DefiniteClause definiteClause = (DefiniteClause) termAsSentence;

                    bindingList = new BindingList();

                    // Do the first 'asserted(A), removeFromClausebase(A)' via calling retract.
                    successful = getTask().getClausebase().retract(definiteClause, bindingList);
                }

                if (successful) {
                    children = new ArrayList<>(2);

                    // retract is essentially defined as:
                    //   retract(A) :- asserted(A), removeFromClausebase(A).
                    //
                    // The first child is successful proof corresponding to a sucessful asserted(A), removeFromClausebase(A).
                    // The asserted(A), removeFromClausebase(A) was done above.
                    children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, bindingList));

                    // The second child allows for the backtracking over the retract to remove multiple clauses from the clausebase.
                    children.add(createChildWithSingleNewLiteral(hornSearchNode, negatedLiteral, queryLiterals));
                    return children;
                }
                else {
                    return null;
                }
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.retractall) {

                if (negatedLiteral.numberArgs() != 1) {
                    Utils.error("retractall must have 1 arguments.  You have: '" + negatedLiteral + "'");
                }

                boolean successful = false;

                Sentence termAsSentence = negatedLiteral.getArgument(0).asSentence();
                if (termAsSentence instanceof Literal) {
                    DefiniteClause definiteClause = (DefiniteClause) termAsSentence;

                    successful = getTask().getClausebase().retractAllClauseWithHead(definiteClause);
                }

                if (successful) {
                    children = new ArrayList<>(1);
                    children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, bindingList));
                    return children;
                }
                else {
                    return null;
                }
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

    private PredicateNameAndArity getPredicateNameAndArity(Term arg) {

        HandleFOPCstrings stringHandler = getStringHandler();

        PredicateNameAndArity predicateNameArity = null;
        PredicateName name = null;
        int arity = -1;
        if (arg instanceof StringConstant) {
            StringConstant stringConstant = (StringConstant) arg;
            String contents = stringConstant.getName();
            int index = contents.indexOf("/");
            if (index == -1) {
                name = stringHandler.getPredicateName(contents);
            }
            else {
                String namePart = contents.substring(0, index);
                String arityPart = contents.substring(index + 1);
                try {
                    arity = Integer.parseInt(arityPart);
                    name = stringHandler.getPredicateName(namePart);
                } catch (NumberFormatException ignored) {
                }
            }
        }
        else if (arg instanceof Function) {
            Function function = (Function) arg;
            if (function.functionName.name.equals("/") && function.numberArgs() == 2) {
                if (function.getArgument(0) instanceof StringConstant && function.getArgument(1) instanceof NumericConstant) {
                    name = stringHandler.getPredicateName(((StringConstant) function.getArgument(0)).getBareName());
                    arity = ((NumericConstant) function.getArgument(1)).value.intValue();
                }
            }
        }


        if (name != null) {
            predicateNameArity = new PredicateNameAndArity(name, arity);
        }

        return predicateNameArity;
    }

    private List<Literal> getQueryRemainder(List<Literal> queryLiterals, long proofCounter, int expansion, BindingList bindingList) {
        int querySize = queryLiterals.size();
        List<Literal> queryRemainder = new LinkedList<>();

        if (querySize > 0) {
            if (getTask().getTraceLevel() >= 2 || (getTask().getTraceLevel() >= 1 && isSpyLiteral(queryLiterals.get(0)))) {
                queryRemainder.add(new StackTraceLiteral(queryLiterals.get(0), proofCounter, expansion));
            }

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

        List<Literal> newQueryLiterals = getQueryRemainder(queryLiterals, proofCounter, expansion, bindingList);

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

        List<Literal> newQueryLiterals = getQueryRemainder(queryLiterals, proofCounter, expansion, null);

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

        List<Literal> newQueryLiterals = getQueryRemainder(queryLiterals, proofCounter, expansion, bindingList);

        return new HornSearchNode(hornSearchNode, getStringHandler().getClause(newQueryLiterals, false), bindingList, proofCounter, expansion);
    }

    private static class StackTraceLiteral extends Literal {

        private static final long serialVersionUID = 7775745656125260261L;

        private final Literal traceLiteral;

        private final long proofCounter;

        private final int expansion;

        StackTraceLiteral(Literal traceLiteral, long proofCount, int expansion) {
            this.traceLiteral = traceLiteral;
            this.proofCounter = proofCount;
            this.expansion = expansion;

            predicateName = traceLiteral.getStringHandler().getPredicateName("StackTrace");
        }

        int getExpansion() {
            return expansion;
        }

        Literal getTraceLiteral() {
            return traceLiteral;
        }

        long getProofCounter() {
            return proofCounter;
        }

        @Override
        public String toString(int precedenceOfCaller) {
            return "StackTrace(Return of " + traceLiteral + " [" + getProofCounter() + "." + getExpansion() + "])";
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

    protected static class CutMarkerNode extends HornSearchNode {

        private static final long serialVersionUID = 8501369564035800995L;
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

        private static final long serialVersionUID = 454415768460975726L;

        /*
         * Head of the clause that contained the cut.
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

        private static final long serialVersionUID = -7370195316256309385L;
        /**
         * Head of the clause that contained the cut.
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

    private static class FailedTraceNode extends HornSearchNode {

        private static final long serialVersionUID = 2628055531715154708L;
        final Literal failedLiteral;

        FailedTraceNode(HornClauseProver task, Literal failedLiteral, long parentProofCounter, int parentExpansionIndex) {
            super(task, null, parentProofCounter, parentExpansionIndex);
            this.failedLiteral = failedLiteral;
        }

        @Override
        public String toString() {
            return "StackTrace(Fail of " + failedLiteral + " [" + parentProofCounter + "." + parentExpansionIndex + "])";
        }
    }
}
