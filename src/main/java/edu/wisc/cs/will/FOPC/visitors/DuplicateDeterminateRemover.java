package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.LinkedMapOfSets;
import edu.wisc.cs.will.Utils.MapOfLists;
import edu.wisc.cs.will.Utils.MapOfSets;

import java.util.*;

/*
 * @author twalker
 */
public class DuplicateDeterminateRemover {

    private static final int debugLevel = 0;

    private static final PassOneVisitor PASS_ONE_VISITOR = new PassOneVisitor();

    private static final PassTwoVisitor PASS_TWO_VISITOR = new PassTwoVisitor();

    private static final PassThreeVisitor PASS_THREE_VISITOR = new PassThreeVisitor();

    public static Sentence removeDuplicates(Sentence sentence) {

        /*
         * This is tricky, tricky, tricky.
         *
         * To handle ORs properly, we have to split the sentence into it's constituent parts.
         * Any time we find an OR connective, we run pass one and two on both subtrees.
         *
         * The PassOne/PassTwo visitors are setup never to recurse passed an OR connective.
         *
         * Once we have completed all the subtrees the visitor just does a normal
         * reassembly of the sentences.
         */

        Sentence result;

        if (sentence instanceof ConnectedSentence && ((ConnectedSentence) sentence).getConnective() == ConnectiveName.OR) {
            ConnectedSentence cs = (ConnectedSentence) sentence;
            Sentence sa = cs.getSentenceA();
            Sentence newSA = removeDuplicates(sa);

            Sentence sb = cs.getSentenceB();
            Sentence newSB = removeDuplicates(sb);

            result = DefaultFOPCVisitor.getCombinedConnectedSentence(cs, newSA, newSB);
        }
        else {
            result = handle(sentence);
        }

        return result;
    }

    private static Sentence handle(Sentence s) {

        // Collect all literals and collect variable groups.
        PassOneData data1 = new PassOneData();
        s.accept(PASS_ONE_VISITOR, data1); // No return value...it is just a collector.

        PassTwoData data2 = new PassTwoData(data1);
        Sentence passTwoResult = s.accept(PASS_TWO_VISITOR, data2);

        PassThreeData data3 = new PassThreeData();

        return passTwoResult.accept(PASS_THREE_VISITOR, data3);
    }

    public static class PassOneVisitor extends DefaultFOPCVisitor<PassOneData> {

        private PassOneVisitor() {}

        @Override
        public Sentence visitConnectedSentence(ConnectedSentence sentence, PassOneData data) {
            if (sentence.getConnective() != ConnectiveName.OR) {
                // During pass one, fail out of the processing when an OR is encountered.
                super.visitConnectedSentence(sentence, data);
            }
            return null;
        }

        @Override
        public Sentence visitLiteral(Literal literal, PassOneData data) {
            if (literal.getStringHandler().isNegationByFailure(literal)) {
                Clause contents = literal.getStringHandler().getNegationByFailureContents(literal);
                Clause newContents = (Clause) contents.accept(this, data);
                if (newContents != null) {
                    newContents.getPosLiteralCount();
                }
            }
            else {
                PredicateNameAndArity pnaa = literal.getPredicateNameAndArity();

                if (pnaa.isDeterminateOrFunctionAsPred()) {
                    data.addLiteral(literal);
                }
            }
            return null;
        }

        @Override
        public Term visitFunction(Function function, PassOneData data) {
            if (function.getStringHandler().isNegationByFailure(function)) {
                Clause contents = function.getStringHandler().getNegationByFailureContents(function);
                Clause newContents = (Clause) contents.accept(this, data);
                if (newContents != null) {
                    newContents.getPosLiteralCount();
                }
            }
            else {
                PredicateNameAndArity pnaa = function.getPredicateNameAndArity();

                if (pnaa.isDeterminateOrFunctionAsPred()) {
                    data.addLiteral(function);
                }
            }

            return null;
        }
    }

    public static class PassTwoVisitor extends DefaultFOPCVisitor<PassTwoData> {

        @Override
        public Sentence visitConnectedSentence(ConnectedSentence sentence, PassTwoData data) {

            if (sentence.getConnective() == ConnectiveName.OR) {
                // We have to return the sentence, otherwise we drop ors?
                return sentence;
            }
            else {
                return super.visitConnectedSentence(sentence, data);
            }

        }

        @Override
        public Literal visitLiteral(Literal literal, PassTwoData data) {

            Literal result = literal;

            if (literal.getStringHandler().isNegationByFailure(literal)) {
                PassTwoData newData = new PassTwoData(data);
                Clause contents = literal.getStringHandler().getNegationByFailureContents(literal);
                Clause newContents = (Clause) contents.accept(this, newData);
                if (newContents != null && newContents.getPosLiteralCount() == 0) {
                    newContents = literal.getStringHandler().trueClause;
                }

                result = literal.getStringHandler().getNegationByFailure(newContents);
            }
            else {
                PredicateNameAndArity pnaa = literal.getPredicateNameAndArity();

                if (pnaa.isDeterminateOrFunctionAsPred()) {
                    result = data.isLiteralUnique(literal);
                }

                result = result == null ? null : (Literal) super.visitLiteral(literal, data);
            }

            return result;
        }

        @Override
        public Term visitFunction(Function function, PassTwoData data) {

            if (function.getFunctionName().equals(function.getStringHandler().standardPredicateNames.negationByFailureAsFunction)) {
                // Only recurse into negation-by-failures
                PassTwoData newData = new PassTwoData(data);
                Clause contents = function.getStringHandler().getNegationByFailureContents(function);

                Clause newContents = (Clause) contents.accept(this, newData);
                if (newContents != null && newContents.getPosLiteralCount() == 0) {
                    newContents = function.getStringHandler().trueClause;
                }

                return function.getStringHandler().getNegationByFailure(newContents).asFunction();
            }
            else {
                return function;
            }
        }

        @Override
        public Term visitVariable(Variable variable, PassTwoData data) {
            Term t = data.getVariableBindings().getMapping(variable);

            return t == null ? variable : t;
        }
    }

    public static class PassThreeVisitor extends DefaultFOPCVisitor<PassThreeData> {

        @Override
        public Sentence visitConnectedSentence(ConnectedSentence sentence, PassThreeData data) {

            if (sentence.getConnective() == ConnectiveName.OR) {
                return removeDuplicates(sentence);
            }
            else {
                return super.visitConnectedSentence(sentence, data);
            }

        }

        @Override
        public Literal visitLiteral(Literal literal, PassThreeData data) {

            Literal result = null;

            if (literal.getStringHandler().isNegationByFailure(literal)) {

                PassThreeData newData = new PassThreeData();

                Clause contents = literal.getStringHandler().getNegationByFailureContents(literal);
                Clause newContents = (Clause) contents.accept(this, newData);
                if (newContents != null && newContents.getPosLiteralCount() == 0) {
                    newContents = literal.getStringHandler().trueClause;
                }

                result = literal.getStringHandler().getNegationByFailure(newContents);
            }
            else if (!data.isSeenLiteral(literal)) {
                result = literal;
                data.addSeenLiteral(literal);
            }

            return result;
        }

        @Override
        public Term visitFunction(Function function, PassThreeData data) {

            Function result = null;

            if (function.getStringHandler().isNegationByFailure(function)) {

                PassThreeData newData = new PassThreeData();

                Clause contents = function.getStringHandler().getNegationByFailureContents(function);
                Clause newContents = (Clause) contents.accept(this, newData);
                if (newContents != null && newContents.getPosLiteralCount() == 0) {
                    newContents = function.getStringHandler().trueClause;
                }

                result = function.getStringHandler().getNegationByFailure(newContents).asFunction();
            }
            else if (!data.isSeenLiteral(function)) {
                result = function;
                data.addSeenLiteral(function);
            }

            return result;
        }
    }

    static class PassOneData {

        private final MapOfSets<Integer, Term> groupToVariableMap = new LinkedMapOfSets<>();

        // Maps from predicates to canonical, unique,
        private final MapOfLists<PredicateNameAndArity, LitEntry> canonicalLiterals = new MapOfLists<>();

        private int nextGroupIndex = 0;

        private final LinkedList<MergeEntry> mergeList = new LinkedList<>();

        void addLiteral(LiteralOrFunction newLiteral) {
            LitEntry newInfo = createLitInfo(newLiteral);

            canonicalLiterals.add(newLiteral.getPredicateNameAndArity(), newInfo);

            scanForMergers();
            performMergers();
        }

        private LitEntry createLitInfo(LiteralOrFunction literal) {
            LitEntry info = new LitEntry(literal.getPredicateNameAndArity());

            List<Term> arguments = literal.getArguments();

            for (int i = 0; i < literal.getArity(); i++) {

                Term term = arguments.get(i);

                int groupIndex = getGroupForTerm(term);

                if (groupIndex == -1) {
                    groupIndex = createGroup();

                    groupToVariableMap.put(groupIndex, term);
                }

                info.setGroup(i, groupIndex);
            }

            return info;
        }

        private int createGroup() {
            return nextGroupIndex++;
        }

        private int getGroupForTerm(Term term) {
            for (Map.Entry<Integer, Set<Term>> entry : groupToVariableMap.entrySet()) {
                if (entry.getValue().contains(term)) {
                    return entry.getKey();
                }
            }

            return -1;
        }

        private void addMerge(MergeEntry mergyEntry) {
            mergeList.add(mergyEntry);
        }

        private void performMergers() {
            boolean done = mergeList.isEmpty();

            while (!done) {

                while (!mergeList.isEmpty()) {
                    MergeEntry me = mergeList.pop();
                    performMerger(me);
                }

                done = !scanForMergers();
            }
        }

        private void performMerger(MergeEntry mergeEntry) {

            if (debugLevel >= 1) {
                System.out.println("Merging " + mergeEntry.oldGroup + " = " + groupToVariableMap.getValues(mergeEntry.oldGroup) + " into " + mergeEntry.newGroup + " = " + groupToVariableMap.getValues(mergeEntry.newGroup) + ".");
            }

            for (List<LitEntry> list : canonicalLiterals.values()) {
                for (LitEntry litEntry : list) {
                    litEntry.renumber(mergeEntry);
                }
            }

            collapseGroups(mergeEntry);
        }

        private void collapseGroups(MergeEntry mergeEntry) {
            Set<Term> terms = groupToVariableMap.getValues(mergeEntry.oldGroup);

            groupToVariableMap.removeValues(mergeEntry.oldGroup);

            groupToVariableMap.putAll(mergeEntry.newGroup, terms);

            if (debugLevel >= 1) {
                System.out.println("Collapsed Group " + mergeEntry.newGroup + " = " + groupToVariableMap.getValues(mergeEntry.newGroup) + ".");
            }
        }

        private boolean scanForMergers() {

            boolean mergerOccurred = false;

            for (Map.Entry<PredicateNameAndArity, List<LitEntry>> entry : canonicalLiterals.entrySet()) {
                List<LitEntry> entries = entry.getValue();

                for (int index1 = 0; index1 < entries.size() - 1; index1++) {

                    LitEntry le1 = entries.get(index1);

                    for (int index2 = index1 + 1; index2 < entries.size(); index2++) {
                        LitEntry le2 = entries.get(index2);

                        if (le1.equals(le2)) {
                            int determinateIndex = le1.determinateIndex;
                            int oldGroup = le2.argumentSetIndices[determinateIndex];
                            int newGroup = le1.argumentSetIndices[determinateIndex];

                            if (oldGroup != newGroup) {
                                if (debugLevel >= 1) {
                                    System.out.println("Found merger of " + le1 + " and " + le2 + ".  Will merge " + oldGroup + " = " + groupToVariableMap.getValues(oldGroup) + " into " + newGroup + " = " + groupToVariableMap.getValues(newGroup) + ".");
                                }

                                addMerge(new MergeEntry(oldGroup, newGroup));

                                mergerOccurred = true;
                            }

                            entries.remove(index2);
                            index2--;
                        }
                    }
                }
            }

            return mergerOccurred;
        }
    }

    static class PassTwoData {

        private PassTwoData parent;

        private PassOneData passOneData;

        private final Set<LitEntry> seenLiterals = new HashSet<>();

        private Map<Integer, Term> groupBindings;

        private BindingList variableBindings;

        PassTwoData(PassOneData passOneData) {
            this.passOneData = passOneData;
            createBindings();
        }

        PassTwoData(PassTwoData parent) {
            this.parent = parent;
        }

        private void createBindings() {
            groupBindings = new HashMap<>();

            for (Integer integer : getPassOneData().groupToVariableMap.keySet()) {
                Term binding = getGroupBinding(integer);

                getGroupBindings().put(integer, binding);
            }

            variableBindings = new BindingList();

            for (Map.Entry<Integer, Set<Term>> entry : getPassOneData().groupToVariableMap.entrySet()) {
                int group = entry.getKey();
                Term groupBinding = getGroupBinding(group);

                for (Term term : entry.getValue()) {
                    if (term instanceof Variable) {
                        Variable variable = (Variable) term;

                        if (!variable.equals(groupBinding)) {
                            getVariableBindings().addBinding(variable, groupBinding);
                        }

                    }
                }
            }
        }

        private Term getGroupBinding(int groupIndex) {

            // Perform two passes of the group.  First look for
            // a constant, then just take the first variable.
            Term binding = null;

            Set<Term> terms = getPassOneData().groupToVariableMap.getValues(groupIndex);

            if (terms != null) {
                for (Term term : terms) {
                    if (term instanceof Constant) {
                        binding = term;
                    }
                }
            }

            if (binding == null) {
                binding = terms.iterator().next();
            }

            return binding;
        }

        Literal isLiteralUnique(LiteralOrFunction literalOrFunction) {

            Literal literal = literalOrFunction.asLiteral();

            Literal result = null;

            LitEntry entry = getPassOneData().createLitInfo(literal);

            Term oldDeterminateTerm = literal.getArguments().get(entry.determinateIndex);
            Term newDeterminateTerm = getGroupBindings().get(entry.argumentSetIndices[entry.determinateIndex]);

            if (newDeterminateTerm != null && oldDeterminateTerm instanceof Constant && !newDeterminateTerm.equals(oldDeterminateTerm)) {
                // Whoops...we have conflicting constant determinate terms.  This rule will never
                // be true, but we will do our best to merge things, but will leave this constant alone.
                List<Term> newArgs = new ArrayList<>();

                for (int i = 0; i < entry.argumentSetIndices.length; i++) {
                    if (i != entry.determinateIndex) {
                        Term newBinding = getGroupBindings().get(entry.argumentSetIndices[i]);
                        newArgs.add(newBinding);
                    }
                    else {
                        newArgs.add(oldDeterminateTerm);
                    }
                }

                result = literal.getStringHandler().getLiteral(literal.getPredicateName(), newArgs, literal.getArgumentNames());
            }
            else if (!isSeenLiteral(entry)) {

                // This is the first time we have seen this literal, so rebind it and return it.
                List<Term> newArgs = new ArrayList<>();

                for (int i = 0; i < entry.argumentSetIndices.length; i++) {
                    Term newBinding = getGroupBindings().get(entry.argumentSetIndices[i]);
                    newArgs.add(newBinding);
                }

                result = literal.getStringHandler().getLiteral(literal.getPredicateName(), newArgs, literal.getArgumentNames());

                seenLiterals.add(entry);
            }

            return result;
        }

        private boolean isSeenLiteral(LitEntry literalEntry) {

            boolean result = seenLiterals.contains(literalEntry);

            if (!result && parent != null) {
                result = parent.isSeenLiteral(literalEntry);
            }

            return result;
        }

        PassOneData getPassOneData() {
            if (parent != null) {
                return parent.getPassOneData();
            }
            else {
                return passOneData;
            }
        }

        Map<Integer, Term> getGroupBindings() {
            if (parent != null) {
                return parent.getGroupBindings();
            }
            else {
                return groupBindings;
            }
        }

        BindingList getVariableBindings() {
            if (parent != null) {
                return parent.getVariableBindings();
            }
            else {
                return variableBindings;
            }
        }
    }

    public static class PassThreeData {

        private final Set<Literal> seenLiterals = new HashSet<>();

        PassThreeData() {}

        void addSeenLiteral(LiteralOrFunction literal) {
            seenLiterals.add(literal.asLiteral());
        }

        boolean isSeenLiteral(LiteralOrFunction literal) {
            return seenLiterals.contains(literal.asLiteral());
        }

        @Override
        public String toString() {
            return "PassThreeData{" + "seenLiterals=" + seenLiterals + '}';
        }
    }

    private static class LitEntry {

        final PredicateNameAndArity pnaa;

        final int[] argumentSetIndices;

        final int determinateIndex;

        LitEntry(PredicateNameAndArity pnaa) {
            this.pnaa = pnaa;
            argumentSetIndices = new int[pnaa.getArity()];
            determinateIndex = pnaa.getDeterminateOrFunctionAsPredOutputIndex() - 1; // Jude numbered the argument starting at 1 for some reason.
        }

        void setGroup(int argumentIndex, int groupIndex) {
            argumentSetIndices[argumentIndex] = groupIndex;
        }

        @Override
        public String toString() {
            return pnaa.toString() + Arrays.toString(argumentSetIndices);
        }

        @Override
        public boolean equals(Object obj) {
            if (obj == null) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            final LitEntry that = (LitEntry) obj;
            if (!Objects.equals(this.pnaa, that.pnaa)) {
                return false;
            }

            for (int i = 0; i < argumentSetIndices.length; i++) {

                if (determinateIndex != i) {
                    int thisGroup = argumentSetIndices[i];
                    int thatGroup = that.argumentSetIndices[i];

                    if (thisGroup != thatGroup) {
                        return false;
                    }
                }
            }

            return this.determinateIndex == that.determinateIndex;
        }

        @Override
        public int hashCode() {
            int hash = 5;
            hash = 59 * hash + (this.pnaa != null ? this.pnaa.hashCode() : 0);

            for (int i = 0; i < argumentSetIndices.length; i++) {

                if (determinateIndex != i) {
                    hash = 59 * hash + argumentSetIndices[i];
                }
            }

            hash = 59 * hash + this.determinateIndex;
            return hash;
        }

        private void renumber(MergeEntry mergeEntry) {
            for (int i = 0; i < argumentSetIndices.length; i++) {
                if (i != determinateIndex) {
                    if (argumentSetIndices[i] == mergeEntry.oldGroup) {
                        argumentSetIndices[i] = mergeEntry.newGroup;
                    }
                }
            }
        }
    }

    private static class MergeEntry {

        final int oldGroup;

        final int newGroup;

        MergeEntry(int oldGroup, int newGroup) {
            this.oldGroup = oldGroup;
            this.newGroup = newGroup;
        }
    }

    private DuplicateDeterminateRemover() {
    }
}
