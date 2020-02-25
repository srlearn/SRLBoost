package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC.visitors.*;
import edu.wisc.cs.will.FOPC.visitors.ElementPositionVisitor.ElementPositionData;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.MapOfLists;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author twalker
 */
public class RelevantClauseInformation implements Cloneable, RelevantInformation {

    private static final SentenceGeneralizer GENERALIZER_SENTENCE_VISITOR = new SentenceGeneralizer();

    private static final SentenceGeneralizerVisitor SENTENCE_GENERALIZER_VISITOR = new SentenceGeneralizerVisitor();

    Example example;

    private boolean relevanceFromPositiveExample = true;

    private Sentence sentence;

    private RelevanceStrength relevanceStrength = RelevanceStrength.POSSIBLE_ANSWER;

    private List<TypeSpec> typeSpecList;

    private boolean constantsSplit = false;

    private Set<ElementPath> constantPositions = null;

    private Map<Term, Term> mappings;

    private Set<Variable> outputVariables = null;

    private RelevantClauseInformation(Example example, Sentence generalizeAdviceSentence, List<TypeSpec> typeSpecList) {
        this.example = example;
        this.sentence = generalizeAdviceSentence;
        this.typeSpecList = typeSpecList;
    }

    RelevantClauseInformation(Example generalizedExample, Sentence sentence) {
        this.example = generalizedExample;
        this.sentence = sentence;

        markConstants();
    }

    public Sentence getSentence() {
        return sentence;
    }

    public Example getExample() {
        return example;
    }

    private ConnectedSentence getImpliedSentence() {
        return example.getStringHandler().getConnectedSentence(getSentence(), ConnectiveName.IMPLIES, example);
    }

    public RelevantClauseInformation getGeneralizeRelevantInformation() {

        Example groundExample = this.example;
        Sentence groundSentence = this.getSentence();

        Map<Term, Term> termToVariableMap = new LinkedHashMap<>();

        Example newExample = new Example(GENERALIZER_SENTENCE_VISITOR.generalize(groundExample, null, termToVariableMap));
        Sentence newSentence = GENERALIZER_SENTENCE_VISITOR.generalize(groundSentence, constantPositions, termToVariableMap);

        RelevantClauseInformation newRCI = this.copy();
        newRCI.example = newExample;
        newRCI.setSentence(newSentence);
        newRCI.mappings = termToVariableMap;
        newRCI.constantPositions = constantPositions;

        return newRCI;
    }

    RelevantClauseInformation getConjunction(RelevantClauseInformation that) {
        RelevantClauseInformation newGAC;

        if (this.sentence instanceof Clause && ((Clause) this.sentence).getPosLiteralCount() == 0) {
            newGAC = that;
        }
        else if (that == null) {
            newGAC = this;
        }
        else if (that.sentence instanceof Clause && ((Clause) that.sentence).getPosLiteralCount() == 0) {
            newGAC = this;
        }
        else {
            BindingList bl = Unifier.UNIFIER.unify(this.example, that.example);

            Sentence thisRebound = this.getSentence().applyTheta(bl);
            Sentence thatRebound = that.getSentence().applyTheta(bl);

            Sentence newSentence = getStringHandler().getConnectedSentence(thisRebound, ConnectiveName.AND, thatRebound);

            Set<ElementPath> newConstantPositions = new HashSet<>();
            for (ElementPath elementPath : this.constantPositions) {
                newConstantPositions.add(elementPath.prepend(0));
            }

            for (ElementPath elementPath : that.constantPositions) {
                newConstantPositions.add(elementPath.prepend(1));
            }

            newGAC = new RelevantClauseInformation(that.example, newSentence, this.getTypeSpecList());
            newGAC.constantPositions = newConstantPositions;
            newGAC.setConstantsSplit(this.isConstantsSplit() || that.isConstantsSplit());
            newGAC.setRelevanceFromPositiveExample(this.relevanceFromPositiveExample && that.relevanceFromPositiveExample);

            newGAC.mappings = new HashMap<>();
            if (this.mappings != null) {
                newGAC.mappings.putAll(this.mappings);
            }
            if (that.mappings != null) {
                newGAC.mappings.putAll(that.mappings);
            }

            // Collect the output variables from each...we might want
            // to do something smarter at a latter point.
            for (Variable variable : this.getOutputVariables()) {
                newGAC.addOutputVariable((Variable) variable.applyTheta(bl));
            }

            for (Variable variable : that.getOutputVariables()) {
                newGAC.addOutputVariable((Variable) variable.applyTheta(bl));
            }
        }

        return newGAC;
    }

    RelevantClauseInformation getDisjunction(RelevantClauseInformation that) {
        RelevantClauseInformation newGAC;

        if (this.sentence instanceof Clause && ((Clause) this.sentence).getPosLiteralCount() == 0) {
            newGAC = that;
        }
        else if (that == null) {
            newGAC = this;
        }
        else if (that.sentence instanceof Clause && ((Clause) that.sentence).getPosLiteralCount() == 0) {
            newGAC = this;
        }
        else {
            BindingList bl = Unifier.UNIFIER.unify(this.example, that.example);

            Sentence thisRebound = this.getSentence().applyTheta(bl);
            Sentence thatRebound = that.getSentence().applyTheta(bl);

            Sentence newSentence = getStringHandler().getConnectedSentence(thisRebound, ConnectiveName.OR, thatRebound);

            Set<ElementPath> newConstantPositions = new HashSet<>();
            for (ElementPath elementPath : this.constantPositions) {
                newConstantPositions.add(elementPath.prepend(0));
            }

            for (ElementPath elementPath : that.constantPositions) {
                newConstantPositions.add(elementPath.prepend(1));
            }

            newGAC = new RelevantClauseInformation(that.example, newSentence, this.getTypeSpecList());
            newGAC.constantPositions = newConstantPositions;

            // Collect the output variables from each...we might want
            // to do something smarter at a latter point.
            for (Variable variable : this.getOutputVariables()) {
                newGAC.addOutputVariable((Variable) variable.applyTheta(bl));
            }

            for (Variable variable : that.getOutputVariables()) {
                newGAC.addOutputVariable((Variable) variable.applyTheta(bl));
            }

            newGAC.mappings = new HashMap<>();
            if (this.mappings != null) {
                newGAC.mappings.putAll(this.mappings);
            }
            if (that.mappings != null) {
                newGAC.mappings.putAll(that.mappings);
            }



            newGAC.setConstantsSplit(this.isConstantsSplit() || that.isConstantsSplit());
            newGAC.setRelevanceFromPositiveExample(true);
        }

        return newGAC;
    }

    public RelevantClauseInformation getNegationByFailure() {
        Sentence newSentence;
        Set<ElementPath> newConstantPositions = new HashSet<>();
        
        if (sentence instanceof Clause && sentence.getStringHandler().isNegationByFailure(sentence)) {
            newSentence = sentence.getStringHandler().getNegationByFailureContents((Clause) sentence);
            
            for (ElementPath elementPath : this.constantPositions) {
                newConstantPositions.add(elementPath.removeFirstElement());
            }
        }
        else if (sentence instanceof Clause) {
            newSentence = sentence.getStringHandler().getNegationByFailure((Clause) sentence);
            for (ElementPath elementPath : this.constantPositions) {
                newConstantPositions.add(elementPath.prepend(0));
            }
        }
        else {
            Clause c = sentence.asClause();
            newSentence = sentence.getStringHandler().getNegationByFailure(c);
            // We can't keep track of the constant positions since the asClause() method
            // may rearrange the sentence.
        }

        RelevantClauseInformation newGAC = new RelevantClauseInformation(example, newSentence, getTypeSpecList());
        newGAC.constantPositions = newConstantPositions;

        // We purposefully ignore the output variables of the original
        // RCI.  They no longer apply once the RCI is wrapped by the
        // negation-by-failure.

        return newGAC;
    }

    RelevantClauseInformation getInlined(HornClauseContext context) {


        Sentence newSentence = Inliner.getInlinedSentence(sentence, context);

        RelevantClauseInformation rci = copy();
        rci.setSentence(newSentence);

        return rci;
    }

    RelevantClauseInformation removeDuplicateDeterminates() {


        Sentence newSentence = DuplicateDeterminateRemover.removeDuplicates(sentence);

        RelevantClauseInformation rci = copy();
        rci.setSentence(newSentence);

        return rci;
    }

    RelevantClauseInformation removeDoubleNegations() {


        Sentence newSentence = DoubleNegationByFailureRemover.removeDoubleNegationByFailure(sentence);

        RelevantClauseInformation rci = copy();
        rci.setSentence(newSentence);

        return rci;
    }

    RelevantClauseInformation applyPruningRules(AdviceProcessor ap) {

        RelevantClauseInformation result = this;

        if ( ap.getPruningRules() != null ) {
            ConnectedSentence implication = getImpliedSentence();
            ConnectedSentence newSentence = (ConnectedSentence)SentencePruner.pruneSentence(ap.getContext(), implication, ap.getPruningRules());

            if (!implication.equals(newSentence)) {
                result = copy();
                result.setSentence(newSentence.getSentenceA());
                result.example = new Example(newSentence.getSentenceB().asClause().getPosLiteral(0));
            }
        }

        return result;
    }

    RelevantClauseInformation getCompressed() {
        Sentence newSentence = SentenceCompressor.getCompressedSentence(sentence);

        RelevantClauseInformation rci = copy();
        rci.setSentence(newSentence);

        return rci;

    }

    List<RelevantClauseInformation> expandNonOperationalPredicates(HornClauseContext context) {

        List<? extends Sentence> sentences = NonOperationalExpander.getExpandedSentences(context, sentence);

        int expansionCount = sentences.size();

        if (expansionCount > 64) {
            Utils.waitHere("Number of non-operation exapansions exceeds 64.  RCI:\n" + this + ".");
        }

        List<RelevantClauseInformation> result;

        if (sentences.size() == 1) {
            result = Collections.singletonList(this);
        }
        else {
            result = new ArrayList<>();

            for (Sentence newSentence : sentences) {
                RelevantClauseInformation newRCI = copy();
                newRCI.sentence = newSentence;
                result.add(newRCI);
            }
        }

        return result;
    }

    @Override
    public String toString() {
        return toString("");
    }

    private String toString(String prefix) {
        BindingList bl;
        bl = new BindingList();

        PrettyPrinterOptions ppo = new PrettyPrinterOptions();
        ppo.setMaximumLiteralsPerLine(1);
        ppo.setSentenceTerminator("");
        ppo.setMaximumIndentationAfterImplication(10);
        ppo.setNewLineAfterImplication(true);

        String exampleString = PrettyPrinter.print(example, "", "", ppo, bl);
        String sentenceString = PrettyPrinter.print(sentence, prefix + "  ", prefix + "  ", ppo, bl);

        return prefix + exampleString + (isRelevanceFromPositiveExample() ? "" : ", NEGATION") + ", advice = \n" + sentenceString;

    }

    private HandleFOPCstrings getStringHandler() {
        return getSentence().getStringHandler();
    }

    private boolean isConstantsSplit() {
        return constantsSplit;
    }

    private void setConstantsSplit(boolean constantsSplit) {
        this.constantsSplit = constantsSplit;
    }

    void setOriginalRelevanceStrength(RelevanceStrength relevanceStrength) {
        this.setRelevanceStrength(relevanceStrength);
    }

    RelevanceStrength getFinalRelevanceStrength() {
        return relevanceStrength;
    }

    public RelevantClauseInformation copy() {
        try {
            return clone();
        } catch (CloneNotSupportedException ex) {
            return null;
        }
    }

    protected RelevantClauseInformation clone() throws CloneNotSupportedException {
        RelevantClauseInformation newRCI = (RelevantClauseInformation) super.clone();
        if (newRCI.mappings != null) {
            newRCI.mappings = new HashMap<>(this.mappings);
        }
        if (newRCI.getSentence() != null) {
            newRCI.example = new Example(example.copy2(true, null)); // JWS: if there are any things dangling off the example, we're losing them (eg, annotations).
            newRCI.setSentence(getSentence().copy2(true, null));
        }
        return newRCI;
    }

    @Override
    public boolean equals(Object that) {
        if (that == null) {
            return false;
        }
        if (getClass() != that.getClass()) {
            return false;
        }
        final RelevantClauseInformation other = (RelevantClauseInformation) that;
        if (!Objects.equals(this.example, other.example)) {
            return false;
        }
        if (this.isRelevanceFromPositiveExample() != other.isRelevanceFromPositiveExample()) {
            return false;
        }
        if (this.getSentence() != other.getSentence() && (this.getSentence() == null || !this.sentence.equals(other.sentence))) {
            return false;
        }
        if (this.getRelevanceStrength() != other.getRelevanceStrength()) {
            return false;
        }
        if (this.getTypeSpecList() != other.getTypeSpecList() && (this.getTypeSpecList() == null || !this.typeSpecList.equals(other.typeSpecList))) {
            return false;
        }
        if (this.isConstantsSplit() != other.isConstantsSplit()) {
            return false;
        }
        return Objects.equals(this.mappings, other.mappings);
    }

    @Override
    public int hashCode() {
        int hash = 5;
        hash = 59 * hash + (this.example != null ? this.example.hashCode() : 0);
        hash = 59 * hash + (this.isRelevanceFromPositiveExample() ? 1 : 0);
        hash = 59 * hash + (this.getSentence() != null ? this.getSentence().hashCode() : 0);
        hash = 59 * hash + (this.getRelevanceStrength() != null ? this.getRelevanceStrength().hashCode() : 0);
        hash = 59 * hash + (this.getTypeSpecList() != null ? this.getTypeSpecList().hashCode() : 0);
        hash = 59 * hash + (this.isConstantsSplit() ? 1 : 0);
        hash = 59 * hash + (this.mappings != null ? this.mappings.hashCode() : 0);
        return hash;
    }

    public List<TypeSpec> getTypeSpecList() {
        if (typeSpecList == null) {
            List<TypeSpec> specs = example.getTypeSpecs();

            typeSpecList = new ArrayList<>();
            if (specs != null) {
                for (TypeSpec typeSpec : specs) {
                    TypeSpec newTypeSpec = null;
                    if (typeSpec != null) {
                        newTypeSpec = typeSpec.copy();
                    }
                    typeSpecList.add(newTypeSpec);
                }
            }
        }

        return typeSpecList;
    }

    public boolean isEquivalentUptoVariableRenaming(RelevantInformation ri) {
        if (ri instanceof RelevantClauseInformation) {
            RelevantClauseInformation that = (RelevantClauseInformation) ri;
            Sentence c1 = this.getImpliedSentence();
            Sentence c2 = that.getImpliedSentence();
            return c1.isEquivalentUptoVariableRenaming(c2);
        }
        else {
            return false;
        }

    }

    public boolean subsumes(RelevantInformation ri) {
        if (ri instanceof RelevantClauseInformation) {
            RelevantClauseInformation that = (RelevantClauseInformation) ri;
            Sentence c1 = this.getImpliedSentence();
            Sentence c2 = that.getImpliedSentence();

            BindingList bl1 = Unifier.UNIFIER.unify(c1, c2);

            if (bl1 == null) {
                return false;
            }

            Sentence c3 = c2.applyTheta(bl1);

            return c2.isEquivalentUptoVariableRenaming(c3);

        }
        else {
            return false;
        }
    }

    public boolean isRelevanceFromPositiveExample() {
        return relevanceFromPositiveExample;
    }

    public void setRelevanceFromPositiveExample(boolean relevanceFromPositiveExample) {
        this.relevanceFromPositiveExample = relevanceFromPositiveExample;
    }

    public RelevanceStrength getRelevanceStrength() {
        return relevanceStrength;
    }

    void setRelevanceStrength(RelevanceStrength relevanceStrength) {
        this.relevanceStrength = relevanceStrength;
    }

    private void markConstants() {
        ConstantMarkerRemover sv = new ConstantMarkerRemover();
        ConstantMarkerData data = new ConstantMarkerData();

        setSentence(getSentence().accept(sv, data));
        constantPositions = data.constantPositions;
    }

    public boolean isValidAdvice(AdviceProcessor ap) {

        Set<PredicateNameAndArity> usedPredicate = PredicateCollector.collectPredicates(sentence, ap.getContext());

        for (PredicateNameAndArity pnaa : usedPredicate) {
            // We want to check that all predicates that are used are defined in the clausebase.
            // However, if it is a non-operational, we assume the operationals are defined somewhere.
            if (!pnaa.isNonOperational() && !ap.getContext().getClausebase().isDefined(pnaa) && !pnaa.getPredicateName().name.startsWith("linked")) {
                Utils.waitHere("Unknown predicate name in advice: " + pnaa + ".");
                return false;
            }
        }

        // Look for Singleton variables that occur as inputs to Functions...

        Sentence s = getImpliedSentence();

        Collection<Variable> headVariables = example.collectAllVariables();


        Map<Variable, Integer> counts = VariableCounter.countVariables(sentence);

        PositionData positions = null;

        for (Map.Entry<Variable, Integer> entry : counts.entrySet()) {
            if (entry.getValue() == 1) {
                // Here is a singleton.  See if it is an argument to a functionAsPred.

                // What we are going to do here is look up the position of the
                // variable in the sentence.  Once we have the position, we will
                // grap the variables "parent", i.e., the literal or function that
                // is using it.  Once we have the literal/function, we will first
                // check if it is a FunctionAsPred.  If it is, we will check if
                // the singleton variable is in the output position.  If it isn't,
                // we will assume that the advice was improperly bound and toss it.
                Variable v = entry.getKey();

                if (!headVariables.contains(v)) {

                    if (positions == null) {
                        positions = new PositionData();
                        ElementPositionVisitor<PositionData> epv = new ElementPositionVisitor<>(new PositionRecorder());
                        s.accept(epv, positions);
                    }

                    ElementPath path = positions.elementToPathMap.getValue(v, 0);

                    ElementPath parentPath = path.getParent();

                    AllOfFOPC parent = positions.pathToElementMap.get(parentPath);

                    if (parent instanceof LiteralOrFunction) {
                        LiteralOrFunction literalOrFunction = (LiteralOrFunction) parent;
                        PredicateName pn = literalOrFunction.getPredicateName();

                        if (pn.isDeterminateOrFunctionAsPred(literalOrFunction.getArity())) {
                            // Damn output indices count from 1!!!!
                            if (pn.getDeterminateOrFunctionAsPredOutputIndex(literalOrFunction.getArity()) - 1 != path.getIndex() && !literalOrFunction.getPredicateName().name.equals("ilField_Composite_name")) {
                                // The ilField_Composite_name is a total hack for the BL project.  ilField_Composite_name is a function, but it is one
                                // in which can either translate from argument 1 to 2 as in: ilField_Composite_name(world, nonSymbol, ?Symbol, state),
                                // or translate from argument 2 to 1: ilField_Composite_name(world, nonSymbol, ?Symbol, state).
                                // Thus, either argument could be unbound.  We really need a pruning rule for this, but
                                // until I get around to writing pruning for the AdviceProcessor, I think I will just hack this up.
                                // TODO(@hayesall): `isVerifyInputsToFunctionsAsPredAreBoundEnabled` was dropped since it was always true, this might be dropped as well.
                                Utils.waitHere("isVerifyInputsToFunctionsAsPredAreBoundEnabled caused invalid advice: " + pn + ".");
                                return false;
                            }
                        }
                    }
                }
            }
        }

        return true;
    }

    private void setSentence(Sentence sentence) {
        this.sentence = sentence;
    }

    void addOutputVariable(Variable e) {
        if (outputVariables == null) {
            outputVariables = new HashSet<>();
        }

        outputVariables.add(e);
    }

    private Set<Variable> getOutputVariables() {
        if (outputVariables == null) {
            return Collections.EMPTY_SET;
        }
        else {
            return outputVariables;
        }
    }

    static class ConstantMarkerData {

        ElementPath currentPosition = new ElementPath(0);

        final Set<ElementPath> constantPositions;

        ConstantMarkerData() {
            this.constantPositions = new HashSet<>();
        }

        void markCurrentPositionAsConstant() {
            constantPositions.add(currentPosition);
        }

        @Override
        public String toString() {
            return "GeneralizerData{" + "\n  currentPosition=" + currentPosition + "\n  constantPositions=" + constantPositions + "\n}";
        }
    }

    public static class ConstantMarkerRemover extends DefaultFOPCVisitor<ConstantMarkerData> {

        ConstantMarkerRemover() {}

        public Clause visitClause(Clause clause, ConstantMarkerData data) {
            List<Literal> positiveLits = null;
            List<Literal> negativeLits = null;

            ElementPath oldPath = null;
            if (data != null) {
                oldPath = data.currentPosition;
            }

            if (clause.getPosLiteralCount() > 0) {
                positiveLits = new ArrayList<>();
                for (int i = 0; i < clause.getPosLiteralCount(); i++) {
                    Literal literal = clause.getPosLiteral(i);
                    if (data != null) {
                        data.currentPosition = new ElementPath(oldPath, i);
                    }
                    Literal newLit = (Literal) literal.accept(this, data);
                    positiveLits.add(newLit);
                }
            }

            if (clause.getNegLiteralCount() > 0) {
                negativeLits = new ArrayList<>();
                for (int i = 0; i < clause.getNegLiteralCount(); i++) {
                    Literal literal = clause.getNegLiteral(i);
                    if (data != null) {
                        data.currentPosition = new ElementPath(oldPath, -1 * i);
                    }
                    Literal newLit = (Literal) literal.accept(this, data);
                    negativeLits.add(newLit);
                }
            }

            if (data != null) {
                data.currentPosition = oldPath;
            }

            return clause.getStringHandler().getClause(positiveLits, negativeLits);
        }

        public Literal visitLiteral(Literal literal, ConstantMarkerData data) {

            return processTermsOfLOT(literal, data);
        }

        @Override
        public Term visitFunction(Function function, ConstantMarkerData data) {
            Term result = getConstantTerm(function, data);

            if (result == null) {
                result = processTermsOfLOT(function, data).asFunction();
            }

            return result;
        }

        /* If this is a constant marker, return the constant, otherwise returns null.
         */
        private Term getConstantTerm(LiteralOrFunction literalOrFunction, ConstantMarkerData data) {

            PredicateName marker = literalOrFunction.getStringHandler().getPredicateName("constant");

            Term result = null;

            if (literalOrFunction.getPredicateName().equals(marker) && literalOrFunction.getArity() == 1) {

                data.markCurrentPositionAsConstant();

                result = literalOrFunction.getArgument(0);
            }

            return result;
        }

        private Literal processTermsOfLOT(LiteralOrFunction literal, ConstantMarkerData data) {
            Literal result = literal.asLiteral();

            if (literal.getArity() != 0) {
                List<Term> newTerms;

                ElementPath oldPath = null;
                if (data != null) {
                    oldPath = data.currentPosition;
                }

                newTerms = new ArrayList<>();
                for (int i = 0; i < literal.getArity(); i++) {
                    Term term = literal.getArgument(i);
                    if (data != null) {
                        data.currentPosition = new ElementPath(oldPath, i);
                    }
                    Term newTerm = term.accept(this, data);
                    newTerms.add(newTerm);
                }

                if (data != null) {
                    data.currentPosition = oldPath;
                }

                result = literal.getStringHandler().getLiteral(literal.asLiteral(), newTerms);
            }

            return result;
        }
    }

    public static class GeneralizerData2 extends ElementPositionData {

        final Set<ElementPath> constantPositions;

        final Map<Term, Term> currentMappings;

        GeneralizerData2(Set<ElementPath> constantPositions, Map<Term, Term> currentMappings) {
            this.constantPositions = constantPositions;
            this.currentMappings = currentMappings;
        }

        boolean isCurrentPositionConstant() {
            return constantPositions != null && constantPositions.contains(getCurrentPosition());
        }

        @Override
        public String toString() {
            return "GeneralizerData{" + "\n  currentPosition=" + currentPosition + "\n  constantPositions=" + constantPositions + "\n  currentMappings=" + currentMappings + "\n}";
        }
    }

    static class SentenceGeneralizer {

        SentenceGeneralizer() {
        }

        <T extends Sentence> T generalize(T clause, Set<ElementPath> constantPositions, Map<Term, Term> mappings) {
            GeneralizerData2 data = new GeneralizerData2(constantPositions, mappings);

            return (T) clause.accept(SENTENCE_GENERALIZER_VISITOR, data);
        }
    }

    private static class SentenceGeneralizerVisitor extends ElementPositionVisitor<GeneralizerData2> {

        @Override
        public Term visitFunction(Function function, GeneralizerData2 data) {
            Term newTerm = function;

            if (!data.isCurrentPositionConstant()) {
                Term mappedVariable;
                if ((mappedVariable = data.currentMappings.get(function)) != null) {
                    newTerm = mappedVariable;
                }
                else if (function.functionName.name.startsWith("linked") && function.getArity() == 1) {
                    mappedVariable = function.getStringHandler().getNewUnamedVariable();
                    data.currentMappings.put(function, mappedVariable);
                    newTerm = mappedVariable;
                }
                else {
                    newTerm = super.visitFunction(function, data);
                }
            }

            return newTerm;
        }

        @Override
        public Term visitConsCell(ConsCell consCell, GeneralizerData2 data) {
            // Here we are going to generalize any given list as a single variable.
            // This probably won't work when if there is important structure in the
            // the list it's self.
            Term newTerm = consCell;
            if (!data.isCurrentPositionConstant()) {
                Term mappedVariable;
                if ((mappedVariable = data.currentMappings.get(consCell)) != null) {
                    newTerm = mappedVariable;
                }
                else {
                    mappedVariable = consCell.getStringHandler().getNewUnamedVariable();
                    data.currentMappings.put(consCell, mappedVariable);
                    newTerm = mappedVariable;
                }
            }

            return newTerm;
        }

        @Override
        public Term visitNumericConstant(NumericConstant term, GeneralizerData2 data) {
            return handleConstant(term, data);
        }

        @Override
        public Term visitOtherTerm(Term term, GeneralizerData2 data) {
            return handleNonConstant(term, data);
        }

        @Override
        public Term visitStringConstant(StringConstant term, GeneralizerData2 data) {
            return handleConstant(term, data);
        }

        @Override
        public Term visitVariable(Variable term, GeneralizerData2 data) {

            return handleNonConstant(term, data);
        }

        private Term handleNonConstant(Term term, GeneralizerData2 data) {
            Term newTerm = term;
            Term mappedVariable;
            if ((mappedVariable = data.currentMappings.get(term)) != null) {
                newTerm = mappedVariable;
            }
            return newTerm;
        }

        private Term handleConstant(Constant term, GeneralizerData2 data) {
            Term newTerm = term;

            if (!data.isCurrentPositionConstant()) {
                Term mappedVariable;
                if ((mappedVariable = data.currentMappings.get(term)) != null) {
                    newTerm = mappedVariable;
                }
                else {
                    mappedVariable = term.getStringHandler().getNewUnamedVariable();
                    data.currentMappings.put(term, mappedVariable);
                    newTerm = mappedVariable;
                }
            }

            return newTerm;
        }
    }

    static class PositionData extends ElementPositionData {

        final Map<ElementPath, AllOfFOPC> pathToElementMap = new HashMap<>();

        final MapOfLists<AllOfFOPC, ElementPath> elementToPathMap = new MapOfLists<>();

    }

    public static class PositionRecorder implements ElementPositionListener<PositionData> {

        public boolean visiting(Sentence s, PositionData data) {
            data.pathToElementMap.put(data.getCurrentPosition(), s);
            data.elementToPathMap.add(s, data.getCurrentPosition());
            return true;
        }

        public boolean visiting(Term t, PositionData data) {
            data.pathToElementMap.put(data.getCurrentPosition(), t);
            data.elementToPathMap.add(t, data.getCurrentPosition());
            return true;
        }
    }
}
