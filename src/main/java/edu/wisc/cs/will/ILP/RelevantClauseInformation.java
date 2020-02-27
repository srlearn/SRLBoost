package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC.visitors.*;
import edu.wisc.cs.will.FOPC.visitors.ElementPositionVisitor.ElementPositionData;

import java.util.*;

/*
 * @author twalker
 */
public class RelevantClauseInformation implements Cloneable, RelevantInformation {

    private static final SentenceGeneralizer GENERALIZER_SENTENCE_VISITOR = new SentenceGeneralizer();

    private static final SentenceGeneralizerVisitor SENTENCE_GENERALIZER_VISITOR = new SentenceGeneralizerVisitor();

    private Example example;

    private boolean relevanceFromPositiveExample = true;

    private Sentence sentence;

    private RelevanceStrength relevanceStrength = RelevanceStrength.POSSIBLE_ANSWER;

    private List<TypeSpec> typeSpecList;

    private Map<Term, Term> mappings;

    RelevantClauseInformation(Example generalizedExample, Sentence sentence) {
        this.example = generalizedExample;
        this.sentence = sentence;

        markConstants();
    }

    private Sentence getSentence() {
        return sentence;
    }

    @Override
    public String toString() {

        BindingList bl;
        bl = new BindingList();

        PrettyPrinterOptions ppo = new PrettyPrinterOptions();
        ppo.setMaximumLiteralsPerLine(1);
        ppo.setSentenceTerminator("");
        ppo.setMaximumIndentationAfterImplication(10);
        ppo.setNewLineAfterImplication(true);

        String exampleString = PrettyPrinter.print(example, "", "", ppo, bl);
        String sentenceString = PrettyPrinter.print(sentence, "  ", "  ", ppo, bl);

        return exampleString + (isRelevanceFromPositiveExample() ? "" : ", NEGATION") + ", advice = \n" + sentenceString;

    }

    void setOriginalRelevanceStrength(RelevanceStrength relevanceStrength) {
        this.setRelevanceStrength(relevanceStrength);
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
        hash = 59 * hash + (this.mappings != null ? this.mappings.hashCode() : 0);
        return hash;
    }

    private List<TypeSpec> getTypeSpecList() {
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

    private boolean isRelevanceFromPositiveExample() {
        return relevanceFromPositiveExample;
    }

    public void setRelevanceFromPositiveExample(boolean relevanceFromPositiveExample) {
        this.relevanceFromPositiveExample = relevanceFromPositiveExample;
    }

    private RelevanceStrength getRelevanceStrength() {
        return relevanceStrength;
    }

    private void setRelevanceStrength(RelevanceStrength relevanceStrength) {
        this.relevanceStrength = relevanceStrength;
    }

    private void markConstants() {
        ConstantMarkerRemover sv = new ConstantMarkerRemover();
        ConstantMarkerData data = new ConstantMarkerData();

        setSentence(getSentence().accept(sv, data));
    }

    private void setSentence(Sentence sentence) {
        this.sentence = sentence;
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

    private static class SentenceGeneralizer {
        // TODO(@hayesall): Empty class.
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
        public Term visitNumericConstant(NumericConstant term, GeneralizerData2 data) {
            return handleConstant(term, data);
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

}
