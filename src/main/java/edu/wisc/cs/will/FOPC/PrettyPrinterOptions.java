package edu.wisc.cs.will.FOPC;

public class PrettyPrinterOptions {

    private final int maximumTermsPerLine = -1;

    private int maximumLiteralsPerLine = -1;

    private boolean multilineOutputEnabled = true;

    private boolean renameVariables = true;

    private boolean alignParathesis = true;

    private boolean newLineAfterOpenParathesis = true;

    private int maximumConsCells = -1;

    private String sentenceTerminator = ".";

    private int maximumIndentationAfterImplication = Integer.MAX_VALUE;

    private boolean newLineAfterImplication = false;

    public PrettyPrinterOptions() {
    }

    int getMaximumLineWidth() {
        return 130;
    }

    int getMaximumTermsPerLine() {
        return maximumTermsPerLine;
    }

    int getMaximumLiteralsPerLine() {
        if ( maximumLiteralsPerLine != -1 ) return maximumLiteralsPerLine;
        if ( maximumTermsPerLine != -1 ) return maximumTermsPerLine;
        return -1;
    }

    public void setMaximumLiteralsPerLine(int maximumLiteralsPerLine) {
        this.maximumLiteralsPerLine = maximumLiteralsPerLine;
    }

    boolean isMultilineOutputEnabled() {
        return multilineOutputEnabled;
    }

    public void setMultilineOutputEnabled(boolean multilineOutputEnabled) {
        this.multilineOutputEnabled = multilineOutputEnabled;
    }

    boolean isRenameVariables() {
        return renameVariables;
    }

    public void setRenameVariables(boolean renameVariables) {
        this.renameVariables = renameVariables;
    }

    boolean isPrintClausesAsImplications() {
        return false;
    }

    boolean isAlignParathesis() {
        return alignParathesis;
    }

    void setAlignParathesis(boolean alignParathesis) {
        this.alignParathesis = alignParathesis;
    }

    boolean isNewLineAfterOpenParathesis() {
        return newLineAfterOpenParathesis;
    }

    void setNewLineAfterOpenParathesis(boolean newLineAfterOpenParathesis) {
        this.newLineAfterOpenParathesis = newLineAfterOpenParathesis;
    }

    int getMaximumConsCells() {
        return maximumConsCells;
    }

    public void setMaximumConsCells(int maximumConsCells) {
        this.maximumConsCells = maximumConsCells;
    }

    String getSentenceTerminator() {
        return sentenceTerminator;
    }

    public void setSentenceTerminator(String sentenceTerminator) {
        this.sentenceTerminator = sentenceTerminator;
    }

    int getMaximumIndentationAfterImplication() {
        return maximumIndentationAfterImplication;
    }

    public void setMaximumIndentationAfterImplication(int maximumIndentationAfterImplication) {
        this.maximumIndentationAfterImplication = maximumIndentationAfterImplication;
    }

    boolean isNewLineAfterImplication() {
        return newLineAfterImplication;
    }

    public void setNewLineAfterImplication(boolean newLineAfterImplication) {
        this.newLineAfterImplication = newLineAfterImplication;
    }

    
}
