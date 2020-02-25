package edu.wisc.cs.will.FOPC;

public class PrettyPrinterOptions {

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
        // TODO(@hayesall): Empty constructor.
    }

    int getMaximumLiteralsPerLine() {
        if ( maximumLiteralsPerLine != -1 ) return maximumLiteralsPerLine;
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

    boolean isAlignParathesis() {
        return alignParathesis;
    }

    void setAlignParathesis() {
        this.alignParathesis = false;
    }

    boolean isNewLineAfterOpenParathesis() {
        return newLineAfterOpenParathesis;
    }

    void setNewLineAfterOpenParathesis() {
        this.newLineAfterOpenParathesis = true;
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
