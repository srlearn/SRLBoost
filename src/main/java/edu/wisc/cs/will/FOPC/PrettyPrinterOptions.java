package edu.wisc.cs.will.FOPC;

public class PrettyPrinterOptions {

    private int maximumLiteralsPerLine = -1;

    private boolean renameVariables = true;

    private boolean alignParathesis = true;

    private boolean newLineAfterOpenParathesis = true;

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
