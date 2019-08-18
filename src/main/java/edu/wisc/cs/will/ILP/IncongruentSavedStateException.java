package edu.wisc.cs.will.ILP;

/*
 * @author twalker
 */
class IncongruentSavedStateException extends Exception {

    /*
     * Constructs an instance of <code>IncongruentCheckpointException</code> with the specified detail message.
     * @param msg the detail message.
     */
    IncongruentSavedStateException(String msg) {
        super(msg);
    }
}
