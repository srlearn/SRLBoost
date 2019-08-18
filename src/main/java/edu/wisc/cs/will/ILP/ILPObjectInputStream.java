package edu.wisc.cs.will.ILP;

import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;

import edu.wisc.cs.will.FOPC.FOPCInputStream;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchInputStream;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask;

/*
 * @author twalker
 */
public class ILPObjectInputStream extends ObjectInputStream implements FOPCInputStream, StateBasedSearchInputStream {
    
    private HandleFOPCstrings stringHandler;

    private StateBasedSearchTask stateBasedSearchTask;

    ILPObjectInputStream(InputStream in, HandleFOPCstrings stringHandler, StateBasedSearchTask stateBasedSearchTask) throws IOException {
        super(in);
        this.stringHandler = stringHandler;
        this.stateBasedSearchTask = stateBasedSearchTask;
    }

    public HandleFOPCstrings getStringHandler() {
        return stringHandler;
    }

    public void setStringHandler(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;
    }

    public StateBasedSearchTask getStateBasedSearchTask() {
        return stateBasedSearchTask;
    }
}
