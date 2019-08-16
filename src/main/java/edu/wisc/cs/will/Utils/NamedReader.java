package edu.wisc.cs.will.Utils;

import java.io.BufferedReader;
import java.io.Reader;

/**
 * @author twalker
 */
public class NamedReader extends BufferedReader {

    private String name;

    public NamedReader(Reader in, String name) {
        super(in);
        this.name = name;
    }

    public NamedReader(Reader in, int sz, String name) {
        super(in,sz);
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }

}
