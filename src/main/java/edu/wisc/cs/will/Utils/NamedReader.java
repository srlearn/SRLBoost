package edu.wisc.cs.will.Utils;

import java.io.BufferedReader;
import java.io.Reader;

/*
 * @author twalker
 */
public class NamedReader extends BufferedReader {

    private final String name;

    public NamedReader(Reader in, String name) {
        super(in);
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }

}
