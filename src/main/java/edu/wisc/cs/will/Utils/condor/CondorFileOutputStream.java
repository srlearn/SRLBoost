package edu.wisc.cs.will.Utils.condor;

import edu.wisc.cs.will.Utils.Utils;

import java.io.*;

/*
 * @author twalker
 */
public class CondorFileOutputStream extends OutputStream {

    private final OutputStream stream;

    public CondorFileOutputStream(File file) throws FileNotFoundException {
        stream = new FileOutputStream(file);
    }

    public CondorFileOutputStream(String fileName) throws FileNotFoundException {

        stream = new FileOutputStream(Utils.replaceWildCards(fileName));
    }

    public CondorFileOutputStream(File file, boolean append) throws FileNotFoundException {
        stream = new FileOutputStream(file, append);
    }

    public CondorFileOutputStream(String fileName, boolean append) throws FileNotFoundException {

        stream = new FileOutputStream(Utils.replaceWildCards(fileName), append);
    }

    public void write(byte[] b, int off, int len) throws IOException {
        checkStream();
        stream.write(b, off, len);
    }

    public void write(byte[] b) throws IOException {
        checkStream();
        stream.write(b);
    }

    public void write(int b) throws IOException {
        checkStream();
        stream.write(b);
    }

    public void flush() throws IOException {
        checkStream();
        stream.flush();
    }

    public void close() throws IOException {
        if (stream != null) {
            stream.close();
        }
    }

    private void checkStream() throws IOException {
        if (stream == null) {
            throw new IOException("CondorFileOutputStream: delegate stream is null.  Perhaps a problem when the stream was opened?");
        }
    }
}
