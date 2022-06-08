package edu.wisc.cs.will.Utils.condor;

import edu.wisc.cs.will.Utils.Utils;

import java.io.*;

/*
 * @author twalker
 */
public class CondorFileInputStream extends InputStream {

    private final InputStream stream;

    public CondorFileInputStream(File file) throws FileNotFoundException {
        stream = new FileInputStream(file);
    }

    public CondorFileInputStream(String fileName) throws FileNotFoundException  {

        stream = new FileInputStream(Utils.replaceWildCards(fileName));
    }

    public long skip(long n) throws IOException {
        checkStream();
        return stream.skip(n);
    }

    public synchronized void reset() throws IOException {
        checkStream();
        stream.reset();
    }

    public int read(byte[] b, int off, int len) throws IOException {
        checkStream();
        return stream.read(b, off, len);
    }

    public int read(byte[] b) throws IOException {
        checkStream();
        return stream.read(b);
    }

    public int read() throws IOException {
        checkStream();
        return stream.read();
    }

    public boolean markSupported() {
        return (stream != null && stream.markSupported());
    }

    public synchronized void mark(int readlimit) {
        if (stream != null) {
            stream.mark(readlimit);
        }
    }

    public void close() throws IOException {
        if (stream != null) {
            stream.close();
        }
    }

    public int available() throws IOException {
        checkStream();
        return stream.available();
    }

    private void checkStream() throws IOException {
        if (stream == null) {
            throw new IOException("CondorFileInputStream: delegate stream is null.  Perhaps a problem when the stream was opened?");
        }
    }
}
