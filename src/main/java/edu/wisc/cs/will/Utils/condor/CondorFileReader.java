package edu.wisc.cs.will.Utils.condor;

import edu.wisc.cs.will.Utils.Utils;

import java.io.*;
import java.nio.CharBuffer;

/*
 * @author twalker
 */
public class CondorFileReader extends Reader {

    private final Reader reader;

    public CondorFileReader(File file) throws FileNotFoundException  {
        reader = new InputStreamReader( new CondorFileInputStream(file));
    }

    public CondorFileReader(String fileNameRaw) throws IOException  {
    	String fileName = Utils.replaceWildCardsAndCheckForExistingGZip(fileNameRaw);
   		boolean isaGzippedFile = fileName.endsWith(".gz");
   		reader = new InputStreamReader(isaGzippedFile ? new CompressedInputStream(fileName) : new CondorFileInputStream(fileName));
    }

    public long skip(long n) throws IOException {
        checkStream();
        return reader.skip(n);
    }

    public void reset() throws IOException {
        checkStream();
        reader.reset();
    }

    public boolean ready() throws IOException {
        checkStream();
        return reader.ready();
    }

    public int read(char[] cbuf, int off, int len) throws IOException {
        checkStream();
        return reader.read(cbuf, off, len);
    }

    public int read(char[] cbuf) throws IOException {
        checkStream();
        return reader.read(cbuf);
    }

    public int read() throws IOException {
        checkStream();
        return reader.read();
    }

    public int read(CharBuffer target) throws IOException {
        checkStream();
        return reader.read(target);
    }

    public boolean markSupported() {
        return reader != null && reader.markSupported();
    }

    public void mark(int readAheadLimit) throws IOException {
        checkStream();
        reader.mark(readAheadLimit);
    }

    public void close() throws IOException {
        if ( reader != null ) reader.close();
    }

    private void checkStream() throws IOException {
        if (reader == null) {
            throw new IOException("CondorFileOutputStream: delegate stream is null.  Perhaps a problem when the stream was opened?");
        }
    }

}
