package edu.wisc.cs.will.Utils.condor;

import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;
import java.nio.CharBuffer;

/**
 * @author twalker
 */
public class CompressedFileReader extends Reader {

    private Reader delegate;

    public CompressedFileReader(String file) throws IOException {
        delegate = new InputStreamReader( new CompressedInputStream(file) );
    }

    public long skip(long n) throws IOException {
        return delegate.skip(n);
    }

    public void reset() throws IOException {
        delegate.reset();
    }

    public boolean ready() throws IOException {
        return delegate.ready();
    }

    public int read(char[] cbuf, int off, int len) throws IOException {
        return delegate.read(cbuf, off, len);
    }

    public int read(char[] cbuf) throws IOException {
        return delegate.read(cbuf);
    }

    public int read() throws IOException {
        return delegate.read();
    }

    public int read(CharBuffer target) throws IOException {
        return delegate.read(target);
    }

    public boolean markSupported() {
        return delegate.markSupported();
    }

    public void mark(int readAheadLimit) throws IOException {
        delegate.mark(readAheadLimit);
    }

    public void close() throws IOException {
        delegate.close();
    }
}
