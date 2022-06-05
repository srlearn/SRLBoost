package edu.wisc.cs.will.Utils.condor;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.util.zip.GZIPOutputStream;

/*
 * @author twalker
 */
public class CompressedOutputStream extends OutputStream {

    private final OutputStream realStream;

    public CompressedOutputStream(String fileName, boolean compressOutput) throws IOException {
        this(new File(fileName), compressOutput);
    }

    private CompressedOutputStream(File file, boolean compressOutput) throws IOException {
        if (compressOutput) {
            File gzFile = CompressionUtilities.getGZFile(file);
            realStream = new GZIPOutputStream(new CondorFileOutputStream(gzFile));
        }
        else {
            File noGZFile = CompressionUtilities.getNonGZFile(file);
            realStream = new CondorFileOutputStream(noGZFile);
        }
    }

    @Override
    public void write(int b) throws IOException {
        realStream.write(b);
    }

    @Override
    public void close() throws IOException {
        realStream.close();
    }

    @Override
    public void flush() throws IOException {
        realStream.flush();
    }

    @Override
    public void write(byte[] b) throws IOException {
        realStream.write(b);
    }

    @Override
    public void write(byte[] b, int off, int len) throws IOException {
        realStream.write(b, off, len);
    }
}
