package edu.wisc.cs.will.Utils.condor;

import edu.wisc.cs.will.Utils.Utils;

import java.io.File;
import java.io.IOException;

/*
 * @author twalker
 */
public class CondorFile extends File {

    static {
        setupChirp();
    }

    public CondorFile(File parent, String child) {
        super(parent, Utils.replaceWildCards(child));
    }

    public CondorFile(String pathname) {
        super(Utils.replaceWildCards(pathname));
    }

    private static void setupChirp() {
    }

    @Override
    public boolean canExecute() {
        return super.canExecute();
    }

    @Override
    public boolean canRead() {
        return super.canRead();
    }

    @Override
    public boolean canWrite() {
        return super.canWrite();
    }

    @Override
    public boolean createNewFile() throws IOException {
        return super.createNewFile();
    }

    @Override
    public boolean delete() {
        return super.delete();
    }

    @Override
    public boolean exists() {
        return super.exists();
    }

    @Override
    public long getTotalSpace() {
        return super.getTotalSpace();
    }

    @Override
    public long getUsableSpace() {
        return super.getUsableSpace();
    }

    @Override
    public boolean isDirectory() {
        return super.isDirectory();
    }

    @Override
    public boolean isFile() {
        return super.isFile();
    }

    @Override
    public long lastModified() {
        return super.lastModified();
    }

    @Override
    public long length() {
        return super.length();
    }

    @Override
    public String[] list() {
        return super.list();
    }

    @Override
    public File[] listFiles() {
        return super.listFiles();
    }

    @Override
    public boolean mkdir() {
        return super.mkdir();
    }

    @Override
    public boolean mkdirs() {
        return super.mkdirs();
    }

    @Override
    public boolean renameTo(File dest) {
        return super.renameTo(dest);
    }

    @Override
    public File getParentFile() {
    	String parent = getParent();
    	if (parent == null) { return null; } // Maybe we should throw an error here?  JWS 10/16/10
        return new CondorFile(parent);
    }
}
