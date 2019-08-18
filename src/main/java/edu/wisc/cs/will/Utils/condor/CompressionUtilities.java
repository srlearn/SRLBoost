package edu.wisc.cs.will.Utils.condor;

import java.io.File;

/*
 * @author twalker
 */
class CompressionUtilities {

    static File getGZFile(File originalFile) {

        if (originalFile.getName().endsWith(".gz")) {
            return originalFile;
        }
		return new File( originalFile.getParent(), originalFile.getName() + ".gz");
    }
    
    static File getNonGZFile(File originalFile) {

        if (originalFile.getName().endsWith(".gz")) {
            String gzFileName   = originalFile.getName();
            String noGZFileName = gzFileName.substring(0, gzFileName.length() - 3);

            return new File( originalFile.getParent(), noGZFileName);
        }
		return originalFile;
    }

    private CompressionUtilities() {
    }
}
