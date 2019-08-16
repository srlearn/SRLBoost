package edu.wisc.cs.will.Utils.condor;

import edu.wisc.cs.will.Utils.Utils;
import java.io.File;

/**
 * @author twalker
 */
public final class CondorUtilities {

    private CondorUtilities() {}

    private static Boolean condor = null;

    private static Boolean chirp = null;

    public static boolean isCondor() {
        if (condor == null) {

            String condorSlot = System.getenv("_CONDOR_SLOT");
            condor = condorSlot != null;

            if (condor) {
                Utils.println("% Executing under condor.");
            }
        }

        return condor;
    }

    static boolean isChirp() {
        if (chirp == null) {
            chirp = false;
            if (isCondor()) {
                // This is really a hack!  The chirp is created in either case.  However
                // if we are in same domain file system, we will be in our run directory
                // while the chirp config will be somewhere else.
                // If this breaks, we could probably check if the user.dir == chirp.config dir
                // as a second attempt.
                String filename = System.getProperty("user.dir");
                if (filename != null) {
                    File f = new CondorFile(filename, "chirp.config");
                    chirp = f.exists();
                }
            }

            if (chirp) {
                Utils.println("% Using Chirp for IO.");
            }
        }

        return chirp;
    }
}
