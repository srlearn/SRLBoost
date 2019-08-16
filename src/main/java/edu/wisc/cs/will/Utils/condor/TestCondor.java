package edu.wisc.cs.will.Utils.condor;

import edu.wisc.cs.will.Utils.condor.chirp.ChirpClient;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Map;
import java.util.Properties;

/**
 * @author twalker
 */
public class TestCondor {

    public static void main(String[] args) throws IOException {

        CondorFileInputStream is1 = new CondorFileInputStream("/tmp/t");
        BufferedReader r1 = new BufferedReader(new InputStreamReader(is1));
        String line;
        System.out.println("-----------------------------");
        System.out.println("File /tmp/t:");
        while ((line = r1.readLine()) != null) {
            System.out.println(line);
        }
        System.out.println("-----------------------------");

        if (CondorUtilities.isChirp()) {
            try {
                ChirpClient cc = new ChirpClient();
                String lookup = cc.lookup("/tmp/t");
                System.out.println("Results of lookup /tmp/t: " + lookup);

                lookup = cc.lookup("/tmp/blah");
                System.out.println("Results of lookup /tmp/blah: " + lookup);
            } catch (IOException iOException) {
                System.out.println("Lookup failed: " + iOException);
            }


            File f = new CondorFile(".").getAbsoluteFile();
            System.out.println("I am chirping! I am in " + f.toString());
            System.out.println("ls " + f.toString() + ":");
            String[] files = f.list();
            for (int i = 0; i < files.length; i++) {
                String string = files[i];
                System.out.println("  " + string);
            }
            System.out.println("");

        }

        System.out.println("env:");
        Map<String, String> env = System.getenv();
        for (Map.Entry<String, String> entry : env.entrySet()) {
            System.out.println(" " + entry.getKey() + " = " + entry.getValue());
        }

        System.out.println("");

        System.out.println("system properties:");
        Properties props = System.getProperties();
        for (String propName : props.stringPropertyNames()) {
            System.out.println(" " + propName + " = " + props.getProperty(propName));
        }

        String filename = System.getProperty("chirp.config");
        System.out.println("Chirp.config:" + filename);
        if (filename != null) {
            BufferedReader r = new BufferedReader(new CondorFileReader(new CondorFile(filename)));
            while (true) {
                line = r.readLine();
                if (line == null) {
                    break;
                }
                System.out.println(line);
            }
        }

        System.out.println("");
    }

    private TestCondor() {
    }
}
