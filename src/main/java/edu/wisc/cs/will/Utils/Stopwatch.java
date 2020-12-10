package edu.wisc.cs.will.Utils;

/*
 * Stopwatch.java
 * Created on September 5, 2007, 7:36 PM
 * @author twalker
 */
public class Stopwatch {

    private long startTime = -1;

    public Stopwatch() {
        this(true);
    }

    private Stopwatch(boolean start) {
        if (start) {
            start();
        }
    }

    private void start() {
        if (startTime == -1) {
            startTime = System.currentTimeMillis();
        }
    }

    public long getTotalTimeInMilliseconds() {
        long time = 0;
        if (startTime != -1) {
            time += System.currentTimeMillis() - startTime;
        }
        return time;
    }
}
