package edu.wisc.cs.will.Utils;

/*
 * Stopwatch.java
 * Created on September 5, 2007, 7:36 PM
 * @author twalker
 */
public class Stopwatch {

    private long startTime = -1;

    /*
     * Creates a new instance of Stopwatch and starts the watch.
     */
    public Stopwatch() {
        this(true);
    }

    /*
     * Creates a new instance of Stopwatch.
     * @param start If true, the watch is started.
     */
    private Stopwatch(boolean start) {
        if (start) {
            start();
        }
    }

    /*
     * Starts the watch. If the watch was already started, nothing is done.
     */
    private void start() {
        if (startTime == -1) {
            startTime = System.currentTimeMillis();
        }
    }

    /*
     * Returns the total time accumulated so far, in milliseconds.
     *
     * If called while the stopwatch is running, this will return the time without
     * stopping the stopwatch.
     * @return Total time so far in milliseconds.
     */
    public long getTotalTimeInMilliseconds() {
        long time = 0;
        if (startTime != -1) {
            time += System.currentTimeMillis() - startTime;
        }
        return time;
    }
}
