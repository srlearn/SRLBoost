package edu.wisc.cs.will.Utils;

import java.util.Comparator;

public class AlphanumComparator implements Comparator<String> {

    public static final AlphanumComparator ALPHANUM_COMPARATOR = new AlphanumComparator();

    private char[] numbers = {'1', '2', '3', '4', '5', '6', '7', '8', '9', '0'};

    private AlphanumComparator() {
    }

    private boolean isIn(char ch, char[] chars) {
        for (char aChar : chars) {
            if (ch == aChar) {
                return true;
            }
        }
        return false;
    }

    private boolean inChunk(char ch, String s) {
        if (s.length() == 0) {
            return true;
        }

        char s0 = s.charAt(0);

        // 0 = alphabetic, 1 = numeric
        int chunkType = 0;

        if (isIn(s0, numbers)) {
            chunkType = 1;
        }

        if ((chunkType == 0) && (isIn(ch, numbers))) {
            return false;
        }
        return (chunkType != 1) || (isIn(ch, numbers));
    }

    @Override
    public int compare(String s1, String s2) {
        // This is soo much easier in a pattern-matching
        // language like Perl!

        int thisMarker = 0;
        int thisNumericChunk;
        String thisChunk;
        int thatMarker = 0;
        int thatNumericChunk;
        String thatChunk;

        while ((thisMarker < s1.length()) && (thatMarker < s2.length())) {
            char thisCh = s1.charAt(thisMarker);
            char thatCh = s2.charAt(thatMarker);

            thisChunk = "";
            thatChunk = "";

            while ((thisMarker < s1.length()) && inChunk(thisCh, thisChunk)) {
                thisChunk = thisChunk + thisCh;
                thisMarker++;
                if (thisMarker < s1.length()) {
                    thisCh = s1.charAt(thisMarker);
                }
            }

            while ((thatMarker < s2.length()) && inChunk(thatCh, thatChunk)) {
                thatChunk = thatChunk + thatCh;
                thatMarker++;
                if (thatMarker < s2.length()) {
                    thatCh = s2.charAt(thatMarker);
                }
            }

            int thisChunkType = isIn(thisChunk.charAt(0), numbers) ? 1 : 0;
            int thatChunkType = isIn(thatChunk.charAt(0), numbers) ? 1 : 0;

            // If both chunks contain numeric characters, sort them numerically
            int result = 0;
            if ((thisChunkType == 1) && (thatChunkType == 1)) {
                thisNumericChunk = Integer.parseInt(thisChunk);
                thatNumericChunk = Integer.parseInt(thatChunk);
                if (thisNumericChunk < thatNumericChunk) {
                    result = -1;
                }
                if (thisNumericChunk > thatNumericChunk) {
                    result = 1;
                }
            }
            else {
                result = thisChunk.compareTo(thatChunk);
            }

            if (result != 0) {
                return result;
            }
        }

        return 0;
    }
}

