package edu.wisc.cs.will.Utils;
import java.util.List;

/**
 * @author twalker
 */
public class Permute {

    /** Randomly permute array in place.
     *
     * @param <T>  Type of list to permute.
     * @param list List to permute in place.  It is highly recommended that this
     * list be a list with quick random access (such as ArrayList).
     */
    public static <T> void permute(List<T> list) {
        if (list != null) {
            for (int i = 1; i < list.size(); i++) {
                int j = (int) (Utils.random() * (i + 1));
                T swap = list.get(i);
                list.set(i, list.get(j));
                list.set(j, swap);
            }
        }
    }
}
