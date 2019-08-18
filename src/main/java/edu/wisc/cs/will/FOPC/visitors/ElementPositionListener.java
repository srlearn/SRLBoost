package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.visitors.ElementPositionVisitor.ElementPositionData;

/*
 *
 * @author twalker
 */
public interface ElementPositionListener<T extends ElementPositionData> {

    /* Informs the listener that the element position is being visited.
     * @return True indicates the element position visitor should stop visiting.
     */
    boolean visiting(Sentence s, T data);
    
    /* Informs the listener that the element position is being visited.
     * @return True indicates the element position visitor should stop visiting.
     */
    boolean visiting(Term t, T data);
}
