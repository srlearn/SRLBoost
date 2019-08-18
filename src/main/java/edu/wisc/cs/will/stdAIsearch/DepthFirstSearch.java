package edu.wisc.cs.will.stdAIsearch;

import java.util.List;

/*
 * Implements a depth-first search.
 * 
 * @author shavlik
 */
public class DepthFirstSearch extends SearchStrategy {

    public DepthFirstSearch() {}

    /*
     * Adds the children to the front of the open list so that the search
     * proceeds depth-first.
     * 
     * @see edu.wisc.cs.will.stdAIsearch.SearchStrategy#addChildrenToOpenList(edu.wisc.cs.will.stdAIsearch.OpenList,
     *      java.util.List)
     */
    public <T extends SearchNode> void addChildrenToOpenList(OpenList<T> open, List<T> children) {

        // Could use addAll, which would maintain order, but by adding one at a time,
        // the addToOpenList can watch what is happening.  So to maintain "left-to-right" order in OPEN,
        // need to reverse.

        // For depth-first search, add new nodes to FRONT of list.  Be sure to maintain order of the children.
        if (children != null) for (int i = children.size() - 1; i >= 0; i-- ) {
            open.addToFrontOfOpenList(children.get(i));
        }
    }

    public String toString() {
        return "depth-first search";
    }
}
