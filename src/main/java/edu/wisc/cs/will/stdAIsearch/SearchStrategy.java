package edu.wisc.cs.will.stdAIsearch;

import java.util.List;

/*
 * A place-holder superclass for different types of searches.
 * 
 * @author shavlik
 */
public abstract class SearchStrategy {
    /*
     * The specification for a state-based search task.
     */
    StateBasedSearchTask task;

    SearchStrategy() {}

    void setSearchTask(StateBasedSearchTask task) {
        this.task = task;
    }

    /*
     * Adds more states to the open list of states.
     * 
     * @param open The open list of states waiting to be examined.
     * @param children The states to add to the open list.
     * @throws SearchInterrupted If the search is interrupted.
     */
    public abstract <T extends SearchNode> void addChildrenToOpenList(OpenList<T> open, List<T> children) throws SearchInterrupted;

}
