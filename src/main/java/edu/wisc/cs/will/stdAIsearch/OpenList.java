package edu.wisc.cs.will.stdAIsearch;

import java.util.Iterator;
import java.util.LinkedList;
import edu.wisc.cs.will.Utils.Utils;

/*
 * Keep an ordered list of search nodes being considered.
 * Method for inserting new items depends on the search strategy being used.
 * @author shavlik
 *
 */
public class OpenList<T extends SearchNode> extends LinkedList<T> {

    private static final long serialVersionUID = 1L;

    public StateBasedSearchTask task;

    private int countOfAdds = 0;

    public OpenList(StateBasedSearchTask task) {
        this.task = task;
        if (task.verbosity > 1) {
            Utils.println("Starting a search with strategy = " + task.strategy.getClass().getName() + ".");
        }
    }

    private void recordNodeCreation(T node) {
        task.nodesCreated++;
        task.nodesCreatedThisIteration++;
        task.searchMonitor.recordNodeCreation();
        if (task.closed != null && task.addNodesToClosedListWhenCreated) {
            task.closed.addNodeToClosed(node);
        }
    }

    public T popOpenList() {
        T popped = pop();

        task.nodesConsidered++;
        task.nodesConsideredThisIteration++;
        task.searchMonitor.recordNodeExpansion();
        if (task.verbosity > 1) {
            Utils.println("Popped '" + popped + "' (" + Utils.comma(task.nodesConsidered) + " nodes considered so far) from the OPEN list.");
        }
        return popped;
    }

    @Override
    public boolean add(T node) {
        throw new UnsupportedOperationException("Programmer error: Do not use add() to add to the open list.  Use a method that also informs the search monitor.");
    }

    public void addToEndOfOpenList(T node) {
        if (node == null) {
            Utils.error("Cannot have node=null!");
        }
        if (task.closed != null && task.closed.alreadyInClosedList(node)) {
            return;
        }
        super.add(node);
        recordNodeCreation(node);

        if (task.verbosity > 2) {
            Utils.println("  Added " + node + " (node #" + Utils.comma(task.nodesCreated) + ") to the end of the OPEN list.");
        }
        if (task.beamWidth > 0) {
            checkBeamWidth();
        }
    }

    public void addToFrontOfOpenList(T node) {
        if (node == null) {
            Utils.error("Cannot have node=null!");
        }
        if (task.closed != null && task.closed.alreadyInClosedList(node)) {
            return;
        }
        super.add(0, node);
        recordNodeCreation(node);

        if (task.verbosity > 2) {
            Utils.println("  Added " + node + " (node #" + Utils.comma(task.nodesCreated) + ") to the front of the OPEN list.");
        }
        if (task.beamWidth > 0) {
            checkBeamWidth();
        }
    }

    private void insertByScoreIntoOpenList(T node, double minAcceptableScore, boolean tiesOK) throws SearchInterrupted {
        // HIGHER SCORES ARE BETTER (since that is the convention in heuristic search).
        if (node == null) {
            Utils.error("Cannot have node=null!");
        }
        if (task.closed != null && task.closed.alreadyInClosedList(node)) {
            if (task.verbosity > 2) {
                Utils.println(" Already in closed: " + node);
            }
            return;
        }
        double score = task.scorer.scoreThisNode(node);
        if (task.verbosity > 2) {
            Utils.println(" insertByScoreIntoOpenList: Score of " + Utils.truncate(score, 3) + " for " + node);
        }
        if (score < minAcceptableScore) {
            if (task.verbosity > 2) {
                Utils.println("  Discard since score less than minAcceptableScore (" + minAcceptableScore + ").");
            }
            return;
        }
        if (!tiesOK && score <= minAcceptableScore) {
            if (task.verbosity > 2) {
                Utils.println("  Discard since score does not exceeed minAcceptableScore (" + minAcceptableScore + ").");
            }
            return;
        }
        if (Double.isNaN(score)) {
            // Allow scorers to return NaN to indicate 'do not keep.'
            return;
        }

        // Used to play tricks when inserting into OPEN, but where the "real" score should be provided to the search monitor.
        double bonusScore = task.scorer.computeBonusScoreForThisNode(node);

        double totalScore = score + bonusScore;

        // See if this node is an acceptable for setting 'bestScoreSeenSoFar.'
        boolean acceptable = true;

        if (task.verbosity > 2) {
            Utils.println("Consider adding this to OPEN: [#" + (++countOfAdds) + "] " + node);
        }
        if (task.discardIfBestPossibleScoreOfNodeLessThanBestSeenSoFar &&
                task.scorer.computeMaxPossibleScore(node) <= task.bestScoreSeenSoFar) {
            // TODO(?): allow this to be '<=' or '<'
            if (task.verbosity > 2) {
                Utils.println("   Discard '" + node + "' because its best possible score (" + task.scorer.computeMaxPossibleScore(node) + ") cannot exceed the best score seen so far (" + task.bestScoreSeenSoFar + " of [" + task.nodeWithBestScore + "]).");
            }
            task.nodesNotAddedToOPENsinceMaxScoreTooLow++;
            return;
        }

        // Don't tell the monitor if pruned, since the monitor may want to compute something
        // cpu-intensive for a node that is being rejected.
        if (task.searchMonitor != null) {
            // TODO(?): also pass in the bonus so the monitor can see if if it wants.

            // Use 'real' score for the search monitor.
            acceptable = task.searchMonitor.recordNodeBeingScored(node, score);
        }

        if (acceptable && score > task.bestScoreSeenSoFar) {
            // TODO(?): allow '<' and '<=' the best score
            if (task.verbosity > 2) {
                Utils.println("NEW BEST SCORING (" + score + ") node: " + node);
            }
            // Do not use BONUS here, since that should only impact sorting in the list.
            task.bestScoreSeenSoFar = score;
            task.nodeWithBestScore = node;
            if (task.discardIfBestPossibleScoreOfNodeLessThanBestSeenSoFar) {
                // TODO(?): allow '<' and '<=' the best score.
                // Remove items from OPEN that cannot beat.
                for (Iterator<T> iter = this.iterator(); iter.hasNext();) {
                    T n = iter.next();
                    if (task.scorer.computeMaxPossibleScore(n) <= score) {
                        if (task.verbosity > 2) {
                            Utils.println("   Can remove this existing OPEN-list node since its best possible score (" + task.scorer.computeMaxPossibleScore(n) + ") cannot beat this new node's score (" + score + "): " + n);
                        }
                        iter.remove();
                        task.nodesRemovedFromOPENsinceMaxScoreNowTooLow++;
                    }
                    else if (task.verbosity > 2) {
                        Utils.println("   Keep in OPEN: " + n);
                    }
                }
            }
        }

        if (node.dontActuallyAddToOpen()) {
            if (task.verbosity > 2) {
                Utils.println("   Do NOT insert into OPEN: " + node);
            }
            return;
        }

        node.score = score;
        node.bonusScore = bonusScore;

        int position = 0;
        boolean found = false;
        boolean tiesInFront = task.inOpenListPutNewTiesInFront;
        for (SearchNode currentNode : this) {
            double currentTotalScore = currentNode.score + currentNode.bonusScore;
            if ((tiesInFront && totalScore >= currentTotalScore) || (!tiesInFront && totalScore > currentTotalScore)) {
                found = true;
                super.add(position, node);
                recordNodeCreation(node);
                if (task.verbosity > 2) {
                    Utils.println("  Added " + node + " (node #" + task.nodesCreated + ") to the OPEN list in position " + position + " based on its score of " + Utils.truncate(totalScore, 3) + ".");
                }
                break;
            }
            position++;
        }
        if (!found) {
            // Don't forget this might need to be the LAST item.
            super.add(node);
            recordNodeCreation(node);
            if (task.verbosity > 2) {
                Utils.println("  Added " + node + " (node #" + task.nodesCreated + ") to the END of the OPEN list (in position " + position + ") based on its score of " + Utils.truncate(totalScore, 3) + ".");
            }
        }

        if (task.beamWidth > 0) {
            checkBeamWidth();
        }
        if (task.verbosity > 3) {
            reportOpenListScores();
        }
    }

    public void insertByScoreIntoOpenList(T node) throws SearchInterrupted {
        this.insertByScoreIntoOpenList(node, task.minAcceptableScore, task.allowToTieMinAcceptableScore);
    }

    private void checkBeamWidth() {
        if (task.beamWidth > 0 && size() > task.beamWidth) {
            int excess = size() - task.beamWidth;

            if (task.verbosity > 2) {
                Utils.println("    Reducing OPEN to max beam size of " + task.beamWidth + ".");
            }
            for (int i = 0; i < excess; i++) {
                removeLast();
            }
        }
    }

    private void reportOpenListScores() {
        Utils.print("  OPEN = [");
        boolean firstTime = true;

        for (SearchNode currentNode : this) {
            double score = currentNode.score;

            if (firstTime) {
                firstTime = false;
            }
            else {
                Utils.print(", ");
            }
            Utils.print("score(" + currentNode + ") = " + score);
        }
        Utils.println("]");
    }
}
