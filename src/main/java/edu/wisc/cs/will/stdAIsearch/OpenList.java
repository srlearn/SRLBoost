package edu.wisc.cs.will.stdAIsearch;

import edu.wisc.cs.will.Utils.Utils;

import java.util.LinkedList;

/*
 * Keep an ordered list of search nodes being considered.
 * Method for inserting new items depends on the search strategy being used.
 * @author shavlik
 *
 */
public class OpenList<T extends SearchNode> extends LinkedList<T> {

    private static final long serialVersionUID = 1L;

    private final StateBasedSearchTask task;

    public OpenList(StateBasedSearchTask task) {
        this.task = task;
    }

    private void recordNodeCreation(T node) {
        task.nodesCreated++;
        task.nodesCreatedThisIteration++;
        if (task.closed != null && task.addNodesToClosedListWhenCreated) {
            task.closed.addNodeToClosed(node);
        }
    }

    public T popOpenList() {
        T popped = pop();

        task.nodesConsidered++;
        task.nodesConsideredThisIteration++;
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
            return;
        }
        double score = task.scorer.scoreThisNode(node);
        if (score < minAcceptableScore) {
            return;
        }
        if (!tiesOK && score <= minAcceptableScore) {
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

        // Don't tell the monitor if pruned, since the monitor may want to compute something
        // cpu-intensive for a node that is being rejected.
        if (task.searchMonitor != null) {
            // TODO(?): also pass in the bonus so the monitor can see if if it wants.

            // Use 'real' score for the search monitor.
            acceptable = task.searchMonitor.recordNodeBeingScored(node, score);
        }

        if (acceptable && score > task.bestScoreSeenSoFar) {
            // TODO(?): allow '<' and '<=' the best score
            // Do not use BONUS here, since that should only impact sorting in the list.
            task.bestScoreSeenSoFar = score;
        }

        if (node.dontActuallyAddToOpen()) {
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
                break;
            }
            position++;
        }
        if (!found) {
            // Don't forget this might need to be the LAST item.
            super.add(node);
            recordNodeCreation(node);
        }

        if (task.beamWidth > 0) {
            checkBeamWidth();
        }
        if (task.verbosity > 3) {
            // TODO(@hayesall): `reportOpenListScores` is the only thing that may need `task.verbosity`
            reportOpenListScores();
        }
    }

    public void insertByScoreIntoOpenList(T node) throws SearchInterrupted {
        this.insertByScoreIntoOpenList(node, task.minAcceptableScore, task.allowToTieMinAcceptableScore);
    }

    private void checkBeamWidth() {
        if (task.beamWidth > 0 && size() > task.beamWidth) {
            int excess = size() - task.beamWidth;
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
