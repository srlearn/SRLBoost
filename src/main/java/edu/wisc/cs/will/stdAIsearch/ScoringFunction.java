package edu.wisc.cs.will.stdAIsearch;

import edu.wisc.cs.will.Utils.Utils;

/*
 * @author shavlik
 */
public abstract class ScoringFunction {

	protected ScoringFunction() {}

	public void setSearchTask(StateBasedSearchTask task) {
	}

	public abstract double scoreThisNode(SearchNode node) throws SearchInterrupted;

	public double computeMaxPossibleScore(SearchNode node) throws SearchInterrupted {
		// THESE ARE HERE TO TRAP SOME ODD BEHAVIOR ThAT POPPED UP ONCE WITH ILP SEARCH.  Can delete later (current date = 7/31/08).
		Utils.waitHere("Wrong computeMaxPossibleScore?");
		Utils.error("Shouldn't happen?");
		return Double.POSITIVE_INFINITY;
	}

	public double computeBonusScoreForThisNode(SearchNode node) throws SearchInterrupted {
		// ADD this to the normal score.
		Utils.waitHere("Wrong computeBonusScoreForThisNode?");
		Utils.error("Shouldn't happen?");
		// Might want to override the regular score to play tricks with insertion into OPEN (eg, used in ILP code).
		return 0;
	}
	
	public void clearAnySavedInformation() {
		// Don't make this abstract since it is unlikely that a scoring function will have something that needs resetting.
	}
}
