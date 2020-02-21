package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.stdAIsearch.ScoringFunction;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

/*
 * @author shavlik
 */
public abstract class ScoreSingleClause extends ScoringFunction {

	ScoreSingleClause() {}

	public double computeBonusScoreForThisNode(SearchNode nodeRaw) throws SearchInterrupted { // ADD this to the normal score.
		// If a clause ends with a DETERMINATE literal, we want to allow it to be expanded
		// since the determinate literal by itself is of no help.
		SingleClauseNode node  = (SingleClauseNode)nodeRaw;
		if (node.endsWithBridgerLiteral()) {
			return computeMaxPossibleScore(node) - scoreThisNode(node); // Since bonus is ADDED, need to subtract the normal score so that the computed score is the total score.
		}
		return 0;
	}

}
