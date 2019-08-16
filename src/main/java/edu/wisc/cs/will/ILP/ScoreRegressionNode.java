package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

public class ScoreRegressionNode extends ScoreSingleClauseByAccuracy {
	protected final static int debugLevel = 0;   // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).

	// Note we ADD penalties here, since the final score gets negated.
	private   final static double scalingPenalties = 0.1; // For regression we might want to shift the penalties since prediction errors might be smaller or larger
	private   final static double bonusForBridgers = 10000.0; // Seems this should suffice, though for some uses of regression it might not.  Don't want to lose the true score, since that'll help sort.
	private boolean forMLNs = false;

	public ScoreRegressionNode(boolean useMLNs) {
		super();
		forMLNs = useMLNs;
	}

	public double computeMaxPossibleScore(SearchNode nodeRaw) {
		SingleClauseNode node = (SingleClauseNode)nodeRaw;
		
		if (debugLevel > 1) { Utils.println("%     computeMaxPossibleScore = " + (-scalingPenalties * getPenalties(node, false, true)) + " for " + node); }
		// In best case, could end up with NO singleton variables.
		return -scalingPenalties * getPenalties(node, false, true);
	}
	
	public double scoreThisNode(SearchNode nodeRaw) throws SearchInterrupted {
		SingleClauseNode node  = (SingleClauseNode)nodeRaw;
		if (!Double.isNaN(node.score)) { return node.score; }
		double fit     = (forMLNs ? node.regressionFitForMLNs() : node.regressionFit());
		double penalty = scalingPenalties * (getPenalties(node, true, true));

		// Add small penalties as a function of length and the number of singleton variables
		// (so shorter better if accuracy the same).
		double score = fit + penalty;
		Utils.println("%     Score = " + Utils.truncate(-score, 6) + " (regressionFit = " + Utils.truncate(fit, 6) + ", penalties=" + penalty + ") for clause:  " + node);

		node.score = -score;
		if (score < 0) { Utils.error("Should not have a negative score: " + Utils.truncate(-score, 6) + " (regressionFit = " + Utils.truncate(fit, 6) + ", penalties=" + penalty + ") for clause:  " + node); }
		return -score; // Since the code MAXIMIZES, negate here.
	}
	
	public double computeBonusScoreForThisNode(SearchNode nodeRaw) throws SearchInterrupted { // ADD this to the normal score.
		// If a clause ends with a DETERMINATE literal, we want to allow it to be expanded
		// since the determinate literal by itself is (usually) of no help.
		SingleClauseNode node  = (SingleClauseNode)nodeRaw; 
		if (node.endsWithBridgerLiteral()) {
			if (debugLevel > 1) { Utils.waitHere("COMPUTE BRIDGER BONUS (" + Utils.truncate(bonusForBridgers, 3) + "): " + node); }
			return bonusForBridgers; 
		}
		return 0;
	}
}
