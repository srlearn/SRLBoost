package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/*
 * @author shavlik
 */
public class ScoreSingleClauseByAccuracy extends ScoreSingleClause {

	private final Set<PredicateName> pNamesSeen = new HashSet<>(32);
	
	ScoreSingleClauseByAccuracy() {
	}
	
	double getPenalties(SingleClauseNode node, boolean includeSingletonCount) {
		List<Variable> allVariables = node.collectAllVariables();
		List<Constant> allConstants = node.collectAllConstants();
		pNamesSeen.clear();
		double bodyCost        =                              node.getCost();
		double singletonVars   = (includeSingletonCount     ? node.countOfSingletonVars(allVariables)      : 0.0);
		double repeatedLits    = (node.discountForRepeatedLiterals(pNamesSeen));
		double uniqueVars      =                              node.countOfUniqueVars(     allVariables);
		double uniqueConstants =                              node.countOfUniqueConstants(allConstants);
		double multiplierForUniqueConstants = 0.0000002;
		double multiplierForUniqueVars = 0.0000001;
		double multiplierForSingletonVars = 0.0000010;

		/*
		 * There are some 'tie-breaking' things that adjust accuracy a little.
		 *   That is predicate names have costs, they are used to adjust the accuracy.
		 *   Also, there is a small penalty for each variable that only appears once.
		 *   Finally, there is a penalty for the number of unique variables there are.
		 */
		// This gets NEGATED below, i.e. this should be a POS number and it is a PENALTY.
		double multiplerForBodyCost = 0.0000100;
				
		return                              multiplerForBodyCost * bodyCost
			 + (includeSingletonCount     ? multiplierForSingletonVars * singletonVars : 0.0)
			 - (multiplerForBodyCost * repeatedLits)
			 +                              multiplierForUniqueVars * uniqueVars
			 +                              multiplierForUniqueConstants * uniqueConstants;
	}

	public double computeMaxPossibleScore(SearchNode nodeRaw) throws SearchInterrupted {
		SingleClauseNode node  = (SingleClauseNode)nodeRaw;
		return node.maxPrecision() - getPenalties(node, false); // In best case, could end up with NO singleton variables.
	}
	
	public double scoreThisNode(SearchNode nodeRaw) throws SearchInterrupted {
		SingleClauseNode node  = (SingleClauseNode)nodeRaw;
		if (!Double.isNaN(node.score)) { return node.score; }
		double           score = node.precision() - getPenalties(node, true); // Add small penalties as a function of length and the number of singleton vars (so shorter better if accuracy the same).
		node.score = score;
		return score;
	}

}
