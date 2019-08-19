package edu.wisc.cs.will.Boosting.Trees;

import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.NumberGroundingsCalculator;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/*
 * @author tkhot
 */
public class RegressionMLNModel extends RegressionTree {

	private NumberGroundingsCalculator calc;
	
	private Map<String, Long> cachedRegressionClauseWeights = null; 

	public RegressionMLNModel(WILLSetup setup) {
		super(setup);
		resetGroundingCalculator();
	}
	
	public void setCachedValues(Map<String, Long> cache) {
		cachedRegressionClauseWeights = cache;
	}
	
	private void addToCache(Clause cl, Literal eg, long val) {
		if (cachedRegressionClauseWeights == null) {
			return;
		}
		String key = getCacheKey(cl, eg);
		cachedRegressionClauseWeights.put(key, val);
	}

	private String getCacheKey(Clause cl, Literal eg) {
		return cl.toString() + ":::" + eg.toString();
	}

	private boolean inCache(Clause cl, Literal eg) {
		if (cachedRegressionClauseWeights == null) {
			return false;
		}
		String key = getCacheKey(cl, eg);
		return cachedRegressionClauseWeights.containsKey(key);
	}

	private long cachedWeight(Clause cl, Literal eg) {
		if (cachedRegressionClauseWeights == null) {
			Utils.error("No cache provided");
		}
		String key = getCacheKey(cl, eg);
		return cachedRegressionClauseWeights.get(key);
	}

	@Override
	public void setSetup(WILLSetup setup) {
		super.setSetup(setup);
		resetGroundingCalculator();
	}
	
	private void resetGroundingCalculator() {
		calc = new NumberGroundingsCalculator(setup.getContext());
	}

	@Override
	protected RegressionValueOrVector getRegressionClauseWt(Clause clause, Example ex) {
		
		if (clause.getPositiveLiterals().size() != 1) {
			Utils.error("Expected horn clause: " + clause);
		}
		Literal head = clause.getPosLiteral(0).copy(false);
		Term y = head.getArgument(head.numberArgs() - 1);
		RegressionValueOrVector val = BoostingUtils.getRegressionValueOrVectorFromTerm(y);
		head.removeArgument(y);
		List<Literal> new_head = new ArrayList<>();
		new_head.add(head);
		
		List<Literal> new_body = clause.getDefiniteClauseBody();
		// remove the cut to get number of proofs
		if (new_body.size() > 0 &&
			new_body.get(new_body.size()-1).equals(setup.getHandler().cutLiteral)) {
			new_body.remove(new_body.size() - 1);
		}
		Clause cl = new Clause(setup.getHandler(), new_head, new_body);
		// Ignore the negation by failure literals as the ordering takes care
		if (calc.isOnlyInHead(cl, ex)) {
			for (int i = 0; i < new_body.size(); i++) {
				Literal lit = new_body.get(i);
				if(lit.predicateName.equals(setup.getHandler().standardPredicateNames.negationByFailure)) {
					new_body.remove(i);
					i--;
				}
			}
			if (!setup.learnClauses) {
				setBreakAfterFirstMatch(true);
			}
		} else {
			setBreakAfterFirstMatch(false);
		}

		
		cl = new Clause(setup.getHandler(), new_head, new_body);
		long num;
		if (inCache(cl, ex)) {
			num=cachedWeight(cl, ex);
		} else {
			num = calc.countNumberOfNonTrivialGroundings(cl, ex);
			addToCache(cl, ex, num);
		}
		// If the clause head unifies with the example and it has no groundings, we want to evaluate the next
		// clause. So return Nan. If the example doesn't unify with the head, then it doesn't matter if we return 0 or Nan, 
		// as both will not have any impact on final regression value.
		if (num ==0) {
			return null;
		} 
		val.multiply(num);
		return val;

	}
}
