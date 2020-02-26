package edu.wisc.cs.will.Boosting.Trees;

import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.Utils.Utils;

/*
 * @author Tushar Khot
 */
public class LearnRegressionTree {

	private final WILLSetup setup;
	
	public LearnRegressionTree(WILLSetup setup) {
		this.setup = setup;
	}

	public RegressionTree parseTheory(Theory th) {
		RegressionTree tree;
		if (!setup.useMLNs) {
			tree = new RegressionTree(setup);
		} else {
			tree = new RegressionMLNModel(setup);
		}
		if (th.getClauses() == null) {
			Utils.error("No regular clauses!!!");
		}
		for (Clause cl : th.getClauses()) {
			if (cl == null)
				continue;
			tree.addClause(cl);
		}
		// Add supporting clauses to bk
		if(th.getSupportClauses() != null) {
			for (Clause cl : th.getSupportClauses()) {
				if (cl == null)
					continue;
				tree.addSupportingClause(cl);
				setup.getInnerLooper().getContext().getClausebase().assertBackgroundKnowledge(cl);
			}
		}
		return tree;
	}

}

