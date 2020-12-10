package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;

/*
 * @author shavlik
 *
 *  An entry in a Gleaner.
 */
class SavedClause implements Serializable {
	private static final long serialVersionUID = -6726298393028248864L;
	double recall;
	double F1;
	double score;

	SavedClause(SingleClauseNode clause) {
		// Holds a string that will be printed when the clause is dumped.
		// Annotation about what created this clause.

		// TODO(@hayesall): Nothing in this constructor appears to actually be used in the code base.

		try {
			clause.precision();
			recall      = clause.recall();
			F1          = clause.F(1);
			score       = clause.score;
			clause.getUptoKmissedPositiveExamples();
			clause.getUptoKcoveredNegativeExamples();
		} catch (Exception e) {
			Utils.reportStackTrace(e);
			Utils.error();
		}
	}
}
