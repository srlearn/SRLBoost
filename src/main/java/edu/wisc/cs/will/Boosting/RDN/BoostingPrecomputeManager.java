package edu.wisc.cs.will.Boosting.RDN;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ILP.Precompute;
import edu.wisc.cs.will.Utils.Utils;

import java.util.ArrayList;
import java.util.List;

class BoostingPrecomputeManager {

	private final WILLSetup setup;

	BoostingPrecomputeManager(WILLSetup setup) {
		this.setup = setup;
	}

	void recomputeFactsFor(PredicateName pName) {
		Precompute precomputer = new Precompute();
        FileParser parser = setup.getInnerLooper().getParser();
		for (int i = 0; i < 125; i++) {

			// Note that this is the set of ALL pre-computes encountered during any file reading.
			List<Sentence> precomputeThese = null;
			precomputeThese = filterSentencesWithHead(precomputeThese, pName);
		}
	}

	private List<Sentence> filterSentencesWithHead(List<Sentence> sentences,
												   PredicateName pName) {
		List<Sentence> acceptedSentences = new ArrayList<>();
		for (Sentence sentence : sentences) {
			List<Clause> clauses = sentence.convertToClausalForm();
			if (clauses == null) {
				continue;
			}
			// Take each clause
			for (Clause clause : clauses) {
				if (!clause.isDefiniteClause()) {
					Utils.error("Can only precompute Horn ('definite' actually) clauses.  You provided: '" + sentence + "'.");
				}

				PredicateName headPredName = clause.posLiterals.get(0).predicateName;
				// This clause should be precomputed
				if (headPredName.equals(pName)) {
					acceptedSentences.add(sentence);
					break;
				}
			}

		}
		return acceptedSentences;
	}

}
