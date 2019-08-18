package edu.wisc.cs.will.Boosting.RDN;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.List;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ILP.Precompute;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;

class BoostingPrecomputeManager {

	private WILLSetup setup;

	BoostingPrecomputeManager(WILLSetup setup) {
		this.setup = setup;
	}

	void recomputeFactsFor(PredicateName pName) {
		Precompute precomputer = new Precompute();
		Precompute.alwaysRecreatePrecomputeFiles = true;
		FileParser parser = setup.getInnerLooper().getParser();
		for (int i = 0; i < parser.getNumberOfPrecomputeFiles(); i++) {

			// Note that this is the set of ALL pre-computes encountered during any file reading.
			List<Sentence> precomputeThese = parser.getSentencesToPrecompute(i);
			precomputeThese = filterSentencesWithHead(precomputeThese, pName);
			if (Utils.getSizeSafely(precomputeThese) > 0) {
				String precomputeFileNameToUse = "recomputed" + Utils.defaultFileExtensionWithPeriod;

				// The method below will check if the precompute file already exists, and if so, will simply return unless overwritten.
				precomputer.processPrecomputeSpecifications(true,
						setup.getContext().getClausebase(),
						precomputeThese, precomputeFileNameToUse);
				addToFacts(precomputeFileNameToUse); // Load the precomputed file.
			}
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

	private List<Sentence> readFacts(Reader factsReader, String readerDirectory) {
		if (factsReader == null) {
			return null;
		}
		List<Sentence> sentences;
		// TODO(?): should get the DIR of the facts file.
		sentences = setup.getInnerLooper().getParser().readFOPCreader(factsReader, readerDirectory);
		if (sentences == null) {
			Utils.error("There are no facts in: " + factsReader);
		}
		return sentences;
	}

	private void addToFacts(String factsFileName) {
		try {
			File factsFile = Utils.ensureDirExists(factsFileName);
			addToFacts(new CondorFileReader(factsFile), factsFile.getParent());
		} catch (FileNotFoundException e) {
			Utils.reportStackTrace(e);
			Utils.error("Cannot find this file: " + factsFileName);
		}
	}

	private void addToFacts(Reader factsReader, String readerDirectory) {
		List<Sentence> moreFacts = readFacts(factsReader, readerDirectory);
		if (moreFacts == null) {
			return;
		}
		addFacts(moreFacts);
	}

	private void addFacts(List<Sentence> newFacts) {
		setup.getContext().assertSentences(newFacts);
	}
}
