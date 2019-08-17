package edu.wisc.cs.will.MLN_Task;

import java.util.ArrayList;
import java.util.List;

import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This is the Block class. Exactly or at most k of the literals within a block
 * can be true. All the ground literals in a block are groundings of the same literal.
 * 
 * @author pavan and shavlik
 */
public class Block {
	private static final int debugLevel = 0;

	private List<GroundLiteral> gndLiterals;      // The ground literals in this block.
	private Literal                literal;       // All ground literals in block are groundings of this literal.

	// Exactly or at-most k of the ground literals in the block must be true.
	private int     k;
	private boolean exactly;

	private boolean groundClausesComputed;
		
	/**
	 * @param literal All ground literals in the block are groundings of this literal.
	 * @param gndLiterals The ground literals in the block. Assumes that it doesn't contain any evidence literals.
	 */
	Block(Literal literal, List<GroundLiteral> gndLiterals) {
		this(literal, gndLiterals, 0);
	}
	
	/**
	 * The constructor. All the gndLiterals and evidence information need not be supplied
	 * at the point of constructing the object. This information can be supplied later with
	 * addGndLiteral and addEvidence methods. However, all this information must be supplied
	 * before the initialization of truth values is done using initValues or setRandomValues 
	 * method. Either initValues or setRandomValues has to be explicitly called to bring the
	 * truth assignments in the block to a consistent state.
	 * 
	 * @param literal All ground literals in the block are groundings of this literal.
	 * @param gndLiterals The ground literals in the block. Assumes that it doesn't contain any evidence literals.
	 * @param numTrueEvidenceLiterals The number of positive evidence literals belonging to this block.
	 */
	private Block(Literal literal, List<GroundLiteral> gndLiterals, int numTrueEvidenceLiterals) {
		this.gndLiterals = gndLiterals;
		this.literal = literal;
		boolean isABlock = false;
		exactly = true;
		List<TypeSpec> typeSpecList = literal.predicateName.getTypeOnlyList(literal.numberArgs()).get(0).getTypeSpecList();
		for (TypeSpec typeSpec : typeSpecList) {
			if (typeSpec.truthCounts != 0) {
				isABlock = true;
				k = typeSpec.truthCounts;
				if (k < 0) {
					exactly = false;
					k = -k;
				}
			}
		}
		if (!isABlock) {
			Utils.printlnErr("Literal " + literal + " should not be used to instantiate a block object.");
		}
		groundClausesComputed = false;
		reduceK(numTrueEvidenceLiterals);
	}	
	
	private void initGndClauses() {
		if (debugLevel > 0) { Utils.println("*** Initializing list of ground clauses in " + literal + "'s block"); }
		// Set of all ground clauses in which the ground literals of this block appear.
		for (GroundLiteral gndLiteral : gndLiterals) {			
			for (GroundClause gndClause : gndLiteral.getGndClauseSet()) {
				if (debugLevel > 0) { Utils.println(gndClause.toString()); }
			}
		}
		if (debugLevel > 0) { Utils.println(""); }
	}

	public void init() {
		if (!groundClausesComputed) {
			initGndClauses();
			groundClausesComputed = true;
		}
	}

	/**
	 * @return The number of ground literals in the block.
	 */
	public int getSize() {
		return gndLiterals.size();
	}

	/**
	 * @return The index of gndLiteral in list of ground literals in this block.
	 */
	public int indexOf(GroundLiteral gndLiteral) {
		return gndLiterals.indexOf(gndLiteral);
	}

	/**
	 * @return true if this block is an 'exactly k true' type, and false if it is an 'atmost k true' type.
	 */
	public boolean isExactly() {
		return exactly;
	}

	/**
	 * @return The value of k in 'exactly/at-most k true literals'
	 */
	public int getK() {
		return k;
	}

	/**
	 * Each time a new true evidence literal belonging to this block is seen,
	 * this method can be called. Do not call this method twice for the same ground literal.
	 * Likewise, do not call this method for ground literals which were accounted for by 
	 * numTrueEvidenceLiterals argument in the constructor call.
	 */
	void addEvidence() {
		reduceK(1);
	}
	
	private void reduceK(int value) {
		if (value <= 0) return;
		k -= value;
		if (k <= 0) {
			for (GroundLiteral gndLiteral : gndLiterals) {
				gndLiteral.setValueOnly();
			}
			k = 0;
		}
	}

	/**
	 * Tries to add the gndLiteral to the block.
	 * @return true if the gndLiteral was added to the block.
	 */
	boolean addGndLiteral(GroundLiteral gndLiteral) {
		if (!canAddGndLiteral()) return false;
		if (gndLiterals == null) {
			gndLiterals = new ArrayList<>();
		}		
		gndLiterals.add(gndLiteral);
		return true;
	}
	
	/**
	 * A gndLiteral can be added to the block if it is a grounding of the same literal,
	 * and has the same constants (for those arguments with truthCounts = 0) as the current
	 * ground literals in the block.
	 *
	 * @return true/false indicating whether this gndLiteral must be added to this block or not.
	 */
	boolean canAddGndLiteral() {
		Utils.error("need to fix this code"); return false;
	}

}