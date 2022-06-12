package edu.wisc.cs.will.Boosting.Utils;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.ResThmProver.InitHornProofSpace;
import edu.wisc.cs.will.ResThmProver.ProofDone;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchResult;

import java.util.*;

/*
 * @author tkhot
 */
public class NumberGroundingsCalculator {

	private final Unifier unifier;
	private final HornClauseProver groundings_prover;
	private final HornClauseContext context;
	private final boolean disableTrivialGndgs = false;

	public NumberGroundingsCalculator(HornClauseContext context) {
		this.context = context;
		unifier = context.getUnifier();
		groundings_prover = new HornClauseProver(context, true);
		
	}
	
	public long countNumberOfNonTrivialGroundings(Clause cl, Literal eg) {
		
		if (isOnlyInHead(cl, eg)) {
			BindingList theta = unifier.unify(cl.getDefiniteClauseHead(), eg.extractLiteral());
			Clause unifiedClause = cl.applyTheta(theta);
			List<Literal> posLits = new ArrayList<>();
			if (disableTrivialGndgs) {
				posLits.add(unifiedClause.getDefiniteClauseHead());
				context.getClausebase().assertFact(eg.extractLiteral());
				long n1 = countGroundingsForConjunction(unifiedClause.negLiterals, posLits);
				
				context.getClausebase().retractAllClausesWithUnifyingBody(eg.extractLiteral());
				long n2 = countGroundingsForConjunction(unifiedClause.negLiterals, posLits);
				if (n2 < n1 || n1 != 0) {
					Utils.waitHere("Wrong num of groundings: " + n2 +":" + n1);
				}
				return n2 - n1;
			} else {
				return countGroundingsForConjunction(unifiedClause.negLiterals, posLits);
			}
		}
		return countNonTrivialGroundingsFromBody(cl,eg);
	}
	
	private long countNonTrivialGroundingsFromBody(Clause clause, Literal ex) {		
		int numberOfLiteralsUnifyingWithEx = 0;
		int numberOfLiteralsDependingOnEx  = 0;
		
		for (Literal negLit : clause.getNegativeLiterals()) {
			BindingList negtheta = context.getUnifier().unify(negLit, ex);
			if (negtheta != null) {
				numberOfLiteralsUnifyingWithEx++;
			}
			if (isLiteralDependentOnEg(negLit, ex)) {
				numberOfLiteralsDependingOnEx++;
			}
		}
		if (numberOfLiteralsUnifyingWithEx == 0 && numberOfLiteralsDependingOnEx == 0) {
			return 0;
		}

		if (numberOfLiteralsDependingOnEx == 1) {
			// check if the clause can be simplified
			Clause newClause = new Clause(context.getStringHandler(), new ArrayList<>(), new ArrayList<>());
			if (replaceNegationByFailureByNots(clause, newClause, ex)) {
				return countSingleLiteralInBody(newClause, ex);
			}
		}
		if (numberOfLiteralsUnifyingWithEx > 1 || numberOfLiteralsDependingOnEx > 0) {
			Utils.error("Can't find groundings for clause:" + clause + " and " + ex);
		}
		System.currentTimeMillis();
		long val = countSingleLiteralInBody(clause, ex);
		System.currentTimeMillis();
		return val;
		
	}
	
	private boolean replaceNegationByFailureByNots(Clause clause,
												   Clause newClause,
												   Literal ex) {
		
		List<Literal> posLits = new ArrayList<>(clause.posLiterals);
		List<Literal> negLits = new ArrayList<>();
		boolean foundUnifyingLiteral = false;
		Collection<Variable> seenVariables = new HashSet<>();
		for (Literal posLit: clause.posLiterals) {
			seenVariables.addAll(posLit.collectFreeVariables(seenVariables));
		}
		for (Literal negLit : clause.negLiterals) {
			
			// Check if this is \+
			if (negLit.predicateName.equals(context.getStringHandler().standardPredicateNames.negationByFailure)) {
				Clause nbfContents = context.getStringHandler().getNegationByFailureContents(negLit);
				boolean thisNegFailContainsEx = false;
			    boolean foundExtraVars 		  = false;
				for (Literal newLit : nbfContents.posLiterals) {
					Collection<Variable> newVars = newLit.collectFreeVariables(seenVariables);
					
					if (newVars.size() > 0) {
						foundExtraVars = true;
					}
					if (newLit.getPredicateNameAndArity().equals(ex.getPredicateNameAndArity())) {
						thisNegFailContainsEx = true;
						if (foundExtraVars) {
							return false;
						}
					}
				}
				if (thisNegFailContainsEx) {
					if (foundUnifyingLiteral) {
						Utils.waitHere("found multiple literals matching example:" + ex + " in " + clause);
					} else {
						foundUnifyingLiteral = true;
					}
					if (foundExtraVars) {
						return false;
					} else {
						posLits.addAll(nbfContents.posLiterals);
					}
				}
				
			} else {
				negLits.add(negLit);
			}
		}
		if (!foundUnifyingLiteral) {
			Utils.println("Dependent literal not one level deep.");
			return false;
		}
		newClause.posLiterals = posLits;
		newClause.negLiterals = negLits;
		return true;
	}

	private boolean isLiteralDependentOnEg(Literal negLit, Literal ex) {
		// Check if literal has some bk rule
		Iterable<Clause> bk = context.getClausebase().getPossibleMatchingBackgroundKnowledge(negLit, null);
		if (bk != null) {
			for (Clause cl : bk) {
				if (cl.negLiterals != null) {
					for (Literal lit : cl.negLiterals) {
						if (context.getUnifier().unify(lit, ex) != null) {
							return true;
						}
						Iterable<Clause> newBK = context.getClausebase().getPossibleMatchingBackgroundKnowledge(lit, null);
						if (newBK != null) {
							// There are multiple level of recursion. Assume there is some dependence
							Utils.println("Too many bk rules with: " + negLit);
							return true;
						}
					}
				}
			}
		}
		
		// Check if this is \+
		if (negLit.predicateName.equals(context.getStringHandler().standardPredicateNames.negationByFailure)) {
			Clause cl = context.getStringHandler().getNegationByFailureContents(negLit);
			if (cl.posLiterals != null) {
			for (Literal newLit : cl.posLiterals) {
				if (newLit.getPredicateNameAndArity().equals(ex.getPredicateNameAndArity())) {
					return true;
				}
				if (isLiteralDependentOnEg(newLit, ex)) {
					return true;
				}
			}
			}
		}
		return false;
	}

	private long countSingleLiteralInBody(Clause clause, Literal ex) {
		int index=-1;
		for (Literal negLit : clause.getNegativeLiterals()) {
			index++;
			BindingList negtheta = context.getUnifier().unify(negLit, ex);
			if (negtheta != null) {
				List<Literal> newPos = negtheta.applyTheta(clause.getPositiveLiterals());
				List<Literal> newNeg = negtheta.applyTheta(clause.getNegativeLiterals());
				// Ignore the unified literal
				newNeg.remove(index);
				return -countGroundingsForConjunction(newNeg, newPos);
			}
		}
		index=-1;
		for (Literal posLit : clause.getPositiveLiterals()) {
			index++;
			BindingList postheta = context.getUnifier().unify(posLit, ex);
			if (postheta != null) {
				List<Literal> newPos = postheta.applyTheta(clause.getPositiveLiterals());
				List<Literal> newNeg = postheta.applyTheta(clause.getNegativeLiterals());
				// Ignore the unified literal
				newPos.remove(index);
				return countGroundingsForConjunction(newNeg, newPos);
			}
		}
		Utils.error("Didn't find any literal in Clause:" + clause + " to unify with " + ex);
		return 0;
	}

	private long countGroundingsForConjunction(List<Literal> posLiterals,
											   List<Literal> negLiterals) {
		return countGroundingsForConjunction(posLiterals, negLiterals, null);
	}

	/*
	 * Count the groundings of conjunction over posLiterals and ~negLiterals. 
	 * e.g. posLiterals=p(x),q(x) and negLiterals=r(x),s(x)
	 * returns count of groundings of p(x)^q(x)^~r(x)^~s(x)
	 */
	public long countGroundingsForConjunction(List<Literal> posLiterals,
										      List<Literal> negLiterals,
										      Set<BindingList> blSet) {
		List<Literal> newPosLits = new ArrayList<>();
		List<Literal> newNegLits = new ArrayList<>();
		if (disableTrivialGndgs) {
			newPosLits.addAll(posLiterals);
			newNegLits.addAll(negLiterals);
		} else {
			if (!filterLiteralsWithNoVariables(posLiterals, negLiterals, newPosLits, newNegLits)) {
				return 0;
			}
		}
		if (newPosLits.isEmpty() && newNegLits.isEmpty()) {
			if (blSet != null) {
				blSet.add(new BindingList());
			}
			return 1;
		}
		
		return countGroundingsForConjunctionUsingProver(newPosLits, newNegLits);
	}
	
	
	/*
	 * @return true if all filtered positive literals are in fact base and all negative literals are not.
	 */
	private boolean filterLiteralsWithNoVariables(List<Literal> posLiterals, List<Literal> negLiterals,
												  List<Literal> newPosLits,  List<Literal> newNegLits) {
		// Do a basic check for literals with no variables
		for (Literal lit : posLiterals) {
			if (canLookupLiteral(lit)) {
				if (!isaFact(lit)) {
					return false;
				}
			} else {
				newPosLits.add(lit);
			}
		}
		for (Literal lit : negLiterals) {
			if (canLookupLiteral(lit)) {
				if (isaFact(lit)) {
					return false;
				}
			} else {
				newNegLits.add(lit);
			}
		}
		return true;
	}
	
	/*
	 * Returns true if lit can be found in the factbase(ie it has no variables and doesn't have to be proved)
	 */
	public boolean canLookupLiteral(Literal lit) {
		return context.getClausebase().getPossibleMatchingBackgroundKnowledge(lit, null) == null &&
				!lit.containsVariables();
	}
	
	public boolean isaFact(Literal lit) {
		Iterable<Literal> facts = context.getClausebase().getPossibleMatchingFacts(lit, null);
		return (facts != null && facts.iterator().hasNext());
	}

	/*
	 * Count the groundings of conjunction over posLiterals and ~negLiterals.
	 * e.g. posLiterals=p(x),q(x) and negLiterals=r(x),s(x)
	 * returns count of groundings of p(x)^q(x)^~r(x)^~s(x)
	 */
	private long countGroundingsForConjunctionUsingProver(List<Literal> posLiterals,
														  List<Literal> negLiterals) {

		List<Literal> sortedPos = posLiterals;
		if (!disableTrivialGndgs) {
			sortedPos = sortByVariables(posLiterals);
		}
		((InitHornProofSpace) groundings_prover.initializer).loadNegatedConjunctiveQuery(sortedPos,
					groundings_prover.open);
		        
		BindingList bl = getNextProof(groundings_prover);
		long counter = 0;
		while(bl != null) {
			
			
			 Collection<BindingList> negBLs = new ArrayList<>();
			 negBLs.add(bl);
				
			for (Literal lit : negLiterals) {
				negBLs = expandNegativeLiteralBindingList(lit, negBLs); 
			}
			counter+= negBLs.size();

			bl = getNextProof(groundings_prover);
		}

		return counter;

	}
	
	private List<Literal> sortByVariables(List<Literal> posLits) {
		if (posLits.size() <= 1) {
			return posLits;
		}
		List<Literal> result = new ArrayList<>();
		List<Literal> copy = new ArrayList<>(posLits);
		
		Collection<Variable> seenVars = new HashSet<>();
		for (int i = 0; i < posLits.size(); i++) {
			int minVars = Integer.MAX_VALUE;
			Literal bestLit = null;
			for (Literal lit : copy) {
				int var = lit.collectFreeVariables(seenVars).size();
				if (var < minVars) {
					minVars = var;
					bestLit = lit;
				}
			}
			if (bestLit == null) {
				Utils.error("Not possible");
			}
			result.add(bestLit);
			seenVars.addAll(bestLit.collectFreeVariables(seenVars));
			copy.remove(bestLit);
		}
		if (!copy.isEmpty() || result.size() != posLits.size()) {
			Utils.error("Lengths are wrong:" + copy.size() + ":" + result.size() +":"+ posLits.size());
		}
		return result;
	}

	private Collection<BindingList> expandNegativeLiteralBindingList(
			Literal lit, Collection<BindingList> negBLs) {
		Collection<BindingList> outBLs = new HashSet<>();
		for (BindingList bl : negBLs) {
			Literal newLit = lit.applyTheta(bl);
			Collection<BindingList> thisLitBL = getAllPossibleGroundingsOf(newLit);
			for (BindingList newBL : thisLitBL) {
				Literal groundedLit = newLit.applyTheta(newBL);
				// If not in fact base, consider this BL
				if (context.getClausebase().getPossibleMatchingFacts(groundedLit, null) == null ||
					!context.getClausebase().getPossibleMatchingFacts(groundedLit, null).iterator().hasNext()) {
					BindingList addBL = new BindingList(newBL.collectBindingsInList());
					addBL.addBindings(bl);
					outBLs.add(addBL);
				}
			}
		}
		return outBLs;
		
	}
	
	private List<BindingList> getAllPossibleGroundingsOf(Literal lit) {
		PredicateName pName = lit.predicateName;
		int index=-1;
		List<Collection<Term>> rangeForArguments = new ArrayList<>();
		List<Term> variableArguments = new ArrayList<>();
		List<BindingList> bindings = new ArrayList<>();
		for (Term arg : lit.getArguments()) {
			index++;
			if (!arg.isGrounded()) {
				if (!(arg instanceof Variable)) {
					Utils.error("expected variable here: " + arg + " in " + lit);
							
				}
				variableArguments.add(arg);
				rangeForArguments.add(new HashSet<>());
				int varIndex = rangeForArguments.size() - 1;
				// Look for all possible types that this arg can have
				for (PredicateSpec spec : pName.getTypeOnlyList()) {
					// Only if arity matches
					if (spec.getArity() == lit.getArity()) {
						Set<Term> consts = context.getStringHandler().isaHandler.getAllInstances(spec.getTypeSpec(index).isaType);
						rangeForArguments.get(varIndex).addAll(consts);
					}
				} 
				if (rangeForArguments.get(varIndex).size() == 0 ) {
					Utils.error("No constants for argument: " + arg + " in " + lit);
				}
			}
		}
		if (variableArguments.isEmpty()) {
			bindings.add(new BindingList());
			return bindings;
		}
		
		List<List<Term>> crossProd = Utils.computeCrossProduct(rangeForArguments);
		
		for (List<Term> oneGrounding : crossProd) {
			BindingList bl = new BindingList();
			for (int i = 0; i < oneGrounding.size(); i++) {
				bl.addBinding((Variable)variableArguments.get(i), oneGrounding.get(i));
			}
			bindings.add(bl);
		}
		return bindings;
	}

	private BindingList getNextProof(HornClauseProver prover2) {
		SearchResult result = null;
		try {
			result = prover2.performSearch();
		} catch (SearchInterrupted e) {
			e.printStackTrace();
		}
        if (result.goalFound()) {
        	return new BindingList(((ProofDone) prover2.terminator).collectQueryBindings());
        }
        return null;
	}

	public boolean isOnlyInHead(Clause cl, Literal eg) {
		Literal head = cl.getDefiniteClauseHead();
		boolean isInHead = head.getPredicateNameAndArity().equals(eg.getPredicateNameAndArity());

		for (Literal body : cl.negLiterals) {
			if (body.getPredicateNameAndArity().equals(eg.getPredicateNameAndArity())) {
				isInHead = false;
				break;
			}
		}
		
		return isInHead;
	}
}
