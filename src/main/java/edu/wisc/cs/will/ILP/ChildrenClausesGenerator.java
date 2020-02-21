package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.ChildrenNodeGenerator;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

import java.util.*;

/*
 * @author shavlik
 * 
 * TODO(@jws) - if last literal is a BRIDGER than REQUIRE (unless flag set?) that a VAR NEW TO THE BRIDGER IS USED (else it isn't bridging).
 *
 */
public class ChildrenClausesGenerator extends ChildrenNodeGenerator {

	private   static final boolean reportPredicateUsage = true;
	private                int     callCounter          = 0;
	private   static final int     callCounterMOD       = 10000; // Every N predicate-usage counts, report predicate usage.

	private final Set<PredicateName>   predicatesMarked     = new HashSet<>(4); // TODO - add code to RESET.  But might not be necessary since not a large number of predicates.
	
	public    static final int       numberofConstantsToCreate = 100;
	private Map<Type,List<Term>>   newTypesPresentInChildMap; // I (JWS) don't know how in Java one can change (and recover) a passed-in argument, so I'll make it a 'global' instance variable.
	private List<Type>             newTypesPresentInChild;


	BindingList            cachedBindingListForPruning; // Used if any pruning is being considered.
	Clause                 numberedBodyForPruning;      // Also used when pruning.
	private   Map<PredicateName,List<Literal>> literalsTriedSoFar; // Used to check for variants in children (only newVars can vary).
	private StringConstant[]       constantsToUse    = null; // These are used to replace variables when matching for pruning.
	private   BindingList            dummyBindingList;         // Use this to save some new'ing.
	int                    countOfPruningDueToVariantChildren = 0;

	ChildrenClausesGenerator() {
	}
	
	void initialize() {
		literalsTriedSoFar     = new HashMap<>(64);
		constantsToUse         = new StringConstant[numberofConstantsToCreate];
		dummyBindingList       = new BindingList();
		boolean wasVarIndicatorSet = ((LearnOneClause) task).stringHandler.isVariableIndicatorSet(); // We would like the following to NOT become the default setting for VariableIndicator (i.e., if it is currently null).
		for (int i = 0; i < numberofConstantsToCreate; i++) { // Task is not yet assigned when instance created, so need an extra call.  Plus good to all a resetting of all instance variables.
			constantsToUse[i] = ((LearnOneClause) task).stringHandler.getStringConstant("WillConst" + (i + 1));  // Need something that is unlikely to also appear in a clause "of its own right."  Also, recall that these count from ONE.
		}
		if (!wasVarIndicatorSet) { ((LearnOneClause) task).stringHandler.setVariableIndicator(null); }
		countOfPruningDueToVariantChildren = 0;
	}

	private List<SearchNode>  children  = new ArrayList<>(8); // TODO - reuse this list which returns children.  This is called alot so don't want to make anew each time.



	// TODO(@hayesall): Too complex to analyze with data flow: major need of refactoring.
	public List<SearchNode> collectChildren(SearchNode nodeBeingExplored) throws SearchInterrupted {


		SingleClauseNode     parent         = (SingleClauseNode) nodeBeingExplored;
		children.clear();
		LearnOneClause       thisTask       = (LearnOneClause) task;
		Set<PredicateNameAndArity>   bodyModes      = thisTask.bodyModes;
		int                  parentBodyLen  = getParentBodyLength(parent, thisTask); // parent.bodyLength();

		// Note this uses the corrected body length for 'bridgers.'  (Not sure that this is being done consistently.)
		// HOWEVER IF A LITERAL ENDS WITH A *BRIDGER* IT IS ADDED (since it is added 'for free').
		// TODO(@jws) - handle maxFreeBridgersInBody (for now simply added if when sometimes it shouldnt be).
		boolean dontAddAnyChildToOpenButStillScoreThem = (parentBodyLen >= thisTask.maxBodyLength - 1); // If one step away from the max length, don't add children to open (but still score them) since they will be discarded when popped.

		// Cannot check this earlier, since could find a good clause using constraints on the head.
		if (Utils.getSizeSafely(bodyModes) < 1) { Utils.waitHere("There are no body modes for this task!"); return null; }
		// TODO(@jws) Some tests (eg, canImprove) for stopping we'll postpone until/if a node is popped from OPEN.  Also, some would require scoring early, though that is cached so no wasted cycles.
        if (parentBodyLen >= thisTask.maxBodyLength) {
            return null; // At max length for clauses.
        }
		// If true, save all the conjuncts created to the collectedConjuncts list.
		boolean collectAllConjuncts = false;
		if (!collectAllConjuncts && !parent.canImprove(thisTask)) {
			return null; // No need to continue if no negative examples are covered, for example (assuming the clause does not have other requirements, such as containing all the variables appearing in the head).
       }

        if (thisTask.performRRRsearch && thisTask.stillInRRRphase1) {
            // See if have completed the first phase of RRR.
            if (parentBodyLen >= thisTask.thisBodyLengthRRR) {
                thisTask.stillInRRRphase1 = false;
                thisTask.beamWidth = thisTask.savedBeamWidth; // When done with RRR's first phase, reset to the standard beam width.
            }
        }

		putParentClauseInFormForPruning(parent);

		Set<PredicateNameAndArity> eligibleBodyModes = applyModeContraints(bodyModes, parent);
		
		int  maxPossibleNewVars = thisTask.maxNumberOfNewVars - parent.numberOfNewVars;

		for (PredicateNameAndArity predicateNameAndArity : eligibleBodyModes) if (predicateNameAndArity.getPredicateName().getTypeList() != null) {       // Consider each known predicate.
            PredicateName predName = predicateNameAndArity.getPredicateName();
			for (PredicateSpec specs : predName.getTypeList()) if (specs != null && specs.isaILPmode()) { // Consider each known mode for this predicate that can be used during ILP.



				// For tree-structured tasks, at least always complete the root.
				// TODO(@jws): maybe we allow a MULTIPLIER (eg, 10x) on the time limit when a ROOT of a tree-structured task?
				if ( (parentBodyLen > 0 || !thisTask.isaTreeStructuredTask() || ((Gleaner) thisTask.searchMonitor).bestNode != null) && // Need to have found something acceptable before stopping.
						thisTask.isThereNotTimeLeft()) {
					Utils.printlnErr("% No time left, so abandoning ILP-node generation:\n  " + thisTask.explainTimeLeft()); thisTask.open.clear(); return null; 
				}


				int              arity = Utils.getSizeSafely(specs.getSignature());
				int countOfOccurrences = parent.countPredicateOccurrences(predName, arity);  // Note that this recorded also as a function of the arity (essentially p/1 and p/2, i.e., p(x) and p(x,y), are two different predicates).
				Integer        predMax = predName.getMaxOccurrences(arity);
				if (predMax == null) {
					Utils.error("No preMax for predName=" + predName + " arity=" + arity + " typeList=" + predName.getTypeList());
				}
				int           maxToUse = (predMax != null || predMax == Integer.MAX_VALUE ? predMax : thisTask.maxPredOccurrences); // If not set to a finite number for this predicate/arity, use the "global" default.  TODO should we take the MAX of these two max's?  I.e., should the global be a default or an overall max?
				if (countOfOccurrences >= maxToUse) { continue; } // Have already used this predicate/arity the maximum number of times.
				boolean                   allNeededPredsFound = true;				
				List<List<Term>>          usableTerms         = new ArrayList<>(4);  // For each argument in this mode, need to collect ALL the terms that can fill it.
				Map<Variable,Type>        newVariables        = null;
				Set<Variable>             mustBeNewVariables  = null; // Need to sometimes treat these specially.
				Map<Type,List<Variable>>  newVarsThisType     = null;
				Map<Term,Type>            typesOfNewTerms     = null;
				Map<Term,Integer>         depthsOfTerms       = null;
				Map<Variable,Type>        typesOfNewConstants = null;  // We may need some variables that will need to be replaced by constants before this method is exited.

                if (reportPredicateUsage) {
                    predName.incrementConsideredCounter();
                    predicatesMarked.add(predName);
                    callCounter++;
                }
                
				if (specs.getTypeSpecList() != null) for (TypeSpec spec : specs.getTypeSpecList()) {               // Consider each argument in this mode.
					List<Term> validTermsOfThisType = new ArrayList<>(4); // Collect all the terms that can legally be used for this argument.
					// If a predicate is acceptable, need to hook into the old variables.
					//   If a +mode, then MUST hook into an old variable of same type, but what if several?  Do all possibilities.
					//   If a $mode, then MUST hook into an old variable that APPEARS ONLY ONCE EARLIER IN THE CLAUSE.  Again, do all such possibilities.
					//   If a -mode, then CAN hook into an old variable of same type, but that if several?  Again do all, as well as create a new variable. 
					//   If a ^mode, then treat SAME as '-' but ONLY create a new variable (and do NOT use other new variables of this type created for this literal).
					//   If a #mode, then use one of the selected positive SEEDs and find a constant of that type.
					//   If a @mode, then use the SPECIFIC value given (should be a constant and not a variable).
					//   If a &mode, then combine '-' and '#'.
					//   If a %mode, then combine '+' and '#'.
					if (spec.mustBeThisValue()) {
						Constant  typeSpecAsConstant = (Constant) ((LearnOneClause) task).stringHandler.getVariableOrConstant(spec.isaType.toString());
						Type typeOfThisSpecificValue = ((LearnOneClause) task).stringHandler.isaHandler.getIsaType(typeSpecAsConstant);
						
						if (typeOfThisSpecificValue == null) { Utils.error("Cannot find type of: '" + typeSpecAsConstant + "'."); }
						validTermsOfThisType.add(typeSpecAsConstant);
						if (typesOfNewTerms == null) { typesOfNewTerms = new HashMap<>(4); }
						Type assignedType = typesOfNewTerms.get(typeSpecAsConstant);
						if (assignedType == null) { typesOfNewTerms.put(typeSpecAsConstant, typeOfThisSpecificValue); }
						else if (assignedType != typeOfThisSpecificValue) { Utils.error("Have two types for '" + typeSpecAsConstant + "': " + assignedType + "' and '" + typeOfThisSpecificValue + "'."); }
						// No need to add to depthsOfTerms since constants have depth of the max depth of the input variables.
					} else if (spec.mustBeConstant()) {  // Grab some number of constants from the positive SEEDs.
						Variable newVarOfThisType = getNewILPbodyVar(spec); // We'll stick a variable in for now, then later find to what it gets bound.
						if (typesOfNewConstants == null) { typesOfNewConstants = new HashMap<>(4); }
						typesOfNewConstants.put(newVarOfThisType, spec.isaType);
						validTermsOfThisType.add(newVarOfThisType); // Just stick in the required type - below possible constants will be picked using the pos seeds.
						// No need to add to depthsOfTerms since constants have depth of the max depth of the input variables.
					} else {
						// Seemed easiest in terms of the logic to repeat the code above.
						if (spec.canBeConstant()) {
							Variable newVarOfThisType = getNewILPbodyVar(spec); // We'll stick a variable in for now, then later find to what it gets bound.
							if (typesOfNewConstants == null) { typesOfNewConstants = new HashMap<>(4); }
							typesOfNewConstants.put(newVarOfThisType, spec.isaType);
							validTermsOfThisType.add(newVarOfThisType); // Just stick in the required type - below possible constants will be picked using the positive seeds.
						}
						
						// Collect all of the variables and constants of this type in the current clause.
						List<Term> existingTermsOfThisType = getExistingTermsOfThisType(spec.isaType, parent); // We want objects UNDER this type (or OF this type).  E.g., if we're looking for an DOG, collect POODLEs, but *not* ANIMALs.
						if (existingTermsOfThisType != null) for (Term item : existingTermsOfThisType) {
							if (depthsOfTerms == null) { depthsOfTerms = new HashMap<>(4); }
							Integer oldDepth = depthsOfTerms.get(item);
							if (oldDepth == null) {
								Integer depthOfItem = parent.getDepthOfArgument(item);
								if (depthOfItem == null) { Utils.error("Cannot find the depth of argument: '" + item + "',  parent = " + parent); }
								depthsOfTerms.put(item, depthOfItem);
							}
						}

						List<Variable> listOfNewVarsThisType = null;
						if (!spec.mustBeBound() && !spec.mustBeNewVariable() && newVarsThisType != null) {
							// Look for new variables of this type already introduced for this mode.
							listOfNewVarsThisType = newVarsThisType.get(spec.isaType);
							if (listOfNewVarsThisType != null) { 
								for (Variable newVar : listOfNewVarsThisType) if (!validTermsOfThisType.contains(newVar)) { validTermsOfThisType.add(newVar); }
							}
						}

						// If this is an input variable, but nothing of that type is present, then this mode isn't eligible.
						// (TODO should CONSTANTS of a specific type be allowed?  Seems so.)
						if (spec.mustBeBound() && (existingTermsOfThisType == null || existingTermsOfThisType.size() < 1)) { 
							allNeededPredsFound = false;
							break;
						}
						// Collect all these legal terms.
						if (existingTermsOfThisType != null) { 
							if (spec.mustBeBoundAndAppearOnlyOnce()) {
								for (Term existing : existingTermsOfThisType) {
									if (parent.thisTermAppearsOnlyOnceInClause(existing)) { validTermsOfThisType.add(existing); }
								}
							} else if (!spec.mustBeNewVariable()) { // This must be a TOTALLY new variable (see about 10 lines above), i.e., cannot appear elsewhere in the predicate?  Seems so ... but need to DOC!
								for (Term existingTerm : existingTermsOfThisType) if (!validTermsOfThisType.contains(existingTerm)) { validTermsOfThisType.add(existingTerm); }
							}
						}
					
						// If this argument can be filled by a NEW argument (i.e., it is an "output" argument), then generate and collect such a variable.
						// Check if there is even room for ONE new variable.  Note: we also need to check again below because there might be room for one but not two new variables.
						if (parent.numberOfNewVars < thisTask.maxNumberOfNewVars && spec.canBeNewVariable()) { // Also create a new variable.
							Variable newVarOfThisType = getNewILPbodyVar(spec);
							
							// Store these newly created variables and their types.
							if (newVariables    == null) { newVariables = new HashMap<>(4); }
							newVariables.put(newVarOfThisType, spec.isaType);
							if (newVarsThisType == null) { newVarsThisType = new HashMap<>(4); }
							if (!spec.mustBeNewVariable()) { // Don't reuse this in the same literal (OK for later literals in the clause).
								if (listOfNewVarsThisType == null) { listOfNewVarsThisType = new ArrayList<>(1); }
								listOfNewVarsThisType.add(newVarOfThisType);
								newVarsThisType.put(spec.isaType, listOfNewVarsThisType);	
							} else {
								if (mustBeNewVariables == null) { mustBeNewVariables = new HashSet<>(4); }
								mustBeNewVariables.add(newVarOfThisType);
							}
							if (typesOfNewTerms == null) { typesOfNewTerms = new HashMap<>(4); } // These don't need to be very big since few new variables per literal.  Ie, allow 3 before rebuilding the hash map.
							typesOfNewTerms.put(newVarOfThisType, spec.isaType);
							validTermsOfThisType.add(newVarOfThisType);
						} else { 

							if (spec.mustBeNewVariable()) {
								usableTerms = null;
								break;		
							}
						}
					}
					// Since this is a notHeadVarMode, we should remove variables after collecting them all
					if (spec.mustNotBeHeadVar()) {
						List<Term> removeTheseVars = parent.getVariablesInTarget();
						validTermsOfThisType.removeAll(removeTheseVars);
					}
					
					
					usableTerms.add(validTermsOfThisType); // Remember what can be used to fill this argument.
				}
				if (usableTerms == null) { continue; }
				int totalNumberOfCandidates = 1;
				for (List<Term> terms : usableTerms) { totalNumberOfCandidates *= Utils.getSizeSafely(terms); }
				if (totalNumberOfCandidates < 1) {
					continue;
				}
				
				if (((LearnOneClause) task).getProver().getClausebase().isOnlyInFacts(predName, arity) && totalNumberOfCandidates > 100) { // See if some useful precomputing can be done.  Only applicable if in facts and not head of a rule, since that rule might require, say, that some arguments are non-variables (eg. number(X) might be in the body).
					// First see if this predicate is true enough times when all arguments are unique variables.
					List<Term> mostGeneralArguments = new ArrayList<>(arity);
					for (List<Term> terms : usableTerms) {
						Term term0 = terms.get(0);
						if (terms.size() == 1) { mostGeneralArguments.add(term0); } // If only ONE possible filler, use it.
						else                   { mostGeneralArguments.add(getNewILPbodyVar(term0.getTypeSpec())); } // Otherwise create a new variable.
					}
					Literal easyPred = thisTask.stringHandler.getLiteral(predName, mostGeneralArguments);
					SingleClauseNode newEasyNode = new SingleClauseNode(parent, easyPred, null);
					if (!newEasyNode.acceptableCoverageOnPosExamples()) {
						continue;
					}

					// Next look at each term in each set, and see if just adding it to the 'easy node' still leads to acceptability.
					// TODO(@jws) can pruning rules also help here?  seems they should
					boolean continueHigherUp                = false;
					boolean needToLoop                      = true;	// See if some singleton created on the CURRENT loop.
					boolean haveReducedCandidateToSingleton = false;
					while (needToLoop && !continueHigherUp) {
						needToLoop    = false;
						int argNumber = 0; // Mark the argument we're at.  NOTE: need to check even the singleton arguments, since other arguments might have been changed.
						for (List<Term> terms : usableTerms) {
							argNumber++;
							if (!haveReducedCandidateToSingleton && terms.size() < 1) { continue; } // No need to check singletons until others reduced to singletons.
							int argNumberMinus1 = argNumber - 1; // Deal with counting from 0 in code, but 1 in human-readable stuff.
							Term    hold        = mostGeneralArguments.get(argNumberMinus1);  // Need to replace when done.
							boolean itemRemoved = false;
							for (ListIterator<Term> termIter = terms.listIterator(); termIter.hasNext(); ) {
							    Term term = termIter.next();
							     
							    mostGeneralArguments.set(argNumberMinus1, term);
								if (!newEasyNode.acceptableCoverageOnPosExamples()) {
									termIter.remove(); // Drop this candidate.	
									itemRemoved = true;
								}
							}
							if (terms.isEmpty()) {
			
								continueHigherUp = true;
								break;
							} else if (itemRemoved && terms.size() == 1) { // If the one argument is a NEW variable, will waste some cycles UNLESS that SAME new variable also appears elsewhere, so still keep around.
								mostGeneralArguments.set(argNumberMinus1, terms.get(0)); // Since only one possibility, use it from now on.  (This makes the process order dependent, but we can live with that.)
								needToLoop = true; // As long as something became permanent in "mostGeneralArguments," continue.
								haveReducedCandidateToSingleton = true;
							}
							else {
								mostGeneralArguments.set(argNumberMinus1, hold);
							}
						}

					}
					if (continueHigherUp) { continue; }
					
				}
				// Now need to create the cross product of allowed terms.  I.e., if arg1 of predicate p can be any of {x1, x2} and argument any of {y1, y2, y3} than can create p(x1,y1), p(x1,y2), p(x1,y3), p(x2,y1), p(x2,y2), and p(x2,y3).  				
				if (allNeededPredsFound) {
					List<List<Term>> allArgPossibilities = Utils.computeCrossProduct(usableTerms, thisTask.maxCrossProductSize); // This is the set of cross products.

					List<List<Term>> allArgPossibilities2 = allArgPossibilities;
					
					// If some fillers really are supposed to be CONSTANTS, collect all (up to k?) ways the variables rep'ing the constants can be bound in some pos seed.
					// Add the constant'ized version to allArgPossibilities.
					if (typesOfNewConstants != null) {
						allArgPossibilities2 = new ArrayList<>(4);
						for (List<Term> args : allArgPossibilities) {
							if (seeIfVarsPresent(args, typesOfNewConstants)) { 
								Literal pred = thisTask.stringHandler.getLiteral(predName, args);	   // Create predicate(arguments) for the predicate being added.
								SingleClauseNode newNode = new SingleClauseNode(parent, pred, specs);  // Create the new search node.  Don't worry about new types here.
								thisTask.collectedConstantBindings = null; // The results will appear here.
								List<Variable> listOfVars4constants = collectVarsPresent(args, typesOfNewConstants);
								Literal testForConstants   = thisTask.stringHandler.getLiteral(thisTask.procDefinedForConstants,
																							   new ArrayList<>(listOfVars4constants));  // Provide the arguments that are to be bound to constants.
								SingleClauseNode newNodeForConstants = new SingleClauseNode(newNode, testForConstants, specs);
								newNodeForConstants.acceptableCoverageOnPosSeeds(); // This will fail, but that is OK.  We simply want to collectedConstantBindings.
								if (thisTask.collectedConstantBindings != null) { // If no bindings, then no constants exist so this literal cannot be added.
									// Note: we may get MANY sets of constants here.  Elsewhere there is a limit of the first 1000, which hopefully is never reached.
									List<List<Term>> allConstantsBindings = thisTask.collectedConstantBindings;
									if (thisTask.maxConstantBindingsPerLiteral > 0 && allConstantsBindings.size() > thisTask.maxConstantBindingsPerLiteral) {
										allConstantsBindings = Utils.reduceToThisSizeByRandomlyDiscardingItemsInPlace(allConstantsBindings, thisTask.maxConstantBindingsPerLiteral);
									}
									for (List<Term> args2 : allConstantsBindings) {
										// Need to collect all those constants that involve the variables in typesOfNewConstants.
										List<Term> args3 = new ArrayList<>(args.size());
										int counter2 = 0; // Cannot do a dual-for-loop, since listOfVars4constants probably is shorter than arguments.  Note that counter is only incremented when a var-for-constant is encountered.
										for (Term term : args) {
											if (term == null) { Utils.error("Should not have term=null!  args=" + args + " args2=" + args2); }
											if (typesOfNewConstants.containsKey(term)) {  // If this is one of the variables-to-grab-constants variables, then get the constant.
												Term newTerm = args2.get(counter2++);
												Type newType = typesOfNewConstants.get(term);
												args3.add(newTerm);
												if (typesOfNewTerms == null) { typesOfNewTerms = new HashMap<>(4); } // Make sure this is bound.
												typesOfNewTerms.put(newTerm, newType);  // Look up the type associated with this var-to-grab-constant.
											}
											else { args3.add(term); } // For other terms, we want to use the originals.
										}
										allArgPossibilities2.add(args3);
									}
									thisTask.collectedConstantBindings = null;  // Might as well return these memory cells now.
								}
							}
							else { allArgPossibilities2.add(args); }
						}
					}
					
					// let's not call this too often?  I'm not sure how expensive it is.
					
					// Now walk through all the possible ways this new literal can be added.
					if (allArgPossibilities2 != null) for (List<Term> args : allArgPossibilities2) {
						int numberOfNewVars     = countNewUniqueVariables(args, newVariables);
						int maxDepthOfInputVars = 0;
						// Determine max depth of an input argument.  The depth of a new variable is that max plus 1.  The depth of a new constant is the max of an input variable.
						if (depthsOfTerms != null) for (Term arg : args) {
							Integer thisDepth = depthsOfTerms.get(arg);
							if (thisDepth != null && thisDepth > maxDepthOfInputVars) {
								maxDepthOfInputVars = thisDepth;
							}
						}

						if (numberOfNewVars > maxPossibleNewVars) { // Note: this case is also caught above - i.e., when ZERO new variables are possible.  This code catches that case when N are still allowed, but N+1 (or more) are needed in 'args.'
							continue;
						}
						if (numberOfNewVars > 0 && maxDepthOfInputVars >= thisTask.maxDepthOfNewVars) {
							continue;
						}
						
						// See if this specific pattern of bound variables has occurred too often.
						int     currentInUseGivenInputArgs = 0; // Only update if this is a mode specification that said we need to monitor it.  SO BE AWARE THAT THIS IS COUNT IS NOT CORRECT IF THIS MODE SPEC DID NOT SAY TO MONITOR (i.e., no need to waste the cpu cycles).
						boolean hasPossiblePredMaxPerInputVars = predName.haveMaxOccurrencesPerInputVarsForThisArity(arity);
						if (hasPossiblePredMaxPerInputVars) { // New design requires always requires a lookup unless there are less than two arguments, since at least infinity is stored.  But keep this code here in case there are later changes, plus it also catches inconsistent information.
							List<Type> inputArgumentTypes  = TypeSpec.getListOfInputArgumentTypes(specs);
							Integer    predMaxPerInputVars = predName.getMaxOccurrencesPerInputVars(arity, inputArgumentTypes);
							if (predMaxPerInputVars != null && predMaxPerInputVars < Integer.MAX_VALUE) {
								int length = inputArgumentTypes.size();
								List<Term> valuesOfInputArgs = new ArrayList<>(length);
								for (int i = 0; i < length; i++) {
									if (inputArgumentTypes.get(i) != null) { valuesOfInputArgs.add(args.get(i)); }
									else                                   { valuesOfInputArgs.add(null); }
								}
								currentInUseGivenInputArgs = parent.countPredicateOccurrencesGivenInputArgs(predName, arity, valuesOfInputArgs);
								if (currentInUseGivenInputArgs >= predMaxPerInputVars) {
									continue;
								}
							}
						} else if (arity > 1) { Utils.error("Should always find hasPossiblePredMaxPerInputVars!  predName = '" + predName + "'"); }
						boolean continueCheckingTheseArgs = true; // Could use catch-throw to skip over bad combo's, but for simplicity use this boolean.
						Literal pred = thisTask.stringHandler.getLiteral(predName, specs.applyArgsToSignature(thisTask.stringHandler, args));	// Create predicate(arguments) for each possible set of arguments.

						// Sometimes we wish to KEEP these.
						boolean discardDuplicateLiterals = true;
						if (!parent.dontConsiderThisLiteral(discardDuplicateLiterals, pred, typesOfNewTerms)) { // Discard EXACT duplicates (which is NOT the same as unifiable terms) and literals in the dontReconsider list.
							if (isaVariantOfChildAlreadyGenerated(pred, ((LearnOneClause) task).unifier)) { // Can't do this too early since this code doesn't understand that some variables are to be replaced by constants.
								continue;
							}
							Map<Type,List<Term>> newTypesInChildMap = collectNewTypesPresentInChildMap(args, typesOfNewTerms); // Collect the new typed variables added, if any.
							List<Type>              newTypesInChild = collectNewTypesPresentInChild(); // Grab the other local variable.
							
							Map<Term,Integer> argDepths = new HashMap<>(args.size());
							if (depthsOfTerms == null) { depthsOfTerms = new HashMap<>(4); }
							setTermDepths(args, depthsOfTerms, newVariables, maxDepthOfInputVars, argDepths);							
							SingleClauseNode newNode      = new SingleClauseNode(parent, pred, argDepths, newTypesInChild, newTypesInChildMap, typesOfNewTerms);  // Create the new search node.
							if (newNode.pruneMe) { continue; } // TODO - should we count these?  If this node marks itself (e.g., it might be an unnecessary constrainer), then do not add to OPEN.
							SingleClauseNode newNodePrime = newNode; // This might get changed below.
							if (thisTask.pruner != null && thisTask.pruner.prune(newNode))  {
								continue; 	 // Advance to the next set of arguments.
							}
							List<Literal>    matchables   = (discardDuplicateLiterals ? parent.collectAllVariants(pred) : null);
							
							// If there are already other versions of this predicate (i.e., same head and same # of arguments) in the clause being created, then
							// make sure that on enough of the positive seeds that this new literal can be bound in a different way from the earlier ones.
							if (matchables != null) {
								matchables.add(0, pred);
								List<Term> matchablesAsTerms = reify(matchables);
								Literal  testForDiffBindings = thisTask.stringHandler.getLiteral(thisTask.procDefinedEnoughDiffMatches, matchablesAsTerms);
								newNodePrime = new SingleClauseNode(newNode, testForDiffBindings);
							}
							
							// If dontAddNewVarsUnlessDiffBindingsPossibleOnPosSeeds is set, this potential new clause involves a new variable, and some existing
							// variables can fill the argument the new variable fills, make sure that this new variable
							// can play a role on enough positive seeds (e.g., if for all seeds, this variable is not bound
							// differently than the other candidate fillers, then don't include this new clause).
							if (thisTask.dontAddNewVarsUnlessDiffBindingsPossibleOnPosSeeds && typesOfNewTerms != null) {
								List<Variable> newVars  = collectNewVariables(args, typesOfNewTerms);								
								// Need to consider EACH new "minus" variable separately, and compare (in procDefinedNeedForNewVariables)
								// to all other variables and constants of the given type ANYWHERE IN THE ENTIRE CLAUSE (including the head).
								// Bug: if two (or more) NEW variables of the same type, this code wont check if one new variable can be used instead.
								int countOfNewVarsNeeded = 0;
								if (newVars != null) { // If no new variable, then nothing to check.
									for (Variable newVar : newVars) {
										boolean isaMustBeVar = (mustBeNewVariables != null && mustBeNewVariables.contains(newVar)); // We will always add these.
										if (newVar == null) { Utils.error("Should not have var=null!  args=" + args + " types=" + typesOfNewTerms); }
										Type       thisVarType             = typesOfNewTerms.get(newVar);
										if (thisVarType == null) { Utils.error("This should not happen inside dontAddNewVarsUnlessDiffBindingsPossibleOnPosSeeds."); }
										List<Term> existingTermsOfThisType = (isaMustBeVar ? null : getExistingTermsOfThisType(thisVarType, parent)); // Need ALL the variables of this type, up to and including the head.  We also can accept LOWER items in the isaHier.  E.g., as above, if we're a DOG, collect POODLEs, but *not* ANIMALs. 
										if (!isaMustBeVar && existingTermsOfThisType != null) { // If no other variables of this type, then this variable is needed so no more checking necessary.
											existingTermsOfThisType.add(0, newVar); // The FIRST variable is the new one whose need is being questioned.

											// The job of 'procDefinedNeedForNewVariables' is to see if we add newVar, there is some binding of the	clause where newVar gets a different grounding
											// then the other variables of that same type (if not, no need to add newVar).  It is possible that some of the other variables will be unbound. yet the clause be satisfied  If that is the case,
											// then also no need for newVar.
											Literal testNeedForNewVariables = thisTask.stringHandler.getLiteral(thisTask.procDefinedNeedForNewVariables, existingTermsOfThisType);
										
											SingleClauseNode newNodeDoublePrime = new SingleClauseNode(newNode, testNeedForNewVariables);
											if (newNodeDoublePrime.acceptableCoverageOnPosSeeds()) { countOfNewVarsNeeded++; }

											existingTermsOfThisType.remove(0); // Remove the extra variable added to the front - need to do this since existingTermsOfThisType is a cached result.

											if (countOfNewVarsNeeded > 0) { break; }
										}
										else { countOfNewVarsNeeded++; break; } // Since only need to need ONE of the newVars, can break here (and also a few lines above).
									}
									// Currently, if at least ONE new variable is needed, then use them all (too complicated to handle the case of partially needed sets of new variables).
									if (countOfNewVarsNeeded == 0) { continueCheckingTheseArgs = false; }
								}
							}
							if (!continueCheckingTheseArgs) { continue; } // Advance to the next set of arguments.
							//  Need to call the positive seeds and the negative seeds separately, since only on the POS do we care about the "diff bindings" and constants.
							if (newNodePrime.acceptableCoverageOnPosSeeds()) { // See if it covers enough of the POS seeds and not too many of the NEG seeds.
								// Need to do the NEG seeds separately, since the EXTENSION to some clause that covers too many negatives might not cover too many negs.  In other words, we might need to reconsider adding the current literal later, even if it is no good now.
								// (NEG seeds might be a little confusing - notice that the FIRST literal added to a clause must "knock out" enough of the neg seeds, and maybe no such single literal exists.)
								if (newNode.acceptableCoverageOnNegSeeds()) {  // If so, it is an acceptable child that will be passed to the general search algo for scoring, etc.

									newNode.numberOfNewVars                  = numberOfNewVars + parent.numberOfNewVars;
									newNode.predicateOccurrences             = countOfOccurrences         + 1; // Need to add one, since we're adding this predicate.
									newNode.predicateOccurrencesPerFixedVars = currentInUseGivenInputArgs + 1; // Ditto.  But be sure to read comments above related to this counter.
									children.add(newNode);

									if (dontAddAnyChildToOpenButStillScoreThem && (thisTask.maxFreeBridgersInBody < 1 || !newNode.endsWithBridgerLiteral())) { newNode.setDontAddMeToOPEN(true); }
									if (reportPredicateUsage) {
										predName.incrementAddedCounter();
									}
									
									// This "side effect" is used when collecting all possible k-long conjuncts (eg, compound features).
								}
							}
							else {
								parent.addToDontConsiderThisLiteral(thisTask, predName, args, typesOfNewTerms);
							}
						}
					}
				}
			}
		}

		if (thisTask.performRRRsearch && thisTask.stillInRRRphase1 && children.size() > thisTask.beamWidthRRR) { // Need to keep a random beamWidthRRR of these (note: elsewhere the beam width of the full OPEN will be used, but also limit here so that all children aren't scored since they can be time-consuming and this phase of RRR is intended to be fast).
			children = Utils.reduceToThisSizeByRandomlyDiscardingItemsInPlace(children, thisTask.beamWidthRRR);  // Randomly discard until small enough.
		}

		if (thisTask.probOfDroppingChild > 0 && children.size() >= thisTask.minChildrenBeforeRandomDropping) {
			children.removeIf(sn -> Utils.random() < thisTask.probOfDroppingChild);
		}
		
		// If we made it this far, let's NOT peak at 'time left' since we might get a new best-node quickly by fully scoring the children.
		
		if (thisTask.getDumpGleanerEveryNexpansions() > 0  && thisTask.getNodesConsidered() % thisTask.getDumpGleanerEveryNexpansions() == 0) {
			((Gleaner) thisTask.searchMonitor).dumpCurrentGleaner(thisTask);
		}
		
		if (callCounter >= callCounterMOD) {
			callCounter = 0;

			// TODO(?) - sort by added/considered

			for (PredicateName pName : predicatesMarked) {
				int considered = pName.getConsideredCounts();
				if (considered < 1) { continue; }
				int used       = pName.getAddedCounts();
				if (used < 1) { continue; }
				pName.clearChildrenClausesCounters();
			}
			for (PredicateName pName : predicatesMarked) {
				int considered = pName.getConsideredCounts();
				if (considered < 1) { continue; }
				int used       = pName.getAddedCounts();
				if (used > 0) { continue; }
				pName.clearChildrenClausesCounters();
			}
		}
				
		return children;
	}
	
	private Variable getNewILPbodyVar(TypeSpec typeSpec) {
		Variable result = ((LearnOneClause) task).stringHandler.getNewUnamedVariable();
		result.setTypeSpec(typeSpec);
		return result;
	}

	private int getParentBodyLength(SingleClauseNode parent, LearnOneClause thisTask) {
		// See if bridgers count in length.  Don't count more than maxBridgersInBody.
		int numBridgers = (thisTask.maxFreeBridgersInBody <= 0 ? 0 : parent.numberOfBridgersInBody(thisTask.currentStartingNode)); // Only want to count bridgers up to currentStartingNode.
		return parent.bodyLength() - (thisTask.maxFreeBridgersInBody > 0 ? Math.min(thisTask.maxFreeBridgersInBody, numBridgers) : 0);
	}

	private void setTermDepths(List<Term> arguments, Map<Term,Integer> depthsOfTerms, Map<Variable,Type> newVariables, int maxDepthOfInputVars, Map<Term,Integer> argDepths) {
		if (arguments == null) { return; }
		for (Term arg : arguments) {
			if (arg instanceof Function) {
				setTermDepths(((Function) arg).getArguments(), depthsOfTerms, newVariables, maxDepthOfInputVars, argDepths);
			} else {
				Integer thisDepth = (newVariables == null ? null : depthsOfTerms.get(arg));
				if (thisDepth != null)          { argDepths.put(arg, thisDepth); } // This is an input variable.
				else if (newVariables != null && newVariables.get(arg) != null) { 
								                  argDepths.put(arg, maxDepthOfInputVars + 1); } // This is a new (i.e., output) variable.
				else                            { argDepths.put(arg, maxDepthOfInputVars);     } // This will become a constant.
			}
		}
	}

	private int countNewUniqueVariables(List<Term> items, Map<Variable,Type> newVars) {
		if (items == null || newVars == null) { return 0; }
		int result = 0;
		Set<Term> seenVars = new HashSet<>(8);
		for (Term term : items) if (!seenVars.contains(term) && term instanceof Variable && newVars.containsKey(term)) { 
			result++;
			seenVars.add(term);
		}
		return result;
	}

	// Convert all these literals into terms.  This allows the literals to be arguments in a literal.  (Recall the arguments to a literal are terms.)
	private List<Term> reify(List<Literal> literals) {
		HandleFOPCstrings handler = ((LearnOneClause) task).stringHandler;
		List<Term> result = new ArrayList<>(literals.size());
		for (Literal lit : literals) {
			FunctionName fName = handler.getFunctionName(lit.predicateName.name); // This is probably a bit inefficient.  Cache somewhere/somehow?
			Function newTerm = (((LearnOneClause) task).stringHandler).getFunction(fName, lit.getArguments(), null); // The arguments of a literal are already terms.
			result.add(newTerm);
		}
		return result;
	}
	
	private Map<Type,List<Term>>  collectNewTypesPresentInChildMap(List<Term> args, Map<Term, Type> typesOfNewTerms) {
		if (typesOfNewTerms == null) { return null; }
		newTypesPresentInChildMap = null;
		newTypesPresentInChild    = null;
		help_collectNewTypesPresentInChildMap(args, typesOfNewTerms);
		return newTypesPresentInChildMap;
	}
	
	// A "hack" to return two results w/o doing an extra "new."  Be careful when calling.
	private List<Type> collectNewTypesPresentInChild() {
		 List<Type>  temp = newTypesPresentInChild;
		 newTypesPresentInChild    = null;
		 newTypesPresentInChildMap = null; // Clean this up as well.
		 return temp;
	}
	
	private void help_collectNewTypesPresentInChildMap(List<Term> args, Map<Term,Type> typesOfNewTerms) {
		if (args != null) for (Term term : args) { collectNewTypesPresentInArg(term, typesOfNewTerms); }
	}	
	
	private void collectNewTypesPresentInArg(Term arg, Map<Term,Type> typesOfNewTerms) {
		if (arg instanceof Variable) {
			Variable argAsVar = (Variable) arg;
			Type     argType  = typesOfNewTerms.get(argAsVar);
			
			if (argType != null) { // This variable is a new one.  So need to add its type.
				if (newTypesPresentInChildMap == null) {  // In no hash map, initialize.
					newTypesPresentInChildMap = new HashMap<>(4);
					newTypesPresentInChild    = new ArrayList<>(4);
				}
				List<Term> termsOfThisType = newTypesPresentInChildMap.get(argType); // See if any variables of this type in the hash map.
				if (termsOfThisType != null) { // Is there already a list for variables of this type in the hash map?
					termsOfThisType.add(argAsVar);
				}
				else { // Otherwise create one.
					List<Term> termList = new ArrayList<>(1);
					termList.add(argAsVar);
					newTypesPresentInChildMap.put(argType, termList);
					newTypesPresentInChild.add(argType);  // Also record that a new type encountered.
				}
			}
		}
		else if (arg instanceof Constant) {
			Constant argAsConst = (Constant) arg;
			Type     argType    = typesOfNewTerms.get(argAsConst);
			
			if (argType != null) { // This constant is a new one.  So need to add its type. todo: clean up this code so vars and constants treated the same - ie, too much duplication.
				if (newTypesPresentInChildMap == null) {  // In no hash map, initialize.
					newTypesPresentInChildMap = new HashMap<>(4);
					newTypesPresentInChild    = new ArrayList<>(4);
				}
				List<Term> termsOfThisType = newTypesPresentInChildMap.get(argType); // See if any vars of this type in the hash map.
				if (termsOfThisType != null) { // Is there already a list for terms of this type in the hash map?
					termsOfThisType.add(argAsConst);
				}
				else { // Otherwise create one.
					List<Term> termList = new ArrayList<>(1);
					termList.add(argAsConst);
					newTypesPresentInChildMap.put(argType, termList);
					newTypesPresentInChild.add(argType);  // Also record that a new type encountered.
				}
			}
		}
		else if (arg instanceof Function) {
			Function argAsFunct = (Function) arg;
			help_collectNewTypesPresentInChildMap(argAsFunct.getArguments(), typesOfNewTerms);			
		}
		else { Utils.error("Should not reach here: " + arg); }
	}
	
	// From these arguments, collect those that are variables and are in this HashMap.
	private List<Variable> collectVarsPresent(List<Term> args, Map<Variable,Type> typesOfNewConstants) {
		if (args == null || typesOfNewConstants == null) { return null; }
		List<Variable> result = new ArrayList<>(args.size());
		for (Term arg : args) {
			if (!(arg instanceof Variable)) { continue; }
			if (typesOfNewConstants.containsKey(arg)) { result.add((Variable) arg); }
		}
		return result;
	}
	
	private List<Variable> collectNewVariables(List<Term> args, Map<Term,Type> typesOfNewTerms) {
		if (args == null || typesOfNewTerms == null) { return null; }
		
		List<Variable> result = null;
		for (Term term : args) if (term instanceof Variable && typesOfNewTerms.containsKey(term)) {
			if (result == null) { result = new ArrayList<>(args.size()); }
			result.add((Variable) term);
		}
		return result;
	}
	
	// From these arguments, see if any variables are in this Map.
	private boolean seeIfVarsPresent(List<Term> args, Map<Variable,Type> typesOfNewConstants) {
		if (args == null || typesOfNewConstants == null) { return false; }
		for (Term arg : args) {
			if (!(arg instanceof Variable)) { continue; }
			if (typesOfNewConstants.containsKey(arg)) { return true; }
		}
		return false;
	}
	
	private List<Term> getExistingTermsOfThisType(Type type, SingleClauseNode parent) {
		return parent.termsOfThisTypePresentInChild(type);
	}
	
	private void putParentClauseInFormForPruning(SingleClauseNode parent) {
		Clause      parentClause = parent.getClause();
		BindingList bl           = parentClause.copyAndReplaceVariablesWithNumbers(constantsToUse);
		cachedBindingListForPruning = bl;
		numberedBodyForPruning = (bl == null ? parentClause : parentClause.applyTheta(bl.theta));
		literalsTriedSoFar.clear();
	}

	private boolean isaVariantOfChildAlreadyGenerated(Literal lit, Unifier unifier) {
		boolean result = false;
		List<Literal> literalsWithThisPnameTriedSoFar = literalsTriedSoFar.get(lit.predicateName); // Could also hash on arity, but don't bother unless this method becomes a bottleneck.
		Literal       initNumberedLit = (cachedBindingListForPruning == null ? lit : lit.applyTheta(cachedBindingListForPruning.theta));
		
		if (literalsWithThisPnameTriedSoFar == null) {
			literalsWithThisPnameTriedSoFar = new ArrayList<>(16);
			literalsTriedSoFar.put(lit.predicateName, literalsWithThisPnameTriedSoFar);
		} else {
			result = (isaVariantOfChildAlreadyGenerated_version2(initNumberedLit) ||
				      isaVariantOfChildAlreadyGenerated_version1(lit, initNumberedLit, unifier));
		}
		literalsWithThisPnameTriedSoFar.add(initNumberedLit);	
		return result;
	}
	private boolean isaVariantOfChildAlreadyGenerated_version1(Literal lit, Literal initNumberedLit, Unifier unifier) {
		PredicateName           pName            = lit.predicateName;
		List<ConnectedSentence> possibleVariants = pName.getVariants(lit.numberArgs());
		
		if (possibleVariants == null) { return false; }
		BindingList   newBL           = bindVarsToUniqueConstants(initNumberedLit);
		Literal fullyNumberedLit = initNumberedLit.applyTheta(newBL.theta); // Need to get rid of all variables.
		for (ConnectedSentence pair : possibleVariants) { // Look at every 'variant' matching this literal.
			Literal     litA      = (Literal) pair.getSentenceA();
			// Don't use dummyBindingList on this next line, since dummyBindingList is used below!
			BindingList bindings1 = unifier.unify(fullyNumberedLit, litA); // Make sure it matches this specific literal IN ITS NUMBERED FORM (so as to not overly generalize).
			
			if (bindings1 == null) { continue; }
			
			Literal       litB   = (Literal) pair.getSentenceB();
			PredicateName pName2 = litB.predicateName;
			List<Literal> literalsWithPname2TriedSoFar = literalsTriedSoFar.get(pName2); // See if previous literals match the 'partner' of this variant.
			if (literalsWithPname2TriedSoFar == null) { continue; }
			Literal litBmatched = litB.applyTheta(bindings1.theta);			

			boolean anyNewVarsInBmatched = litBmatched.containsVariables();
			if (anyNewVarsInBmatched) {

				// TODO(@hayesall): This reports an error, but can likely be simplified.

				Utils.println("*** VARIANT PRUNING:");
				Utils.println("            lit: " + lit);
				Utils.println("    litNumbered: " + fullyNumberedLit);
				Utils.println("           litA: " + litA);
				Utils.println("    litA@theta1: " + litA.applyTheta(bindings1.theta));
				Utils.println("           litB: " + litB);
				Utils.println("    litB@theta1: " + litBmatched);

				Utils.error("Should there be new variables here? " + litBmatched.collectFreeVariables(null));
			}
			
			for (Literal oldLit : literalsWithPname2TriedSoFar) {
				dummyBindingList.theta.clear();
				BindingList bindings2 = unifier.unify(oldLit, litBmatched, dummyBindingList);
				if (bindings2 != null) { // Do a "sanity check" here.
					boolean anyNewVarsInOldLit = oldLit.applyTheta(bindings2.theta).containsVariables();
					if (anyNewVarsInOldLit) {

						// TODO(@hayesall): This reports an error, but can likely be simplified.

						Utils.println("*** VARIANT PRUNING:");
						Utils.println("            lit: " + lit);
						Utils.println("    litNumbered: " + fullyNumberedLit);
						Utils.println("           litA: " + litA);
						Utils.println("    litA@theta1: " + litA.applyTheta(bindings1.theta));
						Utils.println("           litB: " + litB);
						Utils.println("    litB@theta1: " + litBmatched);
						Utils.println("         oldLit: " + oldLit);
						Utils.println("  oldLit@theta2: " + oldLit.applyTheta(bindings2.theta));
						Utils.println("  bl 1: " + bindings1);
						Utils.println("  bl 2: " + bindings2);

						Utils.error("Should there be new variables here? " + oldLit.applyTheta(bindings2.theta).collectFreeVariables(null));
					}
					countOfPruningDueToVariantChildren++;
					return true;
				}
			}
		}
		return false;
	}
	
	private boolean isaVariantOfChildAlreadyGenerated_version2(Literal initNumberedLit) {
		PredicateName pName = initNumberedLit.predicateName;
		List<Literal> literalsWithThisPnameTriedSoFar = literalsTriedSoFar.get(pName); // Could also hash on arity, but don't bother unless this method becomes a bottleneck. 
		if (literalsWithThisPnameTriedSoFar != null) {
			for (Literal oldLit : literalsWithThisPnameTriedSoFar) {
				dummyBindingList.theta.clear();
				if (oldLit.variants(initNumberedLit, dummyBindingList) != null) {
					countOfPruningDueToVariantChildren++;
					return true;
				}
			}
		}
		return false;
	}

	BindingList bindVarsToUniqueConstants(Literal numberedLiteral) {
		BindingList          blForParent = cachedBindingListForPruning;
		BindingList          result      = new BindingList();
		Collection<Variable> newVars     = numberedLiteral.collectFreeVariables(null);		
		if (newVars != null) {
			int currentPositionInConstants = (blForParent == null ? 0 : blForParent.theta.size());
			for (Variable newVar : newVars) { 
				result.addBinding(newVar, constantsToUse[currentPositionInConstants++]); // If we get an error here, look at Clause.copyAndReplaceVariablesWithNumbers (seems unlikely we'll ever have more than 100 unique variables in a clause ...).
			}
		}
		return result;
	}
		
	public void clearAnySavedInformation() {
		if (newTypesPresentInChild    != null) { newTypesPresentInChild.clear();    }
		if (newTypesPresentInChildMap != null) { newTypesPresentInChildMap.clear(); }
		if (literalsTriedSoFar        != null) { literalsTriedSoFar.clear();        }
		if (dummyBindingList != null && dummyBindingList.theta != null) { dummyBindingList.theta.clear(); }
		countOfPruningDueToVariantChildren = 0;
	}

    private LearnOneClause getTask() {
        return (LearnOneClause) task;
    }

	private Set<PredicateNameAndArity> applyModeContraints(Set<PredicateNameAndArity> bodyModes, SingleClauseNode parent) {
        List<ModeConstraint> constraints = getTask().getModeConstraints();

        Set<PredicateNameAndArity> modes = bodyModes;
        boolean mutable = false;

        if (!constraints.isEmpty()) {
            for (ModeConstraint modeConstraint : constraints) {
                if (modes.isEmpty()) {
                    break;
                }
                Set<PredicateNameAndArity> constrainedModes = modeConstraint.applyConstraint(parent, modes, mutable);
                if (constrainedModes != null) {
                    modes = constrainedModes;
                    mutable = true;
                }
            }
        }
        return modes;
    }
}
