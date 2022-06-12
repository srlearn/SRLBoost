package edu.wisc.cs.will.DataSetUtils;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.MessageType;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author shavlik
 */
public class TypeManagement {

    private final HandleFOPCstrings stringHandler;

    private Map<PredicateName, Set<Type>> beenWarnedHashMap;

    private Map<Term, Map<Type, Literal>> addedConstantHashMap;

    public TypeManagement(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;
    }

    // Collect as many types as possible from the data read in.
    // The Boolean return indicates whether or not addToFactsFile should be called.
    public void collectTypedConstants(List<Literal> targetLiterals, List<List<ArgSpec>> targetArgSpecs, Set<PredicateNameAndArity> bodyModes,
                                      List<Example> posExamples, List<Example> negExamples, Iterable<Sentence> backgroundFacts) {

        Utils.println("\n% Collecting the types of constants.");

        collectImplicitTypeConstantsViaModeAndFactInspection(bodyModes, backgroundFacts);
        Utils.println("\n% Looking at the training examples to see if any types of new constants can be inferred.");

        // TODO(hayesall): Inlining on the assumption that `target` and `types` are known at runtime.
        //      Type errors should be treated as runtime/parsing errors.

        if (targetLiterals != null && (posExamples != null || negExamples != null)) {
            for (int i = 0; i < Utils.getSizeSafely(targetLiterals); i++) {
                PredicateName targetPredicate = targetLiterals.get(i).predicateName;
                assert targetArgSpecs != null;
                List<ArgSpec> argSpecs = targetArgSpecs.get(i);
                recordTypedConstantsFromTheseExamples(posExamples, targetPredicate, argSpecs);
                recordTypedConstantsFromTheseExamples(negExamples, targetPredicate, argSpecs);
            }
        }
        checkThatTypesOfAllConstantsAreKnown(backgroundFacts);
    }

    private void collectImplicitTypeConstantsViaModeAndFactInspection(Set<PredicateNameAndArity> bodyModes, Iterable<Sentence> backgroundFacts) {
        Map<Term, Set<Type>> alreadyCheckedConstantHash = new HashMap<>(4096);
        for (PredicateNameAndArity predName : bodyModes) {
            // First need to see if this predicate can have DIFFERENT numbers of arguments.  If so, we need to treat each separately.
            Set<Integer> sizes = new HashSet<>(4);
            for (PredicateSpec specs : predName.getPredicateName().getTypeList()) { // Consider each known mode for this predicate.
                Integer length = Utils.getSizeSafely(specs.getSignature());
                sizes.add(length);
            }

            for (Integer argSize : sizes) {
                boolean firstTime = true;
                int size = Utils.getSizeSafely(predName.getPredicateName().getTypeListForThisArity(argSize));
                Set<Integer> ambiguous = new HashSet<>(size);
                List<Type> argTypes = new ArrayList<>(size);
                for (PredicateSpec specs : predName.getPredicateName().getTypeListForThisArity(argSize)) { // Again consider each known mode for this predicate, but only worry about those with arity = argSize.
                    // We now have to see if all modes for this parity and arity specify the same types for the arguments.
                    // If there is ambiguity then we cannot infer new typed constants since we don't know which mode matches the facts.
                    // (Aside: we could have fact p(dog1, dog2) but only a mode about humans [i.e., the p(dog1,dog2) should be ignored] and this code will infer dog1 and dog2 are humans.  Not clear how to avoid this short of requiring users to always give lists of constants, which is quite the burden.)
                    help_collectImplicitTypeConstantsViaModeAndFactInspection(ambiguous, specs.getSignature(), predName, firstTime, specs.getTypeSpecList(), argTypes);
                    firstTime = false; // The second (and subsequent) time around we need to see if the types are the same, e.g. may only differ in terms of +/-/# etc, which doesn't matter here.
                }
                if (ambiguous.size() < size) {

                    if (backgroundFacts != null) {
                        for (Sentence sentence : backgroundFacts) {
                            if (sentence instanceof Literal) {
                                Literal fact = (Literal) sentence;
                                if (fact.predicateName == predName.getPredicateName() && fact.getArity() == argSize) {
                                    help_matchFactsAndModes(fact, fact.getArguments(), ambiguous, argTypes, alreadyCheckedConstantHash);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    private void help_matchFactsAndModes(Literal fact, List<Term> args, Set<Integer> ambiguous, List<Type> argTypes, Map<Term, Set<Type>> alreadyCheckedConstantHash) {

        int counter = 0;
        if (args == null) {
            return;
        }
        for (Term arg : args) {
            if (ambiguous.contains(counter)) {
                counter++; // Need to skip this argument.
            }
            else if (arg.isGrounded()) {
                Type thisType = argTypes.get(counter);
                if (thisType == null) {
                    if (args.size() > 1) {
                        Utils.println(fact + " thisType = " + null);
                    }
                    counter++; // I added this Nov 2010 since it seems to be needed, though didn't run into any specific bug.
                    continue;  // This argument is a specific constant and not a type, so no type inference possible.
                }
                Set<Type> lookup1 = alreadyCheckedConstantHash.get(arg);

                if (lookup1 != null && lookup1.contains(thisType)) {
                    counter++;
                    continue; // Already checked if this constant is of this type.
                }
                // Have inferred the type of this constant.
                addNewConstant(stringHandler, arg, thisType, fact);
                if (lookup1 == null) {
                    lookup1 = new HashSet<>(4);
                    alreadyCheckedConstantHash.put(arg, lookup1);
                }
                lookup1.add(thisType);
                counter++;
            }
            else if (arg instanceof Variable) {
                counter++; // Simply skip variables.
            }
            else {
                Utils.error("Should not have arg=" + arg);
            }
        }

    }

    private void help_collectImplicitTypeConstantsViaModeAndFactInspection(Set<Integer> ambiguous, List<Term> signature, PredicateNameAndArity predName, boolean firstTime,
                                                                           List<TypeSpec> typeSpecList, List<Type> argTypes) {
        int counter = 0;
        if (signature == null) {
            Utils.error("Should not have signature = null for '" + predName + "'.");
        }
        for (Term term : signature) {
            if (term.isGrounded()) {
                TypeSpec spec = typeSpecList.get(counter);
                Type thisType = (spec.isaType); // Cannot do type inferencing when the specification is for a SPECIFIC value.
                if (firstTime) {
                    argTypes.add(thisType);
                }
                else if (argTypes.get(counter) != thisType) {
                    Utils.println("%  Because type='" + thisType + "' is inconsistent with " + predName + argTypes + ", cannot infer constants from argument #" + (counter + 1) + " in mode = " + typeSpecList);
                    ambiguous.add(counter); // Was 'break' but should be able to walk through the other terms.
                }
                counter++;
            }
            else {
                Utils.error("Should not have term = " + term);
            }
        }
    }

    // Check all constants in facts and make sure they are typed (and uniquely!).
    private void checkThatTypesOfAllConstantsAreKnown(Iterable<Sentence> backgroundFacts) {
        Set<Term> alreadyCheckedHash = new HashSet<>(1024);

        if (backgroundFacts != null) {
            for (Sentence sentence : backgroundFacts) {
                if (sentence instanceof Literal) {
                    Literal fact = (Literal) sentence;

                    if (fact.predicateName.hasMatchingMode(fact)) {
                        for (Term arg : fact.getArguments()) {
                            if (arg.isGrounded()) {
                                if (alreadyCheckedHash.contains(arg)) {
                                    continue;
                                } // Already checked this constant.
                                if (stringHandler.getTypesOfConstant(arg, false) == null) {
                                    throw new RuntimeException("Deprecated + Should not be possible.");
                                }
                                alreadyCheckedHash.add(arg);
                            }
                        }
                    }
                }
            }
        }
    }

    private void recordTypedConstantsFromTheseExamples(List<Example> examples, PredicateName targetPredicate, List<ArgSpec> targetArgSpecs) {

        if (examples == null) {
            return;
        }

        // Collect all the constants in the specified set of examples.
        for (Literal ex : examples) {
            if (targetPredicate != ex.predicateName) { // && warningCounter++ < 10) {
                // This would be handled later by the next call to recordTyped...
                continue;
            }
            int counter = 0;
            for (Term arg : ex.getArguments()) {
                if (arg.isGrounded()) {
                    if (counter >= targetArgSpecs.size()) {
                        Utils.error("#args do not match!  TargetArgSpecs = " + targetArgSpecs + " while ex = " + ex);
                    }
                    ArgSpec spec = targetArgSpecs.get(counter);
                    addNewConstant(stringHandler, arg, spec.typeSpec.isaType, ex);
                    counter++;
                } else if (arg instanceof Function) {
                    Function f = (Function) arg;
                    counter += f.countLeaves();
                } else if (arg instanceof Variable) {
                    Utils.error("Should not have variables here: " + arg + " for: " + targetPredicate);
                } else {
                    Utils.error("Have a type here for which code needs to be written: " + arg);
                }
            }
        }
    }

    // See if this is a new constant of this type.
    private void addNewConstant(HandleFOPCstrings stringHandler, Term constant, Type type, Literal generator) {
        if (generator == null) {
            Utils.error("Cannot have generator=null.");
        }
        PredicateName predName = generator.predicateName;
        int predArity = generator.numberArgs();
        String name = constant.toString();
        if (name == null) {
            Utils.error("Have no name for this constant: '" + constant + "' from " + generator);
        } // Not sure printing constant here will do anything, but might as well try.
        // See comment next line.  Type constantAsType = stringHandler.getIsaType(constant.getName());
        // I (jws) no longer think this is needed: if (stringHandler.reverseIsa(constantAsType) != null) { Utils.error("This code assumes that type '" + constantAsType + "' is a LEAF in the type hierarchy, but instead it has these children: '" + Utils.limitLengthOfPrintedList(stringHandler.reverseIsa(constantAsType), 25) + "'."); }
        Set<Term> knownConstants = stringHandler.getConstantsOfExactlyThisType(type);

        if (knownConstants != null && knownConstants.contains(constant)) {
            return;
        } // Already in the map.
        if (stringHandler.getTypesOfConstant(constant, false) != null) { // See if any types of this constant are already known.

            List<Type> existingTypes = stringHandler.getTypesOfConstant(constant, false);
            if (existingTypes != null) {
                for (Type existing : existingTypes) {
                    // If the new type is a superclass of an existing type, don't add.
                    if (stringHandler.isaHandler.isa(existing, type)) {
                        throw new RuntimeException("Deprecated + Should not be possible.");
                    }

                    // If the new type is a subclass of an existing type, remove the old attachment to this constant, since the ISA hierarchy contains this information.
                    if (stringHandler.isaHandler.isa(type, existing)) {
                        throw new RuntimeException("Deprecated + Should not be possible.");
                    }
                }
            }

            if (beenWarnedHashMap == null) {
                beenWarnedHashMap = new HashMap<>(4);
            }
            Set<Type> lookup1a = beenWarnedHashMap.computeIfAbsent(predName, k -> new HashSet<>(4));  // See if there has been a warning about this type from this predicate.
            if (!lookup1a.contains(type)) {
                if (!predName.dontComplainAboutMultipleTypes(predArity) && !dontWorryAboutTheseTypes(existingTypes)) {

                    // TODO(hayesall): Turn this into an actual error earlier.

                    Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "\n%   *** WARNING ***  Constant '" + constant + "' is already marked as being of types = " + existingTypes
                            + ";\n%          type = '" + type + "' may be added if not already known.\n%  PredicateName = '" + predName + "', from '" + generator + "',\n%  which has types = " + predName.getTypeList()
                            + "\n%   Other warnings with this predicate and this new type are not reported in order to keep this printout small.  Use dontComplainAboutMultipleTypes to override.");
                }
                lookup1a.add(type);
            }
        }

        if (addedConstantHashMap == null) {
            addedConstantHashMap = new HashMap<>(1024);
        }
        Map<Type, Literal> lookup1b = addedConstantHashMap.get(constant);  // See if this constant has been already assigned to another type, and if so report the literal that caused it to be so.
        if (lookup1b != null && !lookup1b.containsKey(type)) { // Just report the FIRST conflict, since the others can be traced back from the reports (i.e., the first one doesn't know it is a duplicate).
            if (!predName.dontComplainAboutMultipleTypes(predArity)) {
                dontWorryAboutTheseTypes(lookup1b);
            }
        }
        if (lookup1b == null) {
            lookup1b = new HashMap<>(4);
            addedConstantHashMap.put(constant, lookup1b);
        }
        if (!lookup1b.containsKey(type)) {
            lookup1b.put(type, generator);
        }
        // Possibly this line should be much earlier in this method, but the other warnings can be helpful.
        Type newType = stringHandler.isaHandler.getIsaType(constant.toString());
        if (newType != type && !stringHandler.isaHandler.okToAddToIsa(newType, type)) { // OK to add constant with same name as type.
            return;
        }
        stringHandler.addNewConstantOfThisType(constant, type);
    }

    private void dontWorryAboutTheseTypes(Map<Type, Literal> types) {
        if (types == null) {
            return;
        }
        for (Type type : types.keySet()) {
            if (!dontWorryAboutThisType(type)) {
                return;
            }
        }
    }

    private boolean dontWorryAboutTheseTypes(List<Type> types) {
        if (types == null) {
            return true;
        }
        for (Type type : types) {
            if (!dontWorryAboutThisType(type)) {
                return false;
            }
        }
        return true;
    }

    private boolean dontWorryAboutThisType(Type type) {
        return type.typeName.equalsIgnoreCase("willAnything") || type.typeName.equalsIgnoreCase("willList");
    }
}
