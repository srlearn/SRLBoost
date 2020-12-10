package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.SentenceVisitor;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author shavlik
 */
public class Literal extends Sentence implements DefiniteClause, LiteralOrFunction {
    private static final long serialVersionUID = -7292498553320907481L;
    public PredicateName predicateName;
    private List<Term>   arguments;     // Note: should not directly manipulate.  Instead use addArgument(), removeArgument(), and setArguments().
    private List<String> argumentNames; // (Optional) names of the arguments.

    private int containsVariables = -1; // Only set to false if CHECKED.  (Key: -1 = unknown, 0 = false, 1 = true.)
    private int cached_arity      = -1;

    protected Literal() {
    }

    protected Literal(HandleFOPCstrings stringHandler, PredicateName pred) {
    	this();
        predicateName      = pred;
        this.stringHandler = stringHandler;
        this.arguments     = null;
        this.argumentNames = null;
    }
    /* Create a Literal given a predicate name and list of terms.
     *
     * TAW: This uses the varargs semantics common in C.  It allows the user to
     * specify a list of terms to be used as arguments without wrapping it in a List
     * or array.  For example, I can do this:
     *
     * 	new Literal(someHandler, "myPredName", Term1, Term2, Term3)
     *
     * Java boxes up the Term1, Term2, Term3 into a Term array.  So arguments will
     * be of type Term[] or null if there were no Terms passed in.
     *
     * @param stringHandler string handler for this predicate
     * @param pred predicate name
     * @param arguments Terms to be arguments of the predicate
     */
    protected Literal(HandleFOPCstrings stringHandler, PredicateName pred, List<Term> arguments) {
        predicateName      = pred;
        this.arguments     = arguments;
        this.argumentNames = null;
        this.stringHandler = stringHandler;
    }


    Literal(HandleFOPCstrings stringHandler, PredicateName pred, Term argument) {
    	this();
        predicateName = pred;
        List<Term> args = new ArrayList<>(1);
        args.add(argument);
        this.stringHandler = stringHandler;
        this.arguments     = args;
        this.argumentNames = null;
    }

    Literal(HandleFOPCstrings stringHandler, PredicateName pred, List<Term> arguments, List<String> argumentNames) {
        this(stringHandler, pred, arguments);
        this.argumentNames = argumentNames;
        sortArgumentsByName();
        this.stringHandler = stringHandler;
        // If one or the other is null, don't check (e.g, this might be a bareCopy call).
        if (arguments != null && argumentNames != null && Utils.getSizeSafely(arguments) != Utils.getSizeSafely(argumentNames)) {
            Utils.error("Have " + arguments + " and " + argumentNames + " - number of arguments and number of names must match.");
        }
    }

    public Literal clearArgumentNamesInPlace() {
        // TODO(@hayesall): Multiple `null` checks, this method might be simplified.
        if (numberArgs() < 1) {
            return this;
        }
        if (argumentNames != null) {
            if (argumentNames.get(0).equalsIgnoreCase("name")) {
                removeArgument(arguments.get(0), argumentNames.get(0));
            }
        }
        argumentNames = null;
        if (arguments == null) {
            return this;
        }
        for (Term term : arguments) {
            if (term instanceof Function) {
                ((Function) term).clearArgumentNamesInPlace();
            }
        }
        return this;
    }

    public boolean isaBridgerLiteral() { // TODO need to check allCollector other vars are bound?
        return predicateName.isaBridgerLiteral(arguments);
    }

    // See Parser.processIsaInterval() for more information.
    public Term getLowerBoundary_1D() {
        int arity = numberArgs();
        if (predicateName.boundariesAtEnd_1D.contains(arity)) {
            return arguments.get(arity - 2);
        }
        if (arity != 3) {
            Utils.println("predicateName = " + predicateName + " predicateName.boundariesAtEnd_1D = " + predicateName.boundariesAtEnd_1D);
            Utils.error("This literal is said to be a 1D interval, but it doesn't have three arguments: " + this);
        }
        return arguments.get(0);
    }

    public Term getUpperBoundary_1D() {
        int arity = numberArgs();
        if (predicateName.boundariesAtEnd_1D.contains(arity)) {
            return arguments.get(arity - 1);
        }
        if (arity != 3) {
            Utils.error("This literal is said to be a 1D interval, but it doesn't have three arguments: " + this);
        }
        return arguments.get(2);
    }

    public Literal createLiteralWithMaskedBoundaries_1D() {
        Literal newVersion = (Literal) copy();
        int arity = numberArgs();
        if (predicateName.boundariesAtEnd_1D.contains(arity)) {
            newVersion.arguments.set(arity - 2, null);
            newVersion.arguments.set(arity - 1, null);
        }
        else if (arity != 3) {
            Utils.println("predicateName = " + predicateName + " predicateName.boundariesAtEnd_1D = " + predicateName.boundariesAtEnd_1D);
            Utils.error("This literal is said to be a 1D interval, but it doesn't have three arguments: " + this);
        }
        else {
            newVersion.arguments.set(0, null);
            newVersion.arguments.set(2, null);
        }
        return newVersion;
    }

    private Literal getBareCopy(List<Term> newArguments) {
        return getBareCopy(newArguments, argumentNames);
    }

    private Literal getBareCopy(List<Term> newArguments, List<String> newNames) {
        return (Literal) stringHandler.getLiteral(predicateName, newArguments, newNames).setWeightOnSentence(wgtSentence);
    }

    // A ('reverse') variant of contains().
    public boolean member(Collection<Literal> otherLists, boolean useStrictEquality) {
        if (Utils.getSizeSafely(otherLists) < 1) {
            return false;
        }
        for (Literal otherLit : otherLists) {
            if (this.equals(otherLit, useStrictEquality)) {
                return true;
            }
        }
        return false;
    }

    // This code makes changes "in place" and assumes that the caller has made a copy if necessary.  (Note: be very careful if you change this code. For efficiency reasons it tries to save using new memory.)
    @Override
    public Literal applyTheta(Map<Variable, Term> theta) {
        // This should be essentially the same code as in Function.applyTheta
        boolean needNewLiteral = false; // See if there is a chance this might need to change (only do a one-level deep evaluation).
        if (arguments != null) {
            for (Term term : arguments) {
                if (!((term instanceof Variable && theta.get(term) == null) || term instanceof Constant)) {
                    needNewLiteral = true;
                    break;
                }
            }
        }
        if (!needNewLiteral) {
            return this;
        }
        int numbArgs = numberArgs();
        List<Term> newArguments = (numbArgs == 0 ? null : new ArrayList<>(numberArgs()));
        if (numbArgs > 0) {
            for (Term arg : arguments) {
                if (arg == null) {
                    Utils.error("Has an arg=null: " + this);
                }
                newArguments.add(arg.applyTheta(theta));
            }
        }
        return getBareCopy(newArguments);
    }

    public Literal applyTheta(BindingList bindingList) {
        if (bindingList != null) {
            return applyTheta(bindingList.theta);
        }
        else {
            return this;
        }
    }

    @Override
    public Literal copy(boolean recursiveCopy) { // recursiveCopy=true means that the copying recurs down to the leaves.   Also, variables will be created anew if requested.
        List<Term>   newArguments = (arguments     != null ? new ArrayList<>(  numberArgs()) : null);
        List<String> newArgNames  = (argumentNames != null ? new ArrayList<>(numberArgs()) : null);
        if (argumentNames != null) {
            newArgNames.addAll(argumentNames);
        }
        assert newArguments != null;
        if (recursiveCopy) {
            if (arguments != null) {
                for (Term term : arguments) {
                    newArguments.add(term == null ? null : term.copy(true));
                }
            }
            return getBareCopy(newArguments, newArgNames);
        }
        if (arguments != null) {
            newArguments.addAll(arguments);
        }
        return getBareCopy(newArguments, newArgNames);
    }

    @Override
    public Literal copy2(boolean recursiveCopy, BindingList bindingList) { // recursiveCopy=true means that the copying recurs down to the leaves.   Also, variables will be created anew if requested.
        List<Term> newArguments = (arguments != null ? new ArrayList<>(numberArgs()) : null);
        List<String> newArgNames = (argumentNames != null ? new ArrayList<>(numberArgs()) : null);
        if (argumentNames != null) {
            newArgNames.addAll(argumentNames);
        }
        assert newArguments != null;
        if (recursiveCopy) {
            if (arguments != null) {
                for (Term term : arguments) {
                    newArguments.add(term == null ? null : term.copy2(true, bindingList));
                }
            }
            return getBareCopy(newArguments, newArgNames);
        }
        if (arguments != null) {
            newArguments.addAll(arguments);
        }
        return getBareCopy(newArguments, newArgNames);
    }

    @Override
    public boolean containsTermAsSentence() {
        return false;
    }

    @Override
    public Collection<Variable> collectAllVariables() {
        return collectFreeVariables(null);
    }

    @Override
    public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
        List<Variable> result = null; // Don't create until needed.

        if (arguments != null) {
            for (Term term : arguments) {
                Collection<Variable> temp = term.collectFreeVariables(boundVariables);

                if (temp != null) {
                    if (result == null) {
                        result = new ArrayList<>(4);
                    }
                    for (Variable var : temp) {
                        if (!result.contains(var)) {
                            result.add(var);
                        }
                    }
                }
            }
        }
        return result== null ? Collections.EMPTY_LIST : result;
    }

    private String restOfToString(BindingList bindingList) {
        StringBuilder result = new StringBuilder("(");
        boolean firstOne = true;
        boolean hasArgNames = (argumentNames != null);
        int numberOfArgNames = Utils.getSizeSafely(argumentNames);

        if (arguments != null) {
            for (int i = 0; i < numberArgs(); i++) {
            	
                Term arg = arguments.get(i);
                if (firstOne) {
                    firstOne = false;
                }
                else {
                    result.append(", ");
                    if (stringHandler.numberOfTermsPerRowInPrintouts == 1 || stringHandler.numberOfTermsPerRowInPrintoutsForLiterals == 1) { result.append("\n        "); } // TODO -  write to properly handle stringHandler.numberOfLiteralsPerRowInPrintouts > 1
                }
                if (arg == null) {
                    result.append("null");
                }
                else {
                    result.append(hasArgNames ? (i >= numberOfArgNames ? "noNameForMe" : argumentNames.get(i)) + "=" : "").append(arg.toString(Integer.MAX_VALUE, bindingList));
                } // No need for extra parentheses in an argument list.
            }
        }
        return result + ")";
    }
    
    public String toStringOneLine() {
    	int hold  = stringHandler.numberOfTermsPerRowInPrintouts;
    	int holdL = stringHandler.numberOfTermsPerRowInPrintoutsForLiterals;
    	stringHandler.numberOfTermsPerRowInPrintouts = Integer.MAX_VALUE;
    	String result = toString();
    	stringHandler.numberOfTermsPerRowInPrintouts            = hold;
    	stringHandler.numberOfTermsPerRowInPrintoutsForLiterals = holdL;
    	return result;
    }

    public PredicateName getPredicateName() {
        return predicateName;
    }

    private FunctionName getFunctionName() {
        return getStringHandler().getFunctionName(predicateName.name);
    }

    public Function asFunction() {

        // We need special handling for conCells for some reason...
        if ( this == getStringHandler().getNilAsLiteral() ) {
            return getStringHandler().getNil(); // Make sure we preserve the Nil function for lists.
        }
        else if (predicateName.equals(getStringHandler().standardPredicateNames.consCell)) {
            return getStringHandler().getConsCell(stringHandler.getFunctionName("consCell"), arguments, argumentNames, null);
        }
        else {
            return getStringHandler().getFunction( getFunctionName(),  getArguments(), getArgumentNames(), null);
        }
    }

    public boolean equals(Object obj, boolean considerUseStrictEqualsForLiterals) {
        if ( this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof Literal)) {
            return false;
        }
        final Literal other = (Literal) obj;

        if (!Objects.equals(this.predicateName, other.predicateName)) {
            return false;
        }
        if (!Objects.equals(this.arguments, other.arguments)) {
            return false;
        }
        return Objects.equals(this.argumentNames, other.argumentNames);
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 23 * hash + (this.predicateName != null ? this.predicateName.hashCode() : 0);
        hash = 23 * hash + (this.arguments != null ? this.arguments.hashCode() : 0);
        hash = 23 * hash + (this.argumentNames != null ? this.argumentNames.hashCode() : 0);
        return hash;
    }

    @Override
    public boolean equals(Object other) {
        return equals(other, true);
    }

    // Are these two equivalent POSSIBLY AFTER SOME VARIABLE RENAMING?
    public BindingList variants(Literal other, BindingList bindings) {
        // Need to collect the matched variables (so they don't get matched to another variable elsewhere).
        if (predicateName != other.predicateName) {
            return null;
        }
        int numbArgs      = numberArgs();
        int otherNumbArgs = other.numberArgs();
        if (numbArgs != otherNumbArgs) {
            return null;
        }
        // Have checked that the lengths are equal, so need only one iterator.
        if (arguments != null) for (ListIterator<Term> terms1 = arguments.listIterator(), terms2 = other.arguments.listIterator(); terms1.hasNext();) {
            Term term1 = terms1.next();
            Term term2 = terms2.next();

            if (term1 == term2) {
                continue;
            }
            if (term1 == null || term2 == null) {
                return null;
            }

            bindings = term1.variants(term2, bindings);
            if (bindings == null) {
                return null;
            }
        }
        if (argumentNames == null && other.argumentNames == null) {
            return bindings;
        }
        if (argumentNames == null || other.argumentNames == null) {
            return null;
        }
        for (int i = 0; i < numbArgs; i++) { // Should do a double walk of the two lists, but I don't recall the syntax
            if (!argumentNames.get(i).equalsIgnoreCase(other.argumentNames.get(i))) {
                return null;
            }
        }
        return bindings;
    }

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Sentence that, BindingList bindings) {
        if (!(that instanceof Literal)) return null;

        Literal thatLiteral = (Literal) that;

        if ( this.predicateName != thatLiteral.predicateName ) return null;

        if ( this.numberArgs() != thatLiteral.numberArgs() ) return null;

        for (int i = 0; i < numberArgs(); i++) {
            bindings = this.getArgument(i).isEquivalentUptoVariableRenaming(thatLiteral.getArgument(i), bindings);
            if ( bindings == null ) return null;
        }

        return bindings;
    }

    @Override
    public BindingList variants(Sentence other, BindingList bindings) {
        // Need to collect the matched variables (so they don't get matched to another variable elsewhere).
        if (!(other instanceof Literal)) {
            return null;
        }
        return variants((Literal) other, bindings);
    }

    public int getArity() {
        return numberArgs();
    }

    public int numberArgs() {
        if (cached_arity < 0) {
            setNumberArgs();
        }
        return cached_arity;
    }

    private void setNumberArgs() {
        if (arguments == null) {
            cached_arity = 0;
        }
        else {
            cached_arity = arguments.size();
        }
        containsVariables();
    }

    public boolean containsThisVariable(Variable var) {
        if (arguments == null) {
            return false;
        }
        for (Term arg : arguments) {
            if (arg == var) {
                return true;
            }
        }
        return false;
    }
    
    // Cache this calculation to save time.
    public boolean containsVariables() {
        if (containsVariables < 0) {
            if (arguments == null) {
                containsVariables = 0;
                return false;
            }
            for (Term term : arguments) {
                if (term instanceof Variable) {
                    containsVariables = 1;
                    return true;
                }
                if ((term instanceof Function) && term.containsVariables()) {
                    containsVariables = 1;
                    return true;
                }
            }
            if (containsVariables < 0) {
                containsVariables = 0;
            }
        }
        return (containsVariables > 0);
    }

    /* Would any variables in this clause remain UNBOUND if this binding list were to be applied?
     */
    @Override
    public boolean containsFreeVariablesAfterSubstitution(BindingList theta) {
        if (!containsVariables()) {
            return false;
        }
        if (theta == null || arguments == null) {
            return false;
        }
        for (Term term : arguments) {
            if (term.freeVariablesAfterSubstitution(theta)) {
                return true;
            }
        }
        return false;
    }

    // Clausal-form converter stuff.
    @Override
    protected boolean containsThisFOPCtype(String marker) {
        return false;
    }

    @Override
    protected Literal convertEquivalenceToImplication() {
        return this;
    }

    @Override
    protected Literal eliminateImplications() {
        return this;
    }

    @Override
    protected Sentence negate() { // In NOTs, the SECOND argument is used.
        return stringHandler.getConnectedSentence(null, stringHandler.getConnectiveName("not"), this).setWeightOnSentence(wgtSentence);
    }

    @Override
    protected Sentence moveNegationInwards() { // Can't go in any further.
        return this;
    }

    @Override
    protected Literal skolemize(List<Variable> outerUniversalVars) {
        return this; // Can't go in any further.
    }

    @Override
    protected Literal distributeDisjunctionOverConjunction() {
        return this; // Can't go in any further.
    }

    @Override
    protected List<Clause> convertToListOfClauses() {
        List<Clause> result = new ArrayList<>(1);
        result.add(convertToClause(true)); // Convert allCollector of these to unnegated literals.
        return result;
    }

    @Override
    protected Clause convertToClause() {
        return convertToClause(true);
    }

    Clause convertToClause(boolean isaPositiveLiteral) {
        double literalWgt = wgtSentence;
        wgtSentence = Sentence.maxWeight; // Move the literal's weight out to the clause that "wraps" it.
        return (Clause) stringHandler.getClause(this, isaPositiveLiteral).setWeightOnSentence(literalWgt);
    }

    public Function convertToFunction(HandleFOPCstrings stringHandler) {
        FunctionName functionName = stringHandler.getFunctionName(predicateName.name);
        return stringHandler.getFunction(functionName, arguments, argumentNames, null);
    }

    @Override
    public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
        return toString(precedenceOfCaller, bindingList);   // TODO have this use toPrettyString in the recursive calls.
    }

    @Override
    public String toString(int precedenceOfCaller, BindingList bindingList) {
        String result = returnWeightString();
        boolean hasArgNames = (argumentNames != null);

        String pNameString = predicateName.toString();
        if (predicateName.printUsingInFixNotation && numberArgs() == 2) {
            int precedence = HandleFOPCstrings.getLiteralPrecedence_static(predicateName);
            if (precedenceOfCaller < precedence) {
                return result + "(" + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + " " + pNameString + " " + (hasArgNames ? argumentNames.get(1) + "=" : "") + arguments.get(1).toString(precedence, bindingList) + ")";
            }
			return result + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + " " + pNameString + " " + (hasArgNames ? argumentNames.get(1) + "=" : "") + arguments.get(1).toString(precedence, bindingList);
        }
        if (predicateName.printUsingInFixNotation && numberArgs() == 3 && predicateName.name.equalsIgnoreCase("then")) {
            int precedence = HandleFOPCstrings.getLiteralPrecedence_static(predicateName);
            if (precedenceOfCaller < precedence) {
                return result + "(" + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + " " + pNameString + " " + (hasArgNames ? argumentNames.get(1) + "=" : "") + arguments.get(1).toString(precedence, bindingList) + " else " + (hasArgNames ? argumentNames.get(2) + "=" : "") + arguments.get(2).toString(precedence, bindingList) + ")";
            }
			return result + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + " " + pNameString + " " + (hasArgNames ? argumentNames.get(1) + "=" : "") + arguments.get(1).toString(precedence, bindingList) + " else " + (hasArgNames ? argumentNames.get(2) + "=" : "") + arguments.get(2).toString(precedence, bindingList);
        }

        result += pNameString;
        if (arguments == null) {
            return result;
        }
        return result + restOfToString(bindingList);
    }

    @Override
    public boolean isDefiniteClause() {
        return true;
    }

    @Override
    public boolean isDefiniteClauseFact() {
        return true;
    }

    @Override
    public boolean isDefiniteClauseRule() {
        return false;
    }

    @Override
    public Literal getDefiniteClauseHead() {
        return this;
    }

    @Override
    public Literal getDefiniteClauseFactAsLiteral() throws IllegalStateException {
        return this;
    }

    @Override
    public Clause getDefiniteClauseAsClause() throws IllegalStateException {
        return getStringHandler().getClause(this, true);
    }

    @Override
    public List<Literal> getDefiniteClauseBody() {
        return Collections.EMPTY_LIST;
    }

    public BindingList unifyDefiniteClause(DefiniteClause otherClause, BindingList bindingList) {
        if (!otherClause.isDefiniteClauseFact()) {
            return null;
        }

        Literal otherHead = otherClause.getDefiniteClauseFactAsLiteral();

        if (predicateName != otherHead.predicateName) {
            return null;
        }

        if (numberArgs() != otherHead.numberArgs()) {
            return null;
        }

        if (bindingList == null) {
            bindingList = new BindingList();
        }

        return Unifier.UNIFIER.unify(this, otherHead, bindingList);
    }

    public List<Term> getArguments() {
        return arguments == null ? Collections.EMPTY_LIST : arguments;
    }

    public Term getArgument(int i) {
        return arguments.get(i);
    }

    public void setArguments(List<Term> arguments) {
        this.arguments = arguments;
        setNumberArgs();
        sortArgumentsByName();
    }

    public List<String> getArgumentNames() {
        return argumentNames;
    }

    public void addArgument(Term term) {
        if (argumentNames != null) {
            Utils.error("Current arguments are named, so you need to pass in term and name for '" + this + "'.");
        }
        if (arguments == null) {
        	arguments = new ArrayList<>(1);
        }
        arguments.add(term);
        setNumberArgs();
    }

    public void addArgument(Term term, String name) {
        arguments.add(term);
        argumentNames.add(name);
        setNumberArgs();
        sortArgumentsByName();
    }

    public void removeArgument(Term term) {
        if (argumentNames != null) {
            Utils.error("Current arguments are named, so you need to pass in term and name for '" + this + "'.");
        }
        if (!arguments.remove(term)) {
            Utils.error("Could not remove '" + term + "' from '" + this + "'.");
        }
        setNumberArgs();
    }

    private void removeArgument(Term term, String name) {
        if (!arguments.remove(term)) {
            Utils.error("Could not remove '" + term + "' from '" + this + "'.");
        }
        if (!argumentNames.remove(name)) {
            Utils.error("Could not remove '" + name + "' from '" + this + "'.");
        }
        setNumberArgs();
        sortArgumentsByName();
    }

    private void sortArgumentsByName() {
        if (argumentNames == null) {
            return;
        }
        int numbArgs = numberArgs();
        if (Utils.getSizeSafely(argumentNames) != numbArgs) {
            Utils.error("# of arguments (" + numbArgs + ") does not equal number of argument names ("
                    + Utils.getSizeSafely(argumentNames) + "):\n   args = " + arguments + "\n  names = " + argumentNames + "\n    lit = " + this);
        }
        if (numbArgs < 2) {
            return;
        }
        List<NamedTerm> namedTerms = new ArrayList<>(numbArgs);
        Set<String> namesSeen = new HashSet<>(4);
        for (int i = 0; i < numbArgs; i++) {
            String argName = argumentNames.get(i);
            if (namesSeen.contains(argName)) {
                Utils.error("Cannot have duplicate names (" + argName + "): " + argumentNames);
            }
            if ( argName != null ) namesSeen.add(argName);
            namedTerms.add(new NamedTerm(arguments.get(i), argName));
        }
        namedTerms.sort(NamedTerm.comparator);
        arguments.clear();
        argumentNames.clear();
        for (NamedTerm nt : namedTerms) {
            arguments.add(nt.term);
            argumentNames.add(nt.name);
        }
    }

    /* Returns all possible TypeSpecs for this literal.
     *
     * If typeSpec variable is set, only that type
     */
    public List<TypeSpec> getTypeSpecs() {

        List<TypeSpec> result;

        List<PredicateSpec> predTypeSpec = predicateName.getTypeList();

        if ( Utils.getSizeSafely(predTypeSpec) > 0 ) {
            PredicateSpec ps = predTypeSpec.get(0);
            result = ps.getTypeSpecList();
        }
        else {
            result = new ArrayList<>();
            for (Term term : getArguments()) {
                result.add(term.getTypeSpec());
            }
        }
        
        return result;
    }

    public PredicateNameAndArity getPredicateNameAndArity() {
        return stringHandler.getPredicate(predicateName, getArity());
    }

    @Override
    public <Return, Data> Return accept(SentenceVisitor<Return, Data> visitor, Data data) {
        return visitor.visitLiteral(this, data);
    }

    @Override
    public Clause getNegatedQueryClause() throws IllegalArgumentException {

        Clause result;

        result = stringHandler.getClause(null, Collections.singletonList(this));

        return result;
    }

	   @Override
    public int countVarOccurrencesInFOPC(Variable v) {
        int total = 0;
        if (arguments != null) {
            for (Term arg : arguments) {
                total += arg.countVarOccurrencesInFOPC(v);
            }
        }
        return total;
    }

}
