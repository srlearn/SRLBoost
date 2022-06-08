package edu.wisc.cs.will.FOPC;


import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

/*
 * @author shavlik
 *
 * This class is used to hold LISTS (since List is a standard Java construct, using the Lisp name of "cons[tructed] cell").
 * See http://en.wikipedia.org/wiki/Lisp_programming_language for more information.
 *
 */
public class ConsCell extends Function implements Iterable<Term> {

    ConsCell(HandleFOPCstrings stringHandler, FunctionName functionName, TypeSpec typeSpec) {
        super(stringHandler, functionName, typeSpec); // This will set this.stringHandler.
        if (!functionName.name.equalsIgnoreCase("consCell")) {
            Utils.error("The name of a ConsCell cannot be: " + functionName);
        }
    }

    ConsCell(HandleFOPCstrings stringHandler) {
        super(stringHandler, stringHandler.getFunctionName("consCell"), null); // The empty cons cell is 'nil'.
    }

    ConsCell(HandleFOPCstrings stringHandler, Term firstTerm, TypeSpec typeSpec) {
        super(stringHandler, stringHandler.getFunctionName("consCell"), typeSpec);
        ConsCell nil = stringHandler.getNil();
        List<Term> arguments2 = new ArrayList<>(2);
        arguments2.add(firstTerm);
        arguments2.add(nil);
        setArguments(arguments2);

    }

    ConsCell(HandleFOPCstrings stringHandler, Term firstTerm, Term restTerm, TypeSpec typeSpec) {
        super(stringHandler, stringHandler.getFunctionName("consCell"), typeSpec);
        List<Term> arguments2 = new ArrayList<>(2);
        arguments2.add(firstTerm);
        arguments2.add(restTerm);
        setArguments(arguments2);
        if (firstTerm == null || restTerm == null) {
            Utils.error("Cannot have firstTerm=null or restTerm=null in a list.");
        }
    }

    ConsCell(HandleFOPCstrings stringHandler, FunctionName functionName, List<Term> arguments, List<String> argumentNames, TypeSpec typeSpec) {
        this(stringHandler, functionName, typeSpec);
        if (!functionName.name.equalsIgnoreCase("consCell")) { // Redundant here, but keep for now.
            Utils.error("The name of a ConsCell cannot be: " + functionName);
        }
        this.setArguments(arguments);
        this.setArgumentNames(argumentNames);
        // Allow either to be null (e.g., a 'bare copy' might be being made).
        if (arguments != null && argumentNames != null && Utils.getSizeSafely(arguments) != Utils.getSizeSafely(argumentNames)) {
            Utils.error("Have " + arguments + " and " + argumentNames + " - number of arguments and number of names must match.");
        }
    }

    // Needed for proper copying.  I.e., need a ConsCell and not a Function.
    private Function getBareCopy() {
        if (this == stringHandler.getNil()) {
            return this;
        }
        else {
            return stringHandler.getConsCell(functionName, typeSpec);
        }
    }

    @Override
    public Function getBareCopy(List<Term> newArguments) {
        Function f = getBareCopy();
        f.setArguments(newArguments);
        return f;
    }

    @Override
    public Function copy(boolean recursiveCopy) {
        if (this == stringHandler.getNil()) {
            return this;
        }
        else {
            return super.copy(recursiveCopy);
        }
    }

    @Override
    public Function copy2(boolean recursiveCopy, BindingList bindingList) {
        if (this == stringHandler.getNil()) {
            return this;
        }
        else {
            return super.copy2(recursiveCopy, bindingList);
        }
    }

    public List<Term> convertConsCellToList() { // Only convert the "top-level" (i.e., no recursion on first).

        ConsCell c = this;
        while (c != null && !c.isNil()) {
            Term first = first();

            Term rest = c.rest();
            if (rest instanceof ConsCell) {
                c = (ConsCell) rest;
            }
            else {
                c = null;
            }
        }

        if (numberArgs() == 0) {
            return new ArrayList<>();
        }
        Term first = getArgument(0);
        ConsCell rest = ensureIsaConsCell(stringHandler, getArgument(1)); // ConsCells should never have one argument.  This will crash on 'dotted pairs' (since 'rest' isn't a ConsCell) but we're not allowing them.
        List<Term> result = new ArrayList<>(length());

        while (true) {
            result.add(first);
            if (rest.numberArgs() == 0) {
                return result;
            }
            first = rest.getArgument(0);
            rest = ensureIsaConsCell(stringHandler, rest.getArgument(1));
        }
    }

    static <T> ConsCell convertListToConsCell(HandleFOPCstrings stringHandler, List<T> items) {
        if (items == null) {
            return null;
        }
        ConsCell result = stringHandler.getNil();
        if (items.isEmpty()) {
            return result;
        }

        for (T item : items) { // Wrap non-terms in ObjectAsTerm instances.  Push on front.
            if (item instanceof Term) {
                result = stringHandler.getConsCell((Term) item, result, null);
            }
            else {
                result = stringHandler.getConsCell(stringHandler.getObjectAsTerm(item), result, null);
            }
        }
        return result.reverse();  // TODO - devise a way to avoid the need to reverse.
    }

    // This is written iteratively instead of recursively to prevent stack overflows (which have happened).
    boolean memberViaEq(Term term) {
        for (Term element : this) {
            if (element == term) {
                return true;
            }
        }
        return false;
    }

    boolean memberViaEquals(Term term) {
        for (Term element : this) {
            if (element.equals(term)) {
                return true;
            }
        }
        return false;
    }

    public int position(Term term) { // Starts from 0, -1 means 'failed' Ignore matching in a possible 'dotted pair.'
        if (numberArgs() == 0) {
            return -1;
        }
        int counter = 0;
        Term first = getArgument(0);
        if (term.equals(first)) {
            return 0;
        }
        Term restRaw = getArgument(1);
        if (!Function.isaConsCell(restRaw)) {
            return -1;
        }
        ConsCell rest = ensureIsaConsCell(stringHandler, getArgument(1)); // ConsCells should never have one argument.

        while (true) {
            if (term.equals(first)) {
                return counter;
            }
            if (rest.numberArgs() == 0) {
                return -1;
            }
            first = rest.getArgument(0);
            rest = ensureIsaConsCell(stringHandler, rest.getArgument(1));
            counter++;
        }
    }

    Term nth(int n) { // Return the nth item in this list.  Counting starts from 0. Return null if it doesn't exist.  Ignore matching in a possible 'dotted pair.'
        return getListElement(n);
    }

    public Term car() {
        return first();
    }

    public Term first() {
        if (numberArgs() == 0) {
            return null;
        }
        return getArgument(0);
    }

    public Term cdr() {
        return rest();
    }

    public Term rest() {
        Term result = null;
        if (numberArgs() >= 2) {
            result = getArgument(1);
        }
        return result;
    }

    public ConsCell push(Term term) { // Note: we are ignoring typeSpec here.  If needed, it'll need to be passed on as well.
        return stringHandler.getConsCell(term, this, null);
    }

    public void setCdr(Term cdr) {
        if (arguments == null) {
            arguments = new ArrayList<>();
            arguments.add(null); // Car is null...probably bad.
            arguments.add(cdr); // Usually this would be another ConsCell, but it could be a variable too.
        }
        else if (arguments.size() == 1) {
            arguments = new ArrayList<>();
            arguments.add(cdr);
        }
        else {
            arguments.set(1, cdr);
        }
    }

    public ConsCell remove(Term term) { // Remove ALL occurrences.  TODO write iterative version.
        if (numberArgs() == 0) {
            return this;
        }
        Term first = getArgument(0);
        ConsCell rest = ensureIsaConsCell(stringHandler, getArgument(1)).remove(term);
        if (first.equals(term)) {
            return rest;
        }
        return stringHandler.getConsCell(first, rest, null);
    }

    public boolean isNil() {
        return this == getStringHandler().getNil();
    }

    /* Return the length of this list.
     * This is written iteratively instead of recursively to prevent stack overflows (which have happened).
     */
    public int length() {
        ConsCell aCell = this;

        int length = 0;

        // ConsCells should always be length 2 with the
        // exception of the Nil ConsCell.  However, we
        // haven't been consistent so we need to do the
        // safety checks here...
        while (aCell.getArity() != 0) {

            length++;

            if (aCell.getArity() == 1) {
                break;
            }

            Term rest = aCell.getArgument(1);

            if (!(rest instanceof ConsCell)) {
                break;
            }

            // All other cases were handled with breaks,
            // so this must be a consCell.
            aCell = (ConsCell) rest;
        }

        return length;
    }

    @Override
    public BindingList variants(Term other, BindingList bindings) {

        if (!(other instanceof ConsCell)) {
            return null;
        }
        else {
            Term next1 = other;
            Term next2 = this;

            while (next2 != null && next1 != null) {

                if (next1 instanceof ConsCell && next2 instanceof ConsCell) {
                    ConsCell consCell1 = (ConsCell) next1;
                    ConsCell consCell2 = (ConsCell) next2;

                    Term car1 = consCell1.car();
                    Term car2 = consCell2.car();

                    if (car1 != car2 && (car1 == null || (bindings = car1.variants(car2, bindings) ) == null)) {
                        // The cars are different.  The logic above is messy, but standard logic to take account
                        // the possibility of one or both being null.
                        return null;
                    }

                    next1 = consCell1.cdr();
                    next2 = consCell2.cdr();
                }
                else if (next1 instanceof ConsCell || next2 instanceof ConsCell) {
                    // One is a consCell, the other isn't, so they aren't varients.
                    return null;
                }
                else {
                    // Neither are consCells, so just return whether they are varients.
                    return next1.variants(next2, bindings);
                }
            }

        }

        return bindings;
    }



    @Override
    public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {

        List<Variable> result = null;

        Term currentTerm = this;

        // ConsCells should always be length 2 with the
        // exception of the Nil ConsCell.  However, we
        // haven't been consistent so we need to do the
        // safety checks here...
        while (currentTerm != null) {

            if (currentTerm instanceof ConsCell) {
                ConsCell aCell = (ConsCell) currentTerm;

                // This is a terminating condition...
                if (aCell.getArity() == 0) {
                    currentTerm = null;
                }
                else if (aCell.getArity() == 1) {
                    Term aTerm = aCell.car();
                    result = addToList(result, aTerm.collectFreeVariables(boundVariables));
                    currentTerm = null;
                }
                else if (aCell.getArity() == 2) {
                    Term aTerm = aCell.car();
                    result = addToList(result, aTerm.collectFreeVariables(boundVariables));
                    currentTerm = aCell.cdr();
                }
            }
            else {
                // We hit the end of the list and it isn't a ConsCell.  This should probably
                // be a variable, but who knows...
                result = addToList(result, currentTerm.collectFreeVariables(boundVariables));
                currentTerm = null;
            }

        }

        return result == null ? Collections.EMPTY_LIST : result;
    }

    @Override
    public boolean equals(Object object) {

        if (this == object) {
            return true;
        }
        if (!(object instanceof ConsCell)) {
            return false;
        }
        ConsCell that = (ConsCell) object;

        Term thisTerm = this;
        Term thatTerm = that;

        // ConsCells should always be length 2 with the
        // exception of the Nil ConsCell.  However, we
        // haven't been consistent so we need to do the
        // safety checks here...
        while (thisTerm != null && thatTerm != null) {

            if (thisTerm instanceof ConsCell && thatTerm instanceof ConsCell) {
                ConsCell thisCell = (ConsCell) thisTerm;
                ConsCell thatCell = (ConsCell) thatTerm;

                Term thisCar = null;
                Term thatCar = null;

                // This is a terminating condition...
                if (thisCell.getArity() == 0) {
                    thisTerm = null;
                }
                else if (thisCell.getArity() == 1) {
                    thisCar = thisCell.car();
                    thisTerm = null;
                }
                else if (thisCell.getArity() == 2) {
                    thisCar = thisCell.car();
                    thisTerm = thisCell.cdr();
                }

                if (thatCell.getArity() == 0) {
                    thatTerm = null;
                }
                else if (thatCell.getArity() == 1) {
                    thatCar = thatCell.car();
                    thatTerm = null;
                }
                else if (thatCell.getArity() == 2) {
                    thatCar = thatCell.car();
                    thatTerm = thatCell.cdr();
                }

                if (!Objects.equals(thisCar, thatCar)) {
                    // The Car's aren't the same, so return false;
                    return false;
                }
            }
            else if (thisTerm instanceof ConsCell || thatTerm instanceof ConsCell) {
                // One of the terms is a consCell and the other isn't.  They aren't equal.
                return false;
            }
            else {
                // We have two non-consCell terms, both at the end of the list...
                return thisTerm.equals(thatTerm);
            }

        }

        // We are at the end of one of the lists.
        // If the lists are equal, both thisTerm & thatTerm should be null;
        return thisTerm == null && thatTerm == null;
    }

    @Override
    public int hashCode() {
        int hash = 17;

        Term currentTerm = this;

        // ConsCells should always be length 2 with the
        // exception of the Nil ConsCell.  However, we
        // haven't been consistent so we need to do the
        // safety checks here...
        while (currentTerm != null) {

            if (currentTerm instanceof ConsCell) {
                ConsCell aCell = (ConsCell) currentTerm;

                Term car = null;
                // This is a terminating condition...
                if (aCell.getArity() == 0) {
                    currentTerm = null;
                }
                else if (aCell.getArity() == 1) {
                    car = aCell.car();
                    currentTerm = null;
                }
                else if (aCell.getArity() == 2) {
                    car = aCell.car();
                    currentTerm = aCell.cdr();
                }

                if (car != null) {
                    hash = hash * 17 + car.hashCode();
                }
            }
            else {
                // We hit the end of the list and it isn't a ConsCell.  This should probably
                // be a variable, but who knows...
                hash = hash * 17 + currentTerm.hashCode();
                currentTerm = null;
            }
        }

        return hash;
    }

    /* Returns the ith element if the consCell was treated as a list.
     */
    private Term getListElement(int index) {
        Term currentTerm = this;

        int currentIndex = 0;

        Term result = null;

        // ConsCells should always be length 2 with the
        // exception of the Nil ConsCell.  However, we
        // haven't been consistent so we need to do the
        // safety checks here...
        while (currentTerm != null) {

            if (currentIndex == index) {

                if (currentTerm instanceof ConsCell) {
                    ConsCell aCell = (ConsCell) currentTerm;

                    if (aCell.getArity() == 0) {
                        throw new IndexOutOfBoundsException("ConsCell end-of-list encountered at " + currentIndex + ".  Requested index " + index + ".");
                    }
                    else {
                        result = aCell.car();
                    }
                }
                else {
                    result = currentTerm;
                }

                currentTerm = null;
            }
            else {
                if (currentTerm instanceof ConsCell) {
                    ConsCell aCell = (ConsCell) currentTerm;

                    if (aCell.getArity() != 2) {
                        throw new IndexOutOfBoundsException("ConsCell end-of-list encountered at " + currentIndex + ".  Requested index " + index + ".");
                    }
                    else {
                        currentTerm = aCell.cdr();
                    }
                }
                else {
                    throw new IndexOutOfBoundsException("ConsCell end-of-list encountered at " + currentIndex + ".  Requested index " + index + ".");
                }
            }

            currentIndex++;
        }

        if (result == null) {
            throw new IndexOutOfBoundsException("ConsCell end-of-list encountered at " + currentIndex + ".  Requested index " + index + ".");
        }

        return result;
    }

    public ConsCell reverse() {
        if (numberArgs() == 0) {
            return this;
        }
        ConsCell answer = stringHandler.getNil(); // Answer is a stack upon which we push things in order to reverse the list.

        Term first = getArgument(0);
        ConsCell rest = ensureIsaConsCell(stringHandler, getArgument(1)); // ConsCells should never have one argument.  This will crash on 'dotted pairs' (since 'rest' isn't a ConsCell) but we're not allowing them.

        while (true) {
            answer = stringHandler.getConsCell(first, answer, null);
            assert rest != null;
            if (rest.numberArgs() == 0) {
                return answer;
            }
            first = rest.getArgument(0);
            rest = ensureIsaConsCell(stringHandler, rest.getArgument(1));
        }
    }

    public static ConsCell append(ConsCell a, ConsCell b) {
        return a.append(b);
    }

    static ConsCell union(ConsCell a, ConsCell b) {
        if (a.length() <= b.length()) { // Walk through the smaller set.
            return a.union(b);
        }
        return b.union(a);
    }

    static ConsCell intersection(ConsCell a, ConsCell b) {
        if (a.length() <= b.length()) { // Walk through the smaller set.
            return a.intersection(b);
        }
        return b.intersection(a);
    }

    // TODO - write an iterative version of this.
    // Note: this is NOT an in-place copy.
    public ConsCell append(ConsCell other) { // TODO: 'typeSpec' is not properly propagated, but wait until we see if that is needed.
        if (numberArgs() == 0) {
            return other;
        }
        if (isaConsCell(getArgument(1))) {
            return stringHandler.getConsCell(getArgument(0), Objects.requireNonNull(ensureIsaConsCell(stringHandler, getArgument(1))).append(other), null);
        }
        Utils.error("Can't yet handle 'dotted-pair' type of lists.");
        return null;
    }

    @Override
    public <Return, Data> Return accept(TermVisitor<Return, Data> visitor, Data data) {
        return visitor.visitConsCell(this, data);
    }

    ConsCell intersection(ConsCell other) {
        if (this == other) {
            return this;
        }
        if (other == null) {
            return null;
        }

        // Collect the items in THIS that are in OTHER.
        List<Term> result = new ArrayList<>(1); // Assume no duplicates in 'this'.
        if (this.numberArgs() == 0) {
            return convertListToConsCell(stringHandler, result);
        }
        Term       first  = getArgument(0);
        ConsCell   rest   = ensureIsaConsCell(stringHandler, getArgument(1));
        boolean continueWhile = true;
        while (continueWhile) {
            if (other.memberViaEquals(first)) {
                result.add(first);
            }
            assert rest != null;
            if (rest.numberArgs() < 1) {
                continueWhile = false;
            } else {
                first = rest.getArgument(0);
                rest = ensureIsaConsCell(stringHandler, rest.getArgument(1));
            }
        }
        return convertListToConsCell(stringHandler, result); // Just use the original typeSpec (TODO - what if OTHER doesn't match?).
    }

    ConsCell union(ConsCell other) { // NOTE: since a Set is used, the order of the result is arbitrary.
        if (this == other) {
            return this;
        }
        if (other == null) {
            return null;
        }

        // Collect the items in THIS that are in OTHER.
        Set<Term> result = new HashSet<>(4);
        Term      first  = getArgument(0);
        ConsCell  rest   = ensureIsaConsCell(stringHandler, getArgument(1));
        result.addAll(other.convertConsCellToList()); // Collect everything in other.
        boolean continueWhile = true;
        while (continueWhile) {
            result.add(first);
            assert rest != null;
            if (rest.numberArgs() < 1) {
                continueWhile = false;
            } else {
                first = rest.getArgument(0);
                rest = ensureIsaConsCell(stringHandler, rest.getArgument(1));
            }
        }
        List<Term> resultAsList = new ArrayList<>(result.size());
        resultAsList.addAll(resultAsList);
        return convertListToConsCell(stringHandler, resultAsList); // Just use the original typeSpec (TODO - what if OTHER doesn't match?).
    }

    // Cache this calculation to save time.
    @Override
    public boolean containsVariables() {
        if (cachedVariableCount < 0) {
            ConsCell aCell = this;

            // ConsCells should always be length 2 with the
            // exception of the Nil ConsCell.  However, we
            // haven't been consistent so we need to do the
            // safety checks here...
            while (aCell.getArity() != 0) {

                if (aCell.cachedVariableCount >= 0) {
                    // We ran into a cell that already has a
                    // cached value, so use that.
                    cachedVariableCount = aCell.cachedVariableCount;
                    break;
                }

                Term first = aCell.getArgument(0);
                if (first.containsVariables()) {
                    cachedVariableCount = 1;
                    break;
                }

                if (aCell.getArity() == 1) {
                    break;
                }

                Term rest = aCell.getArgument(1);

                if (!(rest instanceof ConsCell)) {
                    // rest should be a Variable here, but
                    // who knows.
                    cachedVariableCount = rest.containsVariables() ? 1 : 0;
                    break;
                }

                // All other cases were handled with breaks,
                // so this much be a consCell.
                aCell = (ConsCell) rest;
            }
        }

        return (cachedVariableCount > 0);
    }

    @Override
    public ConsCell applyTheta(Map<Variable, Term> theta) {

        // This code iterates through the consCells and
        // builds a new consCell on the fly.
        //
        // aCell points to the position in the current list.
        // result points to the head of the newly creately list.
        // tail points to the last cell in the new list.
        //
        // We walk through via aCell and append new nodes onto tail.
        //
        // As a side effect, this code will fix "broken" consCells
        // that are missing their Nil terminators (assuming the
        // list is at all arity 1 (which it should be).
        //
        // Bug: If a list's last item is a Variable, it is possible
        // to create an invalid list by binding the cdr of the
        // last cell of the newly created list to something other
        // than a consCell or variable.  That is probably bad,
        // but I don't know if an error should be thrown immediately
        // or if we should wait for things to break down later.

        ConsCell aCell = this;
        ConsCell result = this;
        ConsCell tail = null;

        if (!aCell.isNil() && aCell.getArity() > 0) {
            Term currentPosition = aCell;

            while (currentPosition != null) {
                if (currentPosition instanceof ConsCell) {
                    ConsCell cellPosition = (ConsCell) currentPosition;

                    if (cellPosition.isNil()) {
                        currentPosition = null; // We will fall out of the loop when we see a nil.
                    }
                    else {
                        // Call accept on the car() of the cellPosition cell.
                        Term newCar = cellPosition.car().applyTheta(theta);

                        ConsCell newCell = aCell.getStringHandler().getConsCell(newCar, aCell.getStringHandler().getNil(), cellPosition.getTypeSpec());
                        if (tail == null) {
                            // If we haven't starting constructing the cell chain, so record this first cell as the result.
                            result = newCell;
                        }
                        else {
                            // We are extending the tail, so set the cdr of tail and update tail to this.
                            tail.setCdr(newCell);
                        }
                        tail = newCell;

                        currentPosition = cellPosition.cdr();
                    }
                }
                else {
                    // The currentPosition is not a consCell.
                    // It is probably a variable since that is the only thing that
                    // should occur in a cdr position.

                    // Note...bad things could happen here...if current position
                    // is a variable (which it should be), and that variable maps
                    // to a non-variable && non-consCell then we just built a bad
                    // list.
                    Term newTerm = currentPosition.applyTheta(theta);
                    // We are extending the tail, so set the cdr of tail.
                    // If tail is null here...hmm...that shouldn't happen
                    // since we had a consCell coming in so the first iteration
                    // of the while loop had to create a tail.
                    tail.setCdr(newTerm);

                    // Now just drop out of the loop by setting currentPosition to null;
                    currentPosition = null;
                }
            }
        }

        return result;
    }

    // Play it safe and make sure any Functions that are really ConsCells are so represented.
    static ConsCell ensureIsaConsCell(HandleFOPCstrings stringHandler, Term expression) {
        if (expression instanceof ConsCell) {
            return (ConsCell) expression;
        }
        if (expression instanceof Function) {
            Function f = (Function) expression;
            FunctionName fName = f.functionName;

            if (fName.name.equalsIgnoreCase("conscell")) {
                return stringHandler.getConsCell(f);
            }
        }
        Utils.waitHere("Cannot convert to a cons cell: " + expression);
        return null;
    }

    @Override
    public String toString(int precedenceOfCaller, BindingList bindingList) {

        if (numberArgs() == 0) {
            return "[]";
        } // Could make this a constant, but probably not worth it.

        StringBuilder sb = new StringBuilder("[");

        appendToString(sb, precedenceOfCaller, bindingList);

        sb.append("]");

        return sb.toString();
    }

    private void appendToString(StringBuilder sb, int precedenceOfCaller, BindingList bindingList) {
        Term    term    = this;
        int     counter = 0; // Every N items, add a line feed.  TODO - have a flag to control this.
        boolean first   = true;

        while(term != null && term != stringHandler.getNil()) {

            if (term instanceof ConsCell) {
                ConsCell consCell = (ConsCell) term;
                Term car = consCell.car();

                if (!first) {
                    sb.append(", "); counter++; if (counter % 10 == 0) { sb.append("\n               "); } // Added by JWS to allow easier reading of lists, though note this is buggy if the printing started more than 15 chars in ...
                }
                sb.append(car.toString(precedenceOfCaller, bindingList));
                first = false;

                term = consCell.cdr();
            }
            else {
                sb.append("| ");
                sb.append(term.toString(precedenceOfCaller, bindingList));
                term = null;
            }
        }
    }

    @Override
    public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
        return newLineStarter + toString(precedenceOfCaller, bindingList);
    }

    private List<Variable> addToList(List<Variable> result, Collection<Variable> newFreeVariables) {
        if (newFreeVariables != null && !newFreeVariables.isEmpty()) {
            if (result == null) {
                result = new ArrayList<>(newFreeVariables);
            }
            else {
                result.addAll(newFreeVariables);
            }
        }

        return result;
    }

    public Iterator<Term> iterator() {
        return new ConsCellIterator(this);
    }

    /* Implements a Iterator over the elements of a ConsCell.
     *
     * This iterator returns all the elements of a ConsCell list.
     * However, [_,X] and [_|X] will both return the same sequence
     * of terms.
     */
    private static class ConsCellIterator implements Iterator<Term> {

        /* Pointer to the current head of the list.
         *
         * Normally, this will be a consCell.  However, in cases
         * such as [a,b|X], the currentPosition may actually point to the X.
         *
         * If null, iteration is complete and a NoSuchElement exception will be
         * thrown on a call to next().
         */
        Term currentPosition;

        Term next = null;

        ConsCellIterator(ConsCell consCell) {
            this.currentPosition = consCell;
        }

        public boolean hasNext() {
            setupNext();
            return next != null;
        }

        public Term next() {
            setupNext();

            if (next == null) {
                throw new NoSuchElementException();
            }

            Term result = next;
            next = null;

            return result;
        }

        public void remove() {
            throw new UnsupportedOperationException("Remove not supported.");
        }

        private void setupNext() {
            if (next == null) {
                if (currentPosition != null) {

                    Term newPosition;

                    if (currentPosition instanceof ConsCell) {
                        ConsCell aCell = (ConsCell) currentPosition;

                        // This is a terminating condition...
                        if (aCell.getArity() == 0) {
                            newPosition = null;
                        }
                        else if (aCell.getArity() == 1) {
                            next = aCell.car();
                            newPosition = null;
                        }
                        else if (aCell.getArity() == 2) {
                            next = aCell.car();
                            newPosition = aCell.cdr();
                        }
                        else {
                            throw new IllegalStateException("Encountered a ConsCell of length >= 3 will iterating!");
                        }
                    }
                    else {
                        // We hit the end of the list and it isn't a ConsCell.  This should probably
                        // be a variable, but who knows...
                        next = currentPosition;
                        newPosition = null;
                    }

                    currentPosition = newPosition;
                }
            }
        }
    }
}
