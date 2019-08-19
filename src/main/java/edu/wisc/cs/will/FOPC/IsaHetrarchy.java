package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

public class IsaHetrarchy {	
	/*
	 * Written by shavlik.
	 */

	protected final static int debugLevel = 0; // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).
	
	private HandleFOPCstrings stringHandler; // Have a back pointer to the owner of this ISA hetrarchy.
	
	private static final String WILL_ANYTHING_TYPE_NAME = "willAnything";
	private static final String WILL_LIST_TYPE_NAME     = "willList";
	private static final String WILL_NUMBER_TYPE_NAME   = "willNumber";
	private static final String WILL_BOOLEAN_TYPE_NAME  = "willBoolean";
	private static final String WILL_TOKEN_TYPE_NAME    = "willToken";
	private static final String WILL_ATOMIC_TYPE_NAME   = "willAtomic";
	private Type willNumberType;

	private   Type                        rootOfISA;
	private   Map<Type,List<Type>>        isaHetrarchy; // Only LEAF nodes can be ISA more than one type.  EXTENDED (7/09) TO A HETRARCHY.
	private   Map<Type,List<Type>>        reverseIsaHetrarchy;  // Allow quick lookup of the CHILDREN nodes.
	private Map<String,Type>            isaTypeHash; // Used to convert strings to types.  THIS IS NOT USED TO STORE PARENTS POINTERS IN THE ISA Hetrarchy (isaHetrarchy is used for this).
	
	IsaHetrarchy(HandleFOPCstrings stringHandler) {
		
		this.stringHandler  = stringHandler;

		isaTypeHash         = new HashMap<>(16);
		isaHetrarchy        = new HashMap<>(4);  // Might not have any of these, but go ahead and make the hash map.
		reverseIsaHetrarchy = new HashMap<>(4);  // Ditto.
		rootOfISA           = getIsaType(WILL_ANYTHING_TYPE_NAME); // Be sure to use getIsaType() so the proper case is used.
		reverseIsaHetrarchy.put(rootOfISA, new ArrayList<>(32));
		Type willListType = getIsaType(WILL_LIST_TYPE_NAME);
		Type willAtomicType = getIsaType(WILL_ATOMIC_TYPE_NAME);
		willNumberType  = getIsaType(WILL_NUMBER_TYPE_NAME);
		Type willBooleanType = getIsaType(WILL_BOOLEAN_TYPE_NAME);
		Type willTokenType = getIsaType(WILL_TOKEN_TYPE_NAME);
		addISA(willListType,    rootOfISA);
		addISA(willAtomicType,  rootOfISA);
		addISA(willNumberType,  getIsaType(WILL_ATOMIC_TYPE_NAME));
		addISA(willBooleanType, getIsaType(WILL_ATOMIC_TYPE_NAME));
		addISA(willTokenType,   getIsaType(WILL_ATOMIC_TYPE_NAME));
		
		if (debugLevel > 2) {
			Utils.println("%         isa: " + Utils.limitLengthOfPrintedList(isaHetrarchy,        25));
			Utils.println("% reverse isa: " + Utils.limitLengthOfPrintedList(reverseIsaHetrarchy, 25));
			Utils.waitHere();
		}
	}

	public List<Type> getAllKnownTypesForThisTerm(Term term) {
		if (term instanceof Variable) { return null; }
		if (term instanceof Function) { return null; }
		if (term instanceof StringConstant) {
			StringConstant sc = (StringConstant) term;
			String      value = sc.getName();
			Type lookup = isaTypeHash.get(value);
			if (lookup == null) { return null; }
			return isaHetrarchy.get(lookup);
		}
		if (term instanceof NumericConstant) {
			NumericConstant nc = (NumericConstant) term;
			String      value = nc.getName();
			Type lookup = isaTypeHash.get(value);
			if (lookup == null) { 
				List<Type> result = new ArrayList<>(1);
				result.add(willNumberType);
				return result;
			}
			List<Type> result = isaHetrarchy.get(lookup);
			if (result != null) {
				if (result.contains(willNumberType)) { return result; }
				// Else see if this is already known via an ISA.
				for (Type knownType : result) {
					if (isa(knownType, willNumberType)) { return result; }
				}
			}
			List<Type> result2 = new ArrayList<>(Utils.getSizeSafely(result) + 1);
			if (result != null) { result2.addAll(result); }
			result2.add(willNumberType);
			return result2;
		}
		return null;
	}
	
	public boolean okToAddToIsa(Type child, Type parent) {
		if (isa(child, parent)) { return false; }
		return !isa(parent, child);
	}
	
	public void addISA(Type child, Type parent) {
		if (debugLevel > 1) { Utils.println("addISA(" + child + ", " + parent + ")."); }
		if (isa(child, parent)) { return; }  // Some callers check this and the following line, but not all do, so play it safe.
		if (isa(parent, child)) { Utils.error("Cannot add '" + child + " ISA " + parent + "' because the reverse is already the case."); }
		List<Type> otherParents = isaHetrarchy.get(child);
		
		if (otherParents != null) {
			ListIterator<Type> parentIter = otherParents.listIterator();
			while (parentIter.hasNext()) { // Need to do this for ALL parents.
				Type otherParent = parentIter.next();
				if        (isa(otherParent, parent)) {
					// Want to add isa(A,C) but already have isa(A,B) and isa(B,C).
					Utils.waitHere("This should not occur since then would already be ISA.");
					return;
				} else if (isa(parent, otherParent)) {
					// Want to add isa(A,C) but already have isa(A,B) and isa(C,B),
					// so can remove the A-B link.  HOWEVER CAN ONKY DO THIS BECAUSE A-B IS A *DIRECT* LINK.  OTHERWISE MIGHT LOSE SOME ISA's.
					if (debugLevel > 1) { Utils.println("removeISA(" + child + ", " + otherParent + ") because isa(" + parent + ", " + otherParent + ")."); }
					parentIter.remove(); // Need to use this instead of removeISA() due to the way Java iteration works.
					removeFromReverseISA(otherParent, child);
				}
			}
		}
		else {
			otherParents = new ArrayList<>(1);
		}
		isaHetrarchy.put(child, otherParents);
		otherParents.add(parent);		
		addToReverseISA(parent, child);	
		if (!isaHetrarchy.containsKey(parent)) { addISA(parent, rootOfISA); }
		if (debugLevel > 1) { Utils.println("addISA(" + child + ", " + parent + "): isa = " + Utils.limitLengthOfPrintedList(isaHetrarchy, 25)); }
	}
	
	/*
	 * @return All the children of this type in the type Hetrarchy.
	 */
	private List<Type> reverseIsa(Type parent) {
		return reverseIsaHetrarchy.get(parent);
	}
	public Type getIsaType(Term constant) {	// TODO - clean up and put interfaces to all public's in the string handler?
		return getIsaType(constant.toString());
	}
	public Type getIsaType(String name) {	// Might want to require types to be the same case as constants, but seems OK to deal with these in a case-independent manner.	
		String stdName     = (stringHandler.getStringsAreCaseSensitive() ? name : name.toLowerCase()); // Hash case-independently if that is how strings are handled..
		Type   hashedValue = isaTypeHash.get(stdName);
		if (hashedValue != null) { return hashedValue; }
		Type result = new Type(name, stringHandler); // Store using the first version seen.
		isaTypeHash.put(stdName, result);
		return result;		
	}

	void addISA(Term child, Type parentType) {
		stringHandler.addConstantToISA(child, getIsaType(child), parentType); // Need to register this constant.
	}

	private void addToReverseISA(Type parent, Type child) {
		List<Type> children = reverseIsa(parent);
		
		if (children != null) {
			if (children.contains(child)) { return; } // Already there.
			children.add(child);
			}
		else {
			List<Type> newChildren = new ArrayList<>(1);
			newChildren.add(child);
			reverseIsaHetrarchy.put(parent, newChildren);
		}
	}

	// Only works for DIRECT child-parent links.
	private void removeFromReverseISA(Type parent, Type child) {
		Collection<Type> children = reverseIsa(parent);
		
		if (children != null) {
			if (children.contains(child)) {
				if (!children.remove(child)) { Utils.error("Could not remove '" + child + "' from " + Utils.limitLengthOfPrintedList(children, 10) + " of '" + parent + "'."); }
				return;
			}
		}
		Utils.println("%         isa: " + Utils.limitLengthOfPrintedList(isaHetrarchy));
		Utils.println("% reverse isa: " + Utils.limitLengthOfPrintedList(reverseIsaHetrarchy));
		Utils.println("% reverse children of '" + parent + "' are " + children);
		Utils.error("Cannot remove '" + child + "' from the reverse ISA of '" + parent + "'.");
	}

	// See if child ISA parent.
	public boolean isa(String child, String parent) {
		return isa(getIsaType(child), getIsaType(parent));
	}
	public boolean isa(Type child, String parent) {
		return isa(child, getIsaType(parent));
	}
	public boolean isa(String child, Type parent) {
		return isa(getIsaType(child), parent);
	}
	public boolean isa(Type child, Type parent) {
		return isa(child, parent, 0);
	}
	private boolean isa(Type child, Type parent, int depth) {
		if (depth > 100) { Utils.error("isa depth too deep? checking isa(" + child + "," + parent + ")  depth=" + depth); }
		if (child == parent) { return true; }
		List<Type> ancestors = isaHetrarchy.get(child);
		if (depth >  50) {
			for (int i = 0; i < depth; i++) { Utils.print(""); }
			Utils.println("  checking isa(" + child + "," + parent + ")  depth=" + depth + " ancestors=" + ancestors);
		}
		if (ancestors == null) {return false; }
		int depthPlus1 = depth + 1;
		for (Type ancestor : ancestors) if (isa(ancestor, parent, depthPlus1)) { return true; }
		return false;
	}

	// Collect all the instances of this type AND OF ITS CHILDREN.  A FRESH list is returned.
	public Set<Term> getAllInstances(Type thisType) {
		if (debugLevel > 3) { Utils.println("% knownConstantsOfThisType = " + Utils.limitLengthOfPrintedList(stringHandler.knownConstantsOfThisType, 50)); }
		
		// First get all the instances at this node.
		Set<Term> results = stringHandler.getConstantsOfExactlyThisTypeAsList(thisType);
		// Next collect all the instances beneath this node.
		Collection<Type> children = reverseIsa(thisType);  // Notice we need the REVERSE isa Hetrarchy here.	
		if (children != null) for (Type child : children) { 
			Set<Term> childrenInstances = getAllInstances(child);
			if (childrenInstances == null) { continue; }
			if (results == null) { results = new HashSet<>(4); }
			results.addAll(childrenInstances);
		}
		return results;
	}
}
