package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

import java.util.*;

public class IsaHetrarchy {	
	/*
	 * Written by shavlik.
	 */

	private final HandleFOPCstrings stringHandler; // Have a back pointer to the owner of this ISA hetrarchy.
	
	private static final String WILL_ANYTHING_TYPE_NAME = "willAnything";
	private static final String WILL_LIST_TYPE_NAME     = "willList";
	private static final String WILL_NUMBER_TYPE_NAME   = "willNumber";
	private static final String WILL_BOOLEAN_TYPE_NAME  = "willBoolean";
	private static final String WILL_TOKEN_TYPE_NAME    = "willToken";
	private static final String WILL_ATOMIC_TYPE_NAME   = "willAtomic";

	private final Type                        rootOfISA;
	private final Map<Type,List<Type>>        isaHetrarchy; // Only LEAF nodes can be ISA more than one type.  EXTENDED (7/09) TO A HETRARCHY.
	private final Map<Type,List<Type>>        reverseIsaHetrarchy;  // Allow quick lookup of the CHILDREN nodes.
	private final Map<String,Type>            isaTypeHash; // Used to convert strings to types.  THIS IS NOT USED TO STORE PARENTS POINTERS IN THE ISA Hetrarchy (isaHetrarchy is used for this).
	
	IsaHetrarchy(HandleFOPCstrings stringHandler) {
		
		this.stringHandler  = stringHandler;

		isaTypeHash         = new HashMap<>(16);
		isaHetrarchy        = new HashMap<>(4);  // Might not have any of these, but go ahead and make the hash map.
		reverseIsaHetrarchy = new HashMap<>(4);  // Ditto.
		rootOfISA           = getIsaType(WILL_ANYTHING_TYPE_NAME); // Be sure to use getIsaType() so the proper case is used.
		reverseIsaHetrarchy.put(rootOfISA, new ArrayList<>(32));
		Type willListType = getIsaType(WILL_LIST_TYPE_NAME);
		Type willAtomicType = getIsaType(WILL_ATOMIC_TYPE_NAME);
		Type willNumberType = getIsaType(WILL_NUMBER_TYPE_NAME);
		Type willBooleanType = getIsaType(WILL_BOOLEAN_TYPE_NAME);
		Type willTokenType = getIsaType(WILL_TOKEN_TYPE_NAME);
		addISA(willListType,    rootOfISA);
		addISA(willAtomicType,  rootOfISA);
		addISA(willNumberType,  getIsaType(WILL_ATOMIC_TYPE_NAME));
		addISA(willBooleanType, getIsaType(WILL_ATOMIC_TYPE_NAME));
		addISA(willTokenType,   getIsaType(WILL_ATOMIC_TYPE_NAME));
	}

	public List<Type> getAllKnownTypesForThisTerm(Term term) {
		if (term instanceof Variable) { return null; }
		if (term instanceof Function) { return null; }
		if (term instanceof StringConstant) {
			StringConstant sc = (StringConstant) term;
			String      value = sc.getName();
			Type lookup = isaTypeHash.get(value);
			if (lookup == null) {
				return null;
			} else {
				throw new RuntimeException("Deprecated + Should not be possible.");
			}
		}
		return null;
	}
	
	public boolean okToAddToIsa(Type child, Type parent) {
		if (isa(child, parent)) {
			return false;
		}
		return !isa(parent, child);
	}
	
	public void addISA(Type child, Type parent) {
		if (isa(child, parent)) { return; }  // Some callers check this and the following line, but not all do, so play it safe.
		if (isa(parent, child)) { Utils.error("Cannot add '" + child + " ISA " + parent + "' because the reverse is already the case."); }
		List<Type> otherParents = isaHetrarchy.get(child);
		
		if (otherParents != null) {
			for (Type otherParent : otherParents) { // Need to do this for ALL parents.
				if (isa(otherParent, parent)) {
					throw new RuntimeException("Deprecated + Should not be possible.");
				} else if (isa(parent, otherParent)) {
					throw new RuntimeException("Deprecated + Should not be possible.");
				}
			}
		} else {
			otherParents = new ArrayList<>(1);
		}
		isaHetrarchy.put(child, otherParents);
		otherParents.add(parent);		
		addToReverseISA(parent, child);	
		if (!isaHetrarchy.containsKey(parent)) { addISA(parent, rootOfISA); }
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
		Type result = new Type(name); // Store using the first version seen.
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
