package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.ILP.InlineManager;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.*;


public class TreeStructuredTheory extends Theory {

	private static final long serialVersionUID = 1L;	
	private Literal                  headLiteral;
	private TreeStructuredTheoryNode root;
	private static int uniqueVarCounter = 1; // This is shared across multiple WILL threads, but that should be OK (if not, place counter in stringHander).
	private static final Map<String,StringConstant> flattenedVarMap = new HashMap<>(4); // Ditto.
	private final Set<Literal> uniqueFlattenedLiterals = new HashSet<>(4);
	
	private List<Clause> flattenedClauses;

	private TreeStructuredTheory(HandleFOPCstrings stringHandler) {
		super(stringHandler);
	}

	public TreeStructuredTheory(HandleFOPCstrings stringHandler, Literal headLiteral, TreeStructuredTheoryNode root) {
		this(stringHandler);
		this.headLiteral = headLiteral;
		this.root        = root;
	}
	
	private Variable getNextUniqueBodyVar() {
		return stringHandler.getGeneratedVariable("uniqueVar" + (uniqueVarCounter++), true); // We're counting on this being a unique name.
	}
	private StringConstant flattenedThisVar(Variable var) {
		StringConstant lookup = flattenedVarMap.get(var.getName());
		
		if (lookup != null) { return lookup; }
		
		lookup = convertNameToStringConstant(var.getName());
		flattenedVarMap.put(var.getName(), lookup);
		return lookup;
	}	
	// Drop an leading '?' if that is used to indicate a constant.
	private StringConstant convertNameToStringConstant(String name) {
		if (name == null || name.length() < 1) { return stringHandler.getStringConstant("emptyName"); }
		if (name.equals("_")) { return stringHandler.getStringConstant("underscore"); }
		if (stringHandler.doVariablesStartWithQuestionMarks()) {
			if (name.charAt(0) == '?') { return convertNameToStringConstant(name.substring(1)); } // The ?'s aren't stored, but check anyway.
			return stringHandler.getStringConstant(name); // I (JWS) left this here rather than combining the two IFs in case we need to do something different here.  
		}
		
		return stringHandler.getStringConstant(name);
	}

	Literal getHeadLiteral() {
		return headLiteral;
	}

	public void setRoot(TreeStructuredTheoryNode root) {
		this.root = root;
	}
	
	private String writeDotFormat() {
		TreeStructuredTheoryNode.counter=1;
		String result = "digraph G{ \n";
		result = result + root.writeDotFormat();
		result = result + "}\n";
		return result;
	}
	
	public TreeStructuredTheory convertToStandardTheory(InlineManager checkForInlinersAndSupportingClauses) {
		List<Clause> results = root.collectPathsToRoots(this);
		addAllMainClauses(results, checkForInlinersAndSupportingClauses); 
		return this;
	}
	
	public TreeStructuredTheory renameAllClausesWithUniqueBodyVariables() {
    	if (getClauses() != null) {
    		List<Clause> newClauses = new ArrayList<>(getClauses().size());
    		for (Clause c : getClauses()) if (c.isDefiniteClause()) {
				Collection<Variable> headVars = c.posLiterals.get(0).collectFreeVariables(null);
    			Collection<Variable> bodyVars = c.collectFreeVariables(headVars);
    			BindingList bl = new BindingList();
    			if (bodyVars != null) for (Variable bVar : bodyVars) if (!"_".equals(bVar.getName())) {
    				bl.addBinding(bVar, getNextUniqueBodyVar());
    			}
    			newClauses.add(c.applyTheta(bl.theta));
    		} else { Utils.error("Expecting a definite clause: " + c); }
    		setClauses(newClauses);
    	}
    	if (getSupportClauses() != null) {
    		List<Clause> newSupportClauses = new ArrayList<>(getSupportClauses().size() + 4);
    		for (Clause c : getSupportClauses()) if (c.isDefiniteClause()) {
				Collection<Variable> headVars = c.posLiterals.get(0).collectFreeVariables(null);
    			Collection<Variable> bodyVars = c.collectFreeVariables(headVars);
    			BindingList bl = new BindingList();
    			if (bodyVars != null) for (Variable bVar : bodyVars) if (!"_".equals(bVar.getName())) {
    				bl.addBinding(bVar, getNextUniqueBodyVar());
    			}
    			newSupportClauses.add(c.applyTheta(bl.theta));
    		} else { Utils.error("Expecting a definite clause: " + c); }
    		setSupportClauses(newSupportClauses);
    	}
		return this;
	}
	
	public TreeStructuredTheory createFlattenedClauses() {
    	if (getClauses() != null) {
    		List<Clause> newClauses = new ArrayList<>(getClauses().size());
    		for (Clause c : getClauses()) if (c.isDefiniteClause()) {
				Collection<Variable> bodyVars = c.collectFreeVariables(null); // Need to flatten the head variables as well.
    			BindingList bl = new BindingList();
    			if (bodyVars != null) for (Variable bVar : bodyVars){
    				bl.addBinding(bVar, flattenedThisVar(bVar));
    			}
    			Clause finalC = c.applyTheta(bl.theta);
    			newClauses.add(finalC);
    			addToUniqueFlattenedLiterals(finalC.negLiterals);
    		} else { Utils.error("Expecting a definite clause: " + c); }
    		flattenedClauses = newClauses;
    	}
		return this;
	}
	
	private void addToUniqueFlattenedLiterals(Collection<Literal> lits) {
		if (lits == null) { return; }
		for (Literal lit : lits) if (lit.predicateName != stringHandler.cutLiteral.predicateName)  {
			uniqueFlattenedLiterals.add(lit);
		}
	}

	private String getFlattenedClauseStrings() {
		if (flattenedClauses == null) { return ""; }
		StringBuilder result = new StringBuilder("\n% The flattened versions of these clauses:\n\n");
		int counter = 1;
		for (Clause c : flattenedClauses) {
			result.append("flattened_").append(c.toPrettyString("   ", Integer.MAX_VALUE)).append(". // Flattened version of clause #").append(counter++).append(".\n\n");
		}
		
		result.append("\n% The unique flattened literals:\n");
		for (Literal lit : uniqueFlattenedLiterals) {
			result.append("%   ").append(lit).append("\n");
		}
		return result.toString();
	}
	private Collection<Variable> collectAllVariables() {
		return collectFreeVariables();
	}
	
	private Collection<Variable> collectFreeVariables() {
    	Collection<Variable> headVars = headLiteral.collectFreeVariables(null);
    	Collection<Variable> rootVars = root.collectFreeVariables(null);
		return Variable.combineSetsOfVariables(headVars, rootVars);
	}
	
	// NOTE: if convertToStandardTheory has occurred, it will need to be redone in the new copy after renaming.
	public TreeStructuredTheory renameAllVariables() {
		Collection<Variable> vars = collectAllVariables();
		BindingList bl = stringHandler.renameAllVariables(vars, null);
		return new TreeStructuredTheory(stringHandler, headLiteral.applyTheta(bl.theta), root.applyTheta(bl.theta));
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return printRelationalTree(newLineStarter, precedenceOfCaller, bindingList);
	}

    public String toPrettyString(String newLineStarter, int precedenceOfCaller) {
		return printRelationalTree(newLineStarter, precedenceOfCaller, null);
	}

	private String printRelationalTree(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		if (root == null) { return "\n" + newLineStarter + "  THERE IS NO STORED TREE FOR " + headLiteral.toPrettyString(newLineStarter, precedenceOfCaller, bindingList) + "."; }
		if (bindingList == null) {
			// Create a  new bl for the children
			bindingList = new BindingList(); 
			
		}
		return "% FOR " + headLiteral.toPrettyString("%" + newLineStarter, defaultPrecedence, bindingList) + ":\n% " + newLineStarter + "  "
				+ root.printRelationalTree("% " + newLineStarter + "  ", precedenceOfCaller, 0, bindingList)
				+ "\n\n" + super.toPrettyString(newLineStarter, precedenceOfCaller, bindingList) + // Also print the version as a set of Horn clauses.
				getFlattenedClauseStrings();
	}

	public void writeDOTFile(String fname) {
		Utils.ensureDirExists(fname);
		BufferedWriter wr;
		try {
			wr = new BufferedWriter(new CondorFileWriter(fname, false));
			String res = writeDotFormat();
			wr.write(res);
			wr.close();
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem writing DOTFile: " + fname);
		}
	}

	public Set<Literal> getUniqueFlattenedLiterals() {
		return uniqueFlattenedLiterals;
	}

}
