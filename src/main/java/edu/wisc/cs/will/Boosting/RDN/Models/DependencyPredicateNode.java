package edu.wisc.cs.will.Boosting.RDN.Models;

import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.Utils.Utils;

/*
 * @author Tushar Khot
 */
public class DependencyPredicateNode extends DependencyNode {
	private PredicateName predicate;

	public enum PredicateType {
		HIDDEN,
		EVIDENCE,
		QUERY,
		COMPUTED,
	}
	// Default value is EVIDENCE
	private PredicateType type;
	
	DependencyPredicateNode(PredicateName name) {
		super();
		type=PredicateType.EVIDENCE;
		setPredicate(name);
	}
	
	private String labelForDOT() {
		StringBuilder arglist = new StringBuilder();
		if (predicate != null && predicate.getTypeList() != null) {
			for (PredicateSpec spec : predicate.getTypeList()) {
				if (spec.getTypeSpecList() != null) {
					for (TypeSpec tspec : spec.getTypeSpecList()) {
						arglist.append(",").append(tspec.getType());
					}
					arglist = new StringBuilder(arglist.toString().replaceFirst(",", ""));
					break;
				}
			}
		}
		return predicate.toString()  + "(" + arglist + ")" + "";
	}
	
	private String colorForDOT() {
		switch(type) {
			case QUERY: return "gray52";
			case HIDDEN: return "gray62";
			case COMPUTED: return "gray82";
			case EVIDENCE: return "gray92";
		}
		return "white";
	}
	public String textForDOT() {
		return "style=\"filled\" label=\"" + labelForDOT() +"\" color=\"" + colorForDOT() + "\"";
	}
	
	/*
	 * @return the predicate
	 */
	public PredicateName getPredicate() {
		return predicate;
	}

	/*
	 * @param predicate the predicate to set
	 */
	private void setPredicate(PredicateName predicate) {
		this.predicate = predicate;
	}
	
	/*
	 * @return the type
	 */
	public PredicateType getType() {
		return type;
	}

	/*
	 * @param type the type to set
	 */
	public void setType(PredicateType type) {
		if (this.type != PredicateType.EVIDENCE) {
			Utils.waitHere("Changing type for " + this.labelForDOT() + " from " + this.type +" to " + type);
		}
		this.type = type;
	}

	@Override
	public boolean ignoreNodeForDOT() {
		String predString = getPredicate().toString();
		if (predString.equals("all") ||
			predString.equals("is")  ||
			predString.equals("==")  ||
			predString.equals("=")  ||
			predString.equals("addList")  ||
			predString.equals(">")   ||
			predString.equals("!")   ||
			predString.equals("member")) {
			return true;
		}

		return getType() == PredicateType.COMPUTED &&
				getChildren().isEmpty();
	}

}
