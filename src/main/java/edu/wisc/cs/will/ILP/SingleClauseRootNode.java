package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.ArgSpec;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.MessageType;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask;

import java.util.*;

/*
 * @author shavlik
 */
class SingleClauseRootNode extends SingleClauseNode {
	final Literal        target;          // For now, only work on one target (at a time? to do).
	final List<Term>     variablesInTarget;
	final Set<Variable>  requiredBodyVariablesInTarget = null;

	SingleClauseRootNode(StateBasedSearchTask task, Literal head, List<ArgSpec> argSpecs, List<Term> variables,
                         List<Type> typesPresentInHead, Map<Type, List<Term>> typesMapInHead) throws SearchInterrupted {
		super(task);
		target               = head;
		int targetPredicateArity = head.numberArgs();
		variablesInTarget    = variables;
		literalAdded = head; // The root has with the empty body (i.e., it is an implicit 'true').  So we'll store the head literal here.
		depthOfArgs = new HashMap<>(head.numberArgs());
		markDepthOfLeafTerms(head.getArguments(), 0); // The depth of all the 'leaf' terms in the root (i.e., the head) is zero.
        typesPresent = typesPresentInHead;
		typesMap     = typesMapInHead;
		if (argSpecs != null) {
			for (ArgSpec argSpec : argSpecs) {
				addTypeOfNewTerm(argSpec.arg, argSpec.typeSpec.isaType);
			}
		}
		computeCoverage();
		Utils.println(MessageType.ILP_INNERLOOP, "\n% target           = " + target);
		checkForRequiredBodyVars(target.getArguments());
	}
	
	private void checkForRequiredBodyVars(List<Term> arguments) {
		if (arguments == null) { return; }
		for (Term arg : arguments) {
			if (arg instanceof Variable) {
				Variable var = (Variable) arg;
				// This is a linear lookup - but targets should not be so complex that this inefficiency matters.
			} else if (arg instanceof Function) {
				Function f = (Function) arg;
				checkForRequiredBodyVars(f.getArguments());
			} else { Utils.error("Should never reach here."); }
		}
	}

}
