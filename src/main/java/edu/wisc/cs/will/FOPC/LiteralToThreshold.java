package edu.wisc.cs.will.FOPC;

import java.util.List;

/*
 * @author shavlik
 *
 * This extension to PredicateName is used when a numeric-valued function is represented as a literal,
 * and values for this function should be compared to thresholds.  For example,
 * 
 * 	f(x,y)  where y = f(x)
 * 
 * can be converted to
 * 
 *  f_in_interval(x, y, lower, upper), whose semantics is 'lower <= y < upper'
 *  
 *  This needs to be in FOPC so that HandleFOPCstrings can access it (of course other code restructurings are possible).
 *
 */
public class LiteralToThreshold extends Literal {
	private static final long serialVersionUID = -2379554597565225129L;
	// TODO(@hayesall): This can probably be removed, since the constructor is never
	// used. But several other places will need to be changed.
	public final int     positionToThreshold;
	public final int     maxCuts;
	public final boolean createTiles;
	public final boolean firstArgIsExampleID;

	LiteralToThreshold(HandleFOPCstrings stringHandler, PredicateName pred, List<Term> arguments, int positionToThreshold, int maxCuts, boolean createTiles, boolean firstArgIsExampleID) {
		super(stringHandler, pred, arguments);
		this.positionToThreshold = positionToThreshold;
		this.maxCuts             = maxCuts;
		this.createTiles         = createTiles;
		this.firstArgIsExampleID = firstArgIsExampleID;
	}
}
