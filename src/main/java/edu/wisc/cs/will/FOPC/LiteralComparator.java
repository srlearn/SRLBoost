package edu.wisc.cs.will.FOPC;

import java.util.Comparator;

/*
 * @author shavlik
 */
public class LiteralComparator implements Comparator<Literal> {

	public LiteralComparator() {
	}

	public int compare(Literal lit0, Literal lit1) {
		// TODO(@hayesall): Suspicious `(lit0 == lit1)` before null check.
		if (lit0 == lit1) { return 0; }

		assert lit0 != null;
		assert lit1 != null;

		int int0 = lit0.predicateName.hashCode();
		int int1 = lit1.predicateName.hashCode();
		
		if (int0 != int1) { return int0 - int1; }
		
		int len0 = lit0.numberArgs();
		int len1 = lit1.numberArgs();
		
		if (len0 != len1) { return len0 - len1; }
		
		for (int i = 0; i < len0; i++) {
			Term arg0 = lit0.getArgument(i);
			Term arg1 = lit1.getArgument(i);
			
			if (arg0 == arg1) { continue; }  // Sort based on the first non-matching term.
			if (arg0 instanceof Variable) {
				if (arg1 instanceof Variable) {  // Sort variables based on their name.
					Variable v0 = (Variable) arg0;
					Variable v1 = (Variable) arg1;
					String   s0 = v0.toString();
					String   s1 = v1.toString();
					if (s0.equals(s1)) {
						// These are longs and we need an int, so cannot simply subtract.
						return Long.compare(v0.counter, v1.counter);
					}
					return s0.hashCode() - s1.hashCode();
				}
				return -1;
			}
			if (arg1 instanceof Variable) { return 1; } 
			
			int arg0int = arg0.hashCode();  // TODO should recur inside of these, in case there are functions.
			int arg1int = arg1.hashCode();  // TODO probably should implement hashCode for all FOPC classes.
			
			return arg0int - arg1int;
		}
		
		return 0;  // Could find no difference.
	}

}
