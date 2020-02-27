package edu.wisc.cs.will.DataSetUtils;

import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;

/*
 * @author shavlik
 *
 */
public class WorldState {
	private final Constant world;
	private final Constant state;
	
	WorldState() {
		// TODO(@hayesall): always initializes final values as null.
		this.world = null;
		this.state = null;
	}
	Constant getWorld() {
		return world;
	}

	public Constant getState() {
		return state;
	}

	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((state == null) ? 0 : state.hashCode());
		result = prime * result + ((world == null) ? 0 : world.hashCode());
		return result;
	}

	public boolean equals(Term otherWorld, Term otherState) {
		if (otherWorld instanceof Variable && otherState instanceof Variable) {
			return otherWorld != otherState;
		}
		if (otherWorld instanceof Variable) {
			return state == otherState;
		}
		if (otherState instanceof Variable) {
			return world == otherWorld;
		}
		return (world == otherWorld && state == otherState);
	}

	boolean isaNullWorldState() {
		return (world == null && state == null);
	}
	
	public String toString() {
		return world + "." + state;
	}
}
