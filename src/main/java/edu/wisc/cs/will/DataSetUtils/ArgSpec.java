package edu.wisc.cs.will.DataSetUtils;

import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.TypeSpec;

import java.io.Serializable;

/*
 * @author shavlik
 */
public class ArgSpec implements Serializable {

	private static final long serialVersionUID = 1L;

	public final Term arg;
	public final TypeSpec typeSpec;

	public ArgSpec(Term arg, TypeSpec typeSpec) {
		this.arg = arg;
		this.typeSpec = typeSpec;
	}
	
	public String toString() {
		return arg + "[" + typeSpec + "]";
	}
}
