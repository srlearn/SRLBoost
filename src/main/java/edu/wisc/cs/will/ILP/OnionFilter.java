package edu.wisc.cs.will.ILP;

/**
 * @author shavlik
 */
public abstract class OnionFilter {

	/**
	 * Instances of this abstract class can be used to filter Onion layers by the caller to the Onion.
	 */
	public OnionFilter() {}
	
	abstract boolean skipThisSetting(ILPparameterSettings setting);
}
