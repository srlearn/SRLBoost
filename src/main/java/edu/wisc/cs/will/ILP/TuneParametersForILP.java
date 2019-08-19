package edu.wisc.cs.will.ILP;

import java.util.List;

/*
 * This is the default ONION class.  If is necessary to have the 
 * successive parameter settings get more complicated, the user can set onionLayers
 * or a programmer can 'wrap' on another class ala' a real onion.  TODO - allow the setting of Beta rather than using F1 all the time.
 * 
 * @author shavlik
 * 
 */

public class TuneParametersForILP {
	protected final static int debugLevel = 2; // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).

	private ILPouterLoop outerLooper;

	private List<ILPparameterSettings> onionLayers; // The list of onionLayers to try.


	// These control the onionLayers considered.
	// Can set these as follows in files read in by the parser, for example:
	//		setParam: numbersOfClausesToTry = "1, 2, 4, 8, 16".
	//		setParam: lengthsToTry          = "1, 2, 3, 7, 10, 100";
	//	    setParam: forLengthsLessThanThisOnlyFitTrainSet = 5;
	
	//TODO add setParam for numberOfMaxNodesToConsiderLevels

	/////////////////////////////////////////////////////////////////


}
