package edu.wisc.cs.will.Boosting.Utils;

import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/*
 * @author Tushar Khot
 *
 */
public class BoostingUtils {

	public static List<Example> convertToListOfExamples(List<RegressionRDNExample> examples) {
		if (examples == null) { return null; }
		List<Example> results = new ArrayList<>(examples.size());
		results.addAll(examples);
		return results;
	}

	public static List<RegressionRDNExample> castToListOfRegressionRDNExamples(List<Example> examples) {
		if (examples == null) { return null; }
		List<RegressionRDNExample> results = new ArrayList<>(examples.size());
		for (Example ex : examples) { results.add((RegressionRDNExample)ex); }
		return results;
	}
	
	public static RegressionValueOrVector getRegressionValueOrVectorFromTerm(Term leafTerm) {
		if (leafTerm instanceof NumericConstant) {
			return new RegressionValueOrVector(((NumericConstant) leafTerm).value.doubleValue());
		}
		Utils.error("Uknown type of constant in leaf: " + leafTerm.toPrettyString());
		return null;
	}

	public static String getLabelForModelNumber(int modelNumber) {
		return (modelNumber > 0 ? "Model" + modelNumber : ""); // Model 0 is only implicitly named, in case we only want one model.
	}

	public static String getModelFile(CommandLineArguments cmdArgs, String target, boolean includeExtension) {
		String filename = cmdArgs.getModelDirVal() + "bRDNs/" + target;
		if (cmdArgs.getModelFileVal() != null) {
			 filename += "_" + cmdArgs.getModelFileVal();
		}
		filename += (includeExtension ? ".model" : "");
		Utils.ensureDirExists(filename);
		return filename;
	}

	public static List<PredicateNameAndArity> convertBodyModesToPNameAndArity(Set<PredicateNameAndArity> pnames) {
		List<PredicateNameAndArity> pars = new ArrayList<>();
		for (PredicateNameAndArity predicate : pnames) {
			// For each spec for the predicate
			for (PredicateSpec spec : predicate.getPredicateName().getTypeList()) {
				if (spec.getTypeSpecList() != null) {
					int arity = spec.getTypeSpecList().size();
					PredicateNameAndArity par = new PredicateNameAndArity(predicate.getPredicateName(), arity);
					// TODO(TVK) use a set.
					if (!pars.contains(par)) {
						pars.add(par);
					}
				}
			}
		}
		return pars;
	}

	public static double sigmoid(double numRegExp, double denoRegExp) {
		return 1/ (Math.exp(denoRegExp - numRegExp) + 1);
	}

	public static String getCheckPointFile(String saveModelName) {
		return saveModelName + ".ckpt";
	}

	public static String getCheckPointExamplesFile(String saveModelName) {
		return saveModelName + ".ckptEgs";
	}

	public static String getCheckPointFlattenedLitFile(String saveModelName) {
		return saveModelName + ".ckptLits";
	}


}
