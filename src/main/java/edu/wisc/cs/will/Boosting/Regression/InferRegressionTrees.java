package edu.wisc.cs.will.Boosting.Regression;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.Utils.Utils;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.Map;

/*
 * @author tkhot
 */
class InferRegressionTrees {
	private final CommandLineArguments cmdArgs;
	private final WILLSetup            setup;
	
	InferRegressionTrees(CommandLineArguments cmdArgs, WILLSetup setup) {
		this.cmdArgs = cmdArgs;
		this.setup   = setup;
	}

	void runInference(JointRDNModel fullModel) {
		Map<String,List<RegressionRDNExample>> jointExamples = setup.getJointExamples(fullModel.keySet());
		
		for (String  pred : jointExamples.keySet()) {
			SRLInference regSampler = new RegressionTreeInference(fullModel.get(pred), setup);
			regSampler.getProbabilities(jointExamples.get(pred));
			double squaredError = 0;
			int counter = 0;
			try {
				BufferedWriter writer = new BufferedWriter(new FileWriter(getResultsFile(pred)));
				for (RegressionRDNExample ex : jointExamples.get(pred)) {
					squaredError += Math.pow(ex.getProbOfExample().getProbOfBeingTrue() - ex.originalRegressionOrProbValue, 2);
					counter++;
					writer.write(ex + "\t" + ex.getProbOfExample() + "\t" + ex.originalRegressionOrProbValue);
					writer.newLine();
				}
				Utils.println(pred);
				Utils.println("SquaredError = " + squaredError);
				Utils.println("MeanSquaredError = " + (squaredError/counter));
				writer.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	
	private String getResultsFile(String target) {
		String suff = "";
		if (cmdArgs.getModelFileVal() != null) {
			suff = cmdArgs.getModelFileVal() + "_";
		}
		return setup.getOuterLooper().getWorkingDirectory() + "/results_" + suff + target + ".db";
	}
}
