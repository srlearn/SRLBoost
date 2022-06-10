package edu.wisc.cs.will;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import org.junit.jupiter.api.Test;

public class RDNInferenceTestToyFatherTest {
    @Test
    public void testToyFatherInferenceFromModels() {

        // Test that *just* inference with no learning works.

        String[] testArgs = {"-i", "-model", "data/toy_father_infer/models/", "-test", "data/toy_father_infer/test/", "-target", "father", "-trees", "15"};
        RunBoostedModels.main(testArgs);
    }
}
