package edu.wisc.cs.will;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import org.junit.jupiter.api.Test;

public class CoraRDNTest {
    @Test
    public void testCoraRDNLearnInfer() {
        String[] trainArgs = {"-l", "-train", "data/cora/fold1/train/", "-target", "sameauthor", "-trees", "10"};
        RunBoostedModels.main(trainArgs);

        String[] testArgs = {"-i", "-model", "data/cora/fold1/train/models/", "-test", "data/cora/fold1/test/", "-target", "sameauthor"};
        RunBoostedModels.main(testArgs);
    }
}
