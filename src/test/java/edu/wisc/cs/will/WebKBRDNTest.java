package edu.wisc.cs.will;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import org.junit.jupiter.api.Test;

public class WebKBRDNTest {
    @Test
    public void testWEBKBLearnInfer() {
        String[] trainArgs = {"-l", "-train", "data/webkb/fold1/train/", "-target", "faculty", "-trees", "10"};
        RunBoostedModels.main(trainArgs);

        String[] testArgs = {"-i", "-model", "data/webkb/fold1/train/models/", "-test", "data/webkb/fold1/test/", "-target", "faculty"};
        RunBoostedModels.main(testArgs);
    }
}
