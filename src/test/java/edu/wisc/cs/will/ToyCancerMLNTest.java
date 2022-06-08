package edu.wisc.cs.will;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import org.junit.jupiter.api.Test;

public class ToyCancerMLNTest {
    @Test
    public void testToyCancerMLNLearnInfer() {
        String[] trainArgs = {"-l", "-mln", "-train", "data/toy_cancer/train/", "-target", "cancer", "-trees", "10"};
        RunBoostedModels.main(trainArgs);

        String[] testArgs = {"-i", "-mln", "-model", "data/toy_cancer/train/models/", "-test", "data/toy_cancer/test/", "-target", "cancer"};
        RunBoostedModels.main(testArgs);
    }
}
