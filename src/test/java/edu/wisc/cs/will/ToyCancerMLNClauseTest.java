package edu.wisc.cs.will;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import org.junit.jupiter.api.Test;

public class ToyCancerMLNClauseTest {
    @Test
    public void testToyCancerMLNClauseLearnInfer() {
        String[] trainArgs = {"-l", "-mln", "-mlnClause", "-train", "data/toy_cancer/train/", "-target", "cancer", "-trees", "10"};
        RunBoostedModels.main(trainArgs);

        String[] testArgs = {"-i", "-mln", "-mlnClause", "-model", "data/toy_cancer/train/models/", "-test", "data/toy_cancer/test/", "-target", "cancer"};
        RunBoostedModels.main(testArgs);
    }
}
