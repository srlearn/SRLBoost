package edu.wisc.cs.will;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import org.junit.jupiter.api.Test;

public class BostonHousingMLNClauseRegressionTest {
    @Test
    public void testMLNBostonHousingLearnInfer() {

        String[] trainArgs = {"-l", "-reg", "-mln", "-mlnClause", "-train", "data/boston_housing/train/", "-target", "medv", "-trees", "10"};
        RunBoostedModels.main(trainArgs);

        String[] testArgs = {"-i", "-reg", "-mln", "-mlnClause", "-model", "data/boston_housing/train/models/", "-test", "data/boston_housing/test/", "-target", "medv"};
        RunBoostedModels.main(testArgs);
    }
}
