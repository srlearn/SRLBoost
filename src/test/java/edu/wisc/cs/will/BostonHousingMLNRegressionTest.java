package edu.wisc.cs.will;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import org.junit.jupiter.api.Test;

/*
 * This should either be corrected or treated as an error. I don't think MLN regression is possible currently,
 * but using them in conjunction does not lead to an error.
 *
 * // TODO(hayesall): Deprecate one of them.
 */
public class BostonHousingMLNRegressionTest {
    @Test
    public void testMLNBostonHousingLearnInfer() {

        String[] trainArgs = {"-l", "-reg", "-mln", "-train", "data/boston_housing/train/", "-target", "medv", "-trees", "10"};
        RunBoostedModels.main(trainArgs);

        String[] testArgs = {"-i", "-reg", "-mln", "-model", "data/boston_housing/train/models/", "-test", "data/boston_housing/test/", "-target", "medv"};
        RunBoostedModels.main(testArgs);
    }
}
