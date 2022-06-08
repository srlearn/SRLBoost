package edu.wisc.cs.will;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import org.junit.jupiter.api.Test;

public class ToyFatherMLNClauseTest {
    @Test
    public void testToyFatherMLNLearnInfer() {
        String[] trainArgs = {"-l", "-mln", "-mlnClause", "-train", "data/toy_father/train/", "-target", "father", "-trees", "10"};
        RunBoostedModels.main(trainArgs);

        String[] testArgs = {"-i", "-mln", "-mlnClause", "-model", "data/toy_father/train/models/", "-test", "data/toy_father/test/", "-target", "father"};
        RunBoostedModels.main(testArgs);
    }
}
