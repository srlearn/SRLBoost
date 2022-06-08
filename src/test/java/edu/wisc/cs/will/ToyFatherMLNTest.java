package edu.wisc.cs.will;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import org.junit.jupiter.api.Test;

public class ToyFatherMLNTest {
    @Test
    public void testToyFatherMLNLearnInfer() {
        String[] trainArgs = {"-l", "-mln", "-train", "data/toy_father/train/", "-target", "father", "-trees", "10"};
        RunBoostedModels.main(trainArgs);

        String[] testArgs = {"-i", "-mln", "-model", "data/toy_father/train/models/", "-test", "data/toy_father/test/", "-target", "father"};
        RunBoostedModels.main(testArgs);
    }
}
