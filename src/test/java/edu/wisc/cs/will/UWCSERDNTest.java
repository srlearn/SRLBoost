package edu.wisc.cs.will;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import org.junit.jupiter.api.Test;

public class UWCSERDNTest {
    @Test
    public void testUWCSELearnInfer() {
        String[] trainArgs = {"-l", "-train", "data/uwcse/fold1/train/", "-target", "advisedby", "-trees", "10"};
        RunBoostedModels.main(trainArgs);

        String[] testArgs = {"-i", "-model", "data/uwcse/fold1/train/models/", "-test", "data/uwcse/fold1/test/", "-target", "advisedby"};
        RunBoostedModels.main(testArgs);
    }
}
