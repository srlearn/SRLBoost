package edu.wisc.cs.will;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.assertEquals;


public class RunBoostedModelsTest
{
    @Test
    public void testFoo()
    {
        String[] trainArgs = {"-l", "-train", "data/Toy-Cancer/train/", "-target", "cancer"};
        RunBoostedModels.main(trainArgs);

        String[] testArgs = {"-i", "-model", "data/Toy-Cancer/train/models/", "-test", "data/Toy-Cancer/test/", "-target", "cancer"};
        RunBoostedModels.main(testArgs);
    }
}