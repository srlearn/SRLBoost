package edu.wisc.cs.will;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.assertEquals;


public class RunBoostedModelsTest
{
    @Test
    public void testFoo()
    {
        String[] args = {"-l", "-train", "data/Toy-Cancer/train/", "-target", "cancer"};
        RunBoostedModels.main(args);
    }
}