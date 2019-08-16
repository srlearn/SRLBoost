package edu.wisc.cs.will.ILP;

/**
 * @author twalker
 */
public class TAWExperimenter {

    public TAWExperimenter() {}

    public static class MyExperimenter extends Experimenter {

        boolean myUseAdvice;

        public MyExperimenter(boolean myUseAdvice) {
            this.myUseAdvice = myUseAdvice;
        }

        public void setupUserOverrides() {
            experimentName = "BL_rawData/";
            mainWorkingDir = "/scratch/twalker/development/" + experimentName;

            probOfFlippingClassLabel = 0;
            fractionOfTrainingExamplesToUse = 0.25;
            probOfDroppingLiteral = 0.75;

            setOverWriteOldResults(true);

            if ( probOfFlippingClassLabel < 0 || probOfFlippingClassLabel >= 1 ) {
                throw new IllegalArgumentException("What the hell.  Check the prob of flipping class label value!");
            }
        }
    }
}
