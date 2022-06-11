package edu.wisc.cs.will;


import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import org.junit.jupiter.api.Test;

/*
 * There was a case where RDN learning produced a tree like this:
 *
 * ```
 * setParam: stringsAreCaseSensitive = true.
 * usePrologVariables: true.
 * (advisedby(A, B, 0.011216480726549238) :- professor(B), yearsinprogram(A, year_4), ta(_, A, _), !).
 * (advisedby(A, B, 0.21558828200077015) :- professor(B), yearsinprogram(A, year_4), !).
 * (advisedby(A, B, 0.1584030811343881) :- professor(B), inphase(A, post_generals), tempadvisedby(_, B), !).
 * (advisedby(A, B, -9.549146198883918E-4) :- professor(B), inphase(A, post_generals), !).
 * (advisedby(_, A, -0.0650668206218832) :- professor(A), taughtby(_, A, _), !).
 * (advisedby(_, A, 0.35697404542488276) :- professor(A), !).
 * (advisedby(_, _, -0.06435650552504418) :- !).
 * ```
 *
 * Which seems *relatively* rare.
 *
 * More often, these results look like this:
 *
 * ```
 * setParam: stringsAreCaseSensitive = true.
 * usePrologVariables: true.
 * (advisedby(A, B, 0.10889031008305691) :- professor(B), yearsinprogram(A, year_5), hasposition(B, faculty)).
 * (advisedby(A, B, 0.37011603647970887) :- professor(B), yearsinprogram(A, year_5)).
 * (advisedby(A, B, -0.45743189853468985) :- professor(B), tempadvisedby(A, _), tempadvisedby(_, B)).
 * (advisedby(A, B, -0.19044155953796488) :- professor(B), tempadvisedby(A, _)).
 * (advisedby(_, A, 0.013772404584037513) :- professor(A), tempadvisedby(_, A)).
 * (advisedby(_, A, 0.10982889364255019) :- professor(A)).
 * advisedby(_, _, -0.0685767045296399) .
 * ```
 *
 * This test assists with checking whether inference is possible with both versions.
 *
 * TODO(hayesall): What causes each version to be produced?
 */
public class RDNInferenceTestUWCSETest {

    @Test
    public void testUWCSEInferenceFromModels() {
        String[] testArgs = {"-i", "-model", "data/uwcse_infer/models/", "-test", "data/uwcse_infer/test/", "-target", "advisedby", "-trees", "10"};
        RunBoostedModels.main(testArgs);
    }
}
