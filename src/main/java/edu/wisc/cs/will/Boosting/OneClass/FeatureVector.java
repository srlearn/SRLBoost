package edu.wisc.cs.will.Boosting.OneClass;

import edu.wisc.cs.will.Utils.Utils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/*
 * @author tkhot
 */
public class FeatureVector {
	private List<Double> features;
	
	public List<String> pathFeatures;
	
	public boolean usepath = true;
	public FeatureVector() {
		features = new ArrayList<>();
		pathFeatures = new ArrayList<>();
	}
	
	double getDistance(FeatureVector other) {
		
		
		if (usepath) {
			double dist = 0;
			double count = 0;
			for (int i = 0; i < pathFeatures.size(); i++) {
				String a = pathFeatures.get(i);
				String b = other.pathFeatures.get(i);
				int diffChar = getDiffChar(a, b);
				if (diffChar != -1) {
					dist += Math.exp(-diffChar+1);
				} else {
					dist += 0;
				}
				count++;
			}
			if (count == 0) count=1;
			return dist/count;
		}
		Utils.waitHere("Not using path features!!");
		if (features.size() != other.features.size()) {
			Utils.error("Comparing unequal feature vectors");
		}
		for (int i = 0; i < features.size(); i++) {
			if (Utils.diffDoubles(other.getFeature(i), this.getFeature(i))) {
				return 1;
			}
		}
		
		return 0;
	}
	
	private int getDiffChar(String a, String b) {
		for (int i = 0; i < a.length(); i++) {
			if (a.charAt(i) != b.charAt(i)) {
				return i;
			}
		}
		return -1;
	}

	private double getFeature(int index) {
		return features.get(index);
	}

	public void append(double fval) {
		
		if (Utils.diffDoubles(fval, 0.0) && Utils.diffDoubles(fval, 1.0)) {
			Utils.error("Can only handle boolean features");
		}
		features.add(fval);
	}

	public void append(FeatureVector featureVector) {
		if (usepath) { pathFeatures.addAll(featureVector.pathFeatures); }
		features.addAll(featureVector.features);
	}
	
	void parseString(String fvec) {
		if (usepath) {
			fvec = fvec.replace("[", "").replace("]", "");
			String[] parts = fvec.split("\\|");
			pathFeatures = new ArrayList<>(Arrays.asList(parts));
		} else {
			Utils.waitHere("Cant parse non path features");
		}
	}
	public String toString() {
		StringBuilder result = new StringBuilder();

		if (usepath) {
			for (int i = 0; i < pathFeatures.size(); i++) {
				if (i == pathFeatures.size() - 1) {
					result.append(pathFeatures.get(i));
				} else {
					result.append(pathFeatures.get(i)).append("|");
				}
			}	
		} else {
			for (Double feature : features) {
				result.append(Utils.diffDoubles(feature, 1.00) ? "0" : "1");
			}
		}
		
		return "[" + result +"]";
	}

}
