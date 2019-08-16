package edu.wisc.cs.will.Utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

// A way to create cross products that is space efficient - i.e., it creates a data structure where one can request the next item.
public class CrossProductViaContinuation<E> {

	public final static int debugLevel = 0;

	public double sizeOfCrossProduct = 0.0;

	// Number of collections 'crossed.'
	private int size = 0;

	private double maxSize = Double.MAX_VALUE;
	private int[] locationInEachCollection;
	private int[] sizeOfEachCollection;
	private List<Collection<E>> listOfCollections;
	private List<E[]> collections;
	private List<E> result;
	private double probOfKeepingItem = Double.MAX_VALUE;

	// Watch for too many of these.
	private int rejectionsInaRow = 0;

	// This means probability of rejecting a result can never be less than one over this, but that should be fine.
	private int maxRejectionsInaRow = 10000000;

	private int debugCounter = 0;
	private boolean initialized = false;

	public CrossProductViaContinuation(List<Collection<E>> listOfCollections) {
		this(listOfCollections, Double.MAX_VALUE);
	}

	private CrossProductViaContinuation(List<Collection<E>> listOfCollections, double maxSize) {
		// Hold these for faster access, at least if the Collection are hash tables or the like.  Used by containsThisEntry.
		this.listOfCollections = listOfCollections;
		this.maxSize = maxSize;
		if (listOfCollections != null) { 
			size = listOfCollections.size();
			sizeOfCrossProduct = 1.0;
			for (int i=0; i<size; i++) {
				sizeOfCrossProduct *= Utils.getSizeSafely(listOfCollections.get(i));
			}
		}
	}

	private void initializeCrossProducts() {
		// Postpone this until needed, since often all this precalculation isn't.
		locationInEachCollection = new int[size];
		sizeOfEachCollection = new int[size];
		collections = new ArrayList<>(size);
		result = new ArrayList<>(size);

		for (int i = 0; i < size; i++) {
			locationInEachCollection[i] = 0;
			Collection<E> ithCollection = listOfCollections.get(i);

			if (ithCollection == null) {
				Utils.error("Have provided collection(" + i + ") = null.");
			}
			sizeOfEachCollection[i] = ithCollection.size();
			E[] ithCollectionAsArray = (E[]) ithCollection.toArray(); // Check this cast?

			if (ithCollectionAsArray.length < 1) {
				Utils.error("Have length of ithCollectionAsArray(" + i + ") = " + ithCollectionAsArray.length);
			}
			collections.add(ithCollectionAsArray);

			// Need to have 'result' be of the required length.
			result.add(null);
		}

		probOfKeepingItem = Math.min(1.0, maxSize / sizeOfCrossProduct);
		if (probOfKeepingItem < 1.0 / maxRejectionsInaRow) {
			// Leave this here in case we change the error below to a warning.
			probOfKeepingItem = 1.0 / maxRejectionsInaRow;
			Utils.error("Cannot request that probOfKeepingItem be less than: " + Utils.truncate(1.0 / maxRejectionsInaRow, 3) + ".  Edit CrossProductViaContinuation if you want to do so.");
		}

		initialized = true;
	}

	public Collection<E> getThisEntry(int i) {
		return listOfCollections.get(i);
	}

	// See if the ith collection contains this entry.
	public boolean containsThisEntry(int i, E item) {
		Collection<E> items = listOfCollections.get(i);
		if (items == null) { Utils.error("Have an empty list in a cross product.  Was it cleared?"); }
		return items.contains(item);
	}

	public void reset() {
		// Start this cross-product generator anew.
		if (size < 1) { return; }
		if (!initialized) { initializeCrossProducts(); }
		else for (int i = 0; i < size; i++) { locationInEachCollection[i] = 0; }
	}
	
	public boolean isEmpty() { // If reached the end of the first list (or had no items to begin with), then done. 
		if (!initialized) { return (sizeOfCrossProduct < 1); } // Since not yet initialized, see if there will be at least one item in the cross product.
		return (size < 1 || (locationInEachCollection[0] >= sizeOfEachCollection[0]));
	}
	
	public List<E> getNextCrossProduct() {
		if (!initialized) { initializeCrossProducts(); }
		if (isEmpty()) { return null; } // If reached the end of the first list, then done.  Return NULL from now on.
		boolean continueGettingItem = true;
		while (continueGettingItem) {
			// Grab the current objects and place in the result list.		
			for (int i = 0; i < size; i++) {
				result.set(i, collections.get(i)[locationInEachCollection[i]]);
			}
			// Now update all the locations, starting with the last one.
			int updateMe = size - 1;
			while (updateMe >= 0) {
				locationInEachCollection[updateMe]++;
				if (locationInEachCollection[updateMe] >= sizeOfEachCollection[updateMe]) { // Have reached the end of this collection, so need to increment counter on previous one.
					if (updateMe > 0) { locationInEachCollection[updateMe] = 0; } // If in the FIRST collection, don't wrap around; leave here so know that have generated all combinations.
					updateMe--;
				} else { updateMe = -1; } // Done updating, so end the WHILE.
			}
			if (debugLevel > 0) {
				int maxDebugCounter = 3;
				if (debugCounter < maxDebugCounter) { Utils.println("    getNextCrossProduct = " + result); }
				debugCounter++;
			}
			if (!(probOfKeepingItem < 1.0 && Utils.random() > probOfKeepingItem && rejectionsInaRow++ < maxRejectionsInaRow)) { // Reject this item and repeat the WHILE loop.
				rejectionsInaRow    = 0;
				continueGettingItem = false;
			}	
		}
		return result;
	}
	
	public String toString() {
		StringBuilder results = new StringBuilder("There are " + Utils.comma(size) + " collections: ");
		for (int i = 0; i < size; i++) {
			results.append(i > 0 ? "x" : "").append(Utils.getSizeSafely(listOfCollections.get(i)));
		}
		return results + " = " + Utils.truncate(sizeOfCrossProduct, 0);
	}
}