package edu.wisc.cs.will.FOPC;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;

import edu.wisc.cs.will.Utils.AlphanumComparator;
import edu.wisc.cs.will.Utils.TimeScale;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author twalker
 */
public final class UserDefinedLiteralCache {

    private static final int DEFAULT_CACHE_SIZE = 10000;

    /** Indicates a fail during previous evaluation of the predicate. */
    static final Object FAILURE_INDICATOR = new Object();

    private SizeLimitedCacheMap cacheMap;

    private CacheStatistics globalStatistics;

    private Map<PredicateNameAndArity, CacheStatistics> statisticsMap;

    UserDefinedLiteralCache() {
        cacheMap = new SizeLimitedCacheMap(DEFAULT_CACHE_SIZE);
        statisticsMap = new HashMap<>();
        globalStatistics = new CacheStatistics("Overall Cache Statistics");
    }

    /** Indicates that Cache timing are desired.
     *
     * Cache timing is always optional on the clients part.  If the client
     * does not want/need to perform timings due to performance reasons,
     * it does not have too.
     */
    boolean isCacheTimingEnabled() {
        return true;
    }

    /** Returns a CacheEntry for the predicateName/Arity and the set of ground terms.
     *
     * The CacheEntry contains all of the information about the current cache state for
     * the indicated arguments.  This includes the cacheValue (either the previously
     * set value, null to indicate the values was not previously set, or FAILURE_INDICATOR
     * to indicate that a failure of the predicateName/Arity and terms is cached).  The
     * cache statistics are also included in case they are needed.
     * <p>
     * After a lookup has occurred, methods of the CacheEntry should be used to cache new
     * or updated cache values, record times (if enabled), etc.  The CacheEntry delegates
     * all necessary work back to the source UserDefinedLiteralCache.
     * <p>
     * This is a flexible caching mechanism so the UserDefinedLiteral can determine
     * how it wants to use it based upon the specific implementation of the user defined literal.
     * The only requirement is that for any fixed set of terms, the cached value is always the
     * same.
     * <p>
     * Note, the list of terms does not need to match the arity of the literal being evaluated.
     * However, if a reduction of the number of terms is performed (say by ignoring Variable
     * terms), it should be a 1-to-1 mapping of the original terms to the new term list.  Just
     * removing all non-ground terms generally will not result in a 1-to-1 mapping.
     *
     * @param predicateNameArity Predicate name and arity to lookup.
     * @param terms List of terms to lookup.
     * @return A CacheEntry associated with the predicateName/Arity and terms.
     *
     */
    CacheEntry lookupCacheEntry(PredicateNameAndArity predicateNameArity, List<Term> terms, UserDefinedCacheResolver cacheResolver) {

        CacheStatistics cs = getCacheStatistics(predicateNameArity);

        CacheKey ck = new CacheKey(predicateNameArity, terms, cacheResolver);

        Object cachedValue = cacheMap.get(ck);

        if (cachedValue == null) {
            globalStatistics.recordMiss();
            cs.recordMiss();
        }

        globalStatistics.recordLookup();
        cs.recordLookup();

        return new CacheEntry(ck, cs, cachedValue);
    }

    private String getCacheStatistics() {
        StringBuilder sb = new StringBuilder();

        List<PredicateNameAndArity> cachedPreds = new ArrayList<>(statisticsMap.keySet());
        cachedPreds.sort((o1, o2) -> AlphanumComparator.ALPHANUM_COMPARATOR.compare(o1.toString(), o2.toString()));

        int descWidth = globalStatistics.description.length();
        for (PredicateNameAndArity predicateNameArity : cachedPreds) {
            descWidth = Math.max(descWidth, predicateNameArity.toString().length());
        }

        sb.append(getCacheStatisticsHeader(descWidth + 4));

        sb.append(globalStatistics.toString(descWidth + 4)).append("\n");

        for (PredicateNameAndArity predicateNameArity : cachedPreds) {
            CacheStatistics cs = statisticsMap.get(predicateNameArity);

            if (cs != null) {
                sb.append(cs.toString(descWidth + 4)).append("\n");
            }
        }

        return sb.toString();
    }

    private static String getCacheStatisticsHeader(int descWidth) {
        return String.format("%-" + descWidth + "s %9s %9s %7s %9s %7s %9s %9s %9s\n",
                "Literal", " Calls  ", " Hits  ", " Hit % ", "Misses  ", " Miss %", "TimeSaved", "s/Eval ", "s/Lookup ") + String.format("%-" + descWidth + "s %9s %9s %7s %9s %7s %9s %9s %9s\n",
                "-----------", "---------", "---------", "-------", "---------", "-------", "---------", "---------", "---------");
    }

    private CacheStatistics getCacheStatistics(PredicateNameAndArity predicateNameArity) {
        CacheStatistics cs = statisticsMap.get(predicateNameArity);
        if (cs == null) {
            cs = new CacheStatistics(predicateNameArity.toString());
            statisticsMap.put(predicateNameArity, cs);
        }
        return cs;
    }

    @Override
    public String toString() {
        return "UserDefiniteLiteral Cache:\n" + getCacheStatistics();
    }

    @SuppressWarnings("serial")
    private static class SizeLimitedCacheMap<Key, Value> extends LinkedHashMap<Key, Value> {

        private int maximumSize;

        SizeLimitedCacheMap(int maximumSize) {
            super(16, 0.75f, true);

            this.maximumSize = maximumSize;
        }

        @Override
        protected boolean removeEldestEntry(Entry<Key, Value> eldest) {
            return maximumSize > 0 && size() > maximumSize;
        }
    }

    public final class CacheEntry {

        private CacheKey cacheKey;

        private CacheStatistics cacheStatistics;

        private Object cachedValue;

        CacheEntry(CacheKey cacheKey, CacheStatistics cacheStatistics, Object cachedValue) {
            this.cacheKey = cacheKey;
            this.cacheStatistics = cacheStatistics;
            this.cachedValue = cachedValue;
        }

        /** Sets the cached value for this cache entry.
         *
         * Note, this is a flexible caching mechanism so the UserDefinedLiteral can determine
         * how it wants to use it based upon the specific implementation of the user defined literal.
         * The only requirement is that for any fixed set of terms, the cached value is always the
         * same.
         * <p>
         * Note, the list of terms does not need to match the arity of the literal being evaluated.
         * However, if a reduction of the number of terms is performed (say by ignoring Variable
         * terms), it should be a 1-to-1 mapping of the original terms to the new term list.  Just
         * removing all non-ground terms generally will not result in a 1-to-1 mapping.
         * <p>
         * If you wish to cache a failed evaluation result, either null or FAILURE_INDICATOR can be
         * passed in for the value argument.  However, a null value will be stored as FAILURE_INDICATOR.
         *
         * @param value Value to cache or FAILURE_INDICATOR (or null) if the evaluation of the literal for terms failed.
         */
        void setCachedValue(Object value) {

            if (value == null) {
                value = FAILURE_INDICATOR;
            }

            if (!Objects.equals(this.cachedValue, value)) {
                if (this.cachedValue != null) {
                    Utils.warning("Previously set cache value for " + cacheKey + " has been reset.");
                }

                cacheMap.put(cacheKey, value);
            }
        }

        /** Returns the previously cached value.
         *
         * @return Either a value, FAILURE_INDICATOR, or null.  If the lookup is successful, the value
         * of the literal for terms will be returned, with a return value of
         * FAILURE_INDICATOR indicating that the evaulation of the literal previously
         * failed.  If the lookup is unsuccessful (ie the value for terms isn't currently
         * cached) then null is returned.
         */
        Object getCachedValue() {
            return cachedValue;
        }

        /** Records the time necessary to perform a cache lookup.
         *
         * This time should include the lookup time as well as the setCacheValue
         * time, but should not include any time spent performing the actual
         * calculation. Any time the is shared by existing cached value evaluation
         * and new evalutions (such as unifying to the final output) should not
         * be included.
         *
         * @param timeInNanoseconds Time in nanoseconds taken to perform a lookup.
         */
        void recordLookupTime(long timeInNanoseconds) {
            globalStatistics.recordLookupTime(timeInNanoseconds);
            cacheStatistics.recordLookupTime(timeInNanoseconds);
        }

        /** Records the time necessary to perform the actual literal evalution.
         *
         * This time should include only the time necessary to perform the calculation
         * of the value.  Any time the is shared by existing cached value evaluation
         * and new evalutions (such as unifying to the final output) should not
         * be included.
         *
         * @param timeInNanoseconds Time in nanoseconds taken to perform an evalution of the literal.
         */
        void recordEvaluationTime(long timeInNanoseconds) {
            globalStatistics.recordEvaluationTime(timeInNanoseconds);
            cacheStatistics.recordEvaluationTime(timeInNanoseconds);
        }

        @Override
        public String toString() {
            return "CacheEntry [" + cacheStatistics.toString() + "]";
        }
    }

    protected static final class CacheKey {

        PredicateNameAndArity predicateNameAndArity;

        List<Term> terms;

        UserDefinedCacheResolver cacheResolver;

        CacheKey(PredicateNameAndArity predicateNameAndArity, List<Term> terms, UserDefinedCacheResolver cacheResolver) {
            this.predicateNameAndArity = predicateNameAndArity;
            this.terms = terms;
            this.cacheResolver = cacheResolver;
        }

        @Override
        public boolean equals(Object obj) {
            if (obj == null) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            final CacheKey other = (CacheKey) obj;
            if (!Objects.equals(this.predicateNameAndArity, other.predicateNameAndArity)) {
                return false;
            }
            return Objects.equals(this.terms, other.terms);
        }

        @Override
        public int hashCode() {
            int hash = 7;
            hash = 89 * hash + (this.predicateNameAndArity != null ? this.predicateNameAndArity.hashCode() : 0);
            hash = 89 * hash + (this.terms != null ? this.terms.hashCode() : 0);
            return hash;
        }
    }

    public static final class CacheStatistics {

        private String description;

        private long accessCount = 0;

        private long missCount = 0;

        private long totalEvaluationTime = 0;

        private long totalEvaluationCount = 0;

        private long totalLookupTime = 0;

        private long totalLookupTimeCount = 0;

        CacheStatistics(String description) {
            this.description = description;
        }

        long getAccessCount() {
            return accessCount;
        }

        long getHits() {
            return accessCount - missCount;
        }

        double getHitFraction() {
            return accessCount == 0 ? Double.NaN : (double) (accessCount - missCount) / accessCount;
        }

        long getMisses() {
            return missCount;
        }

        double getMissFraction() {
            return accessCount == 0 ? Double.NaN : (double) missCount / accessCount;
        }

        double getMeanEvaluationTimeInMicroseconds() {
            return totalEvaluationCount == 0 ? Double.NaN : (double) totalEvaluationTime / totalEvaluationCount / 1000.0;
        }

        double getMeanLookupTimeInMicroseconds() {
            return totalLookupTimeCount == 0 ? Double.NaN : (double) totalLookupTime / totalLookupTimeCount / 1000.0;
        }

        double getDeltaTimeInMicroseconds() {
            double memoizedTime = accessCount * getMeanLookupTimeInMicroseconds() + missCount * getMeanEvaluationTimeInMicroseconds();
            double notMemoizedTime = accessCount * getMeanEvaluationTimeInMicroseconds();

            return notMemoizedTime - memoizedTime;
        }

        private void recordLookup() {
            accessCount++;
        }

        private void recordMiss() {
            missCount++;
        }

        private void recordLookupTime(long timeInNanoseconds) {
            totalLookupTime += timeInNanoseconds;
            totalLookupTimeCount++;
        }

        private void recordEvaluationTime(long timeInNanoseconds) {
            totalEvaluationTime += timeInNanoseconds;
            totalEvaluationCount++;
        }

        @Override
        public String toString() {
            return toString(description.length() + 4);
        }

        public String toString(int descriptionWidth) {

            return String.format("%-" + descriptionWidth + "s %9d %9d %6.2f%% %9d %6.2f%% %9s %9s %9s",
                    description,
                    getAccessCount(),
                    getHits(),
                    getHitFraction() * 100.0,
                    getMisses(), getMissFraction() * 100.0,
                    TimeScale.MICROSECOND.getBestFormattedString(getDeltaTimeInMicroseconds(), "%+7.1f%2s"),
                    TimeScale.MICROSECOND.getBestFormattedString(getMeanEvaluationTimeInMicroseconds(), "%7.1f%2s"),
                    TimeScale.MICROSECOND.getBestFormattedString(getMeanLookupTimeInMicroseconds(), "%7.1f%2s"));

        }
    }
}
