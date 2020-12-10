package edu.wisc.cs.will.Utils;

import java.util.*;
import java.util.Map.Entry;

// TODO(@hayesall): This class basically duplicates `MapOfLists`: types might be generalized.

/* A Map that maps Keys to Set of values.
 *
 * Each key can be mapped to a set of values.
 *
 * @author twalker
 */
public class MapOfSets<Key, Value> implements Iterable<Value> {

    private Map<Key, Set<Value>> map;

    public MapOfSets() {
    }

    private Set<Value> getValues(Key key) {
        return map == null ? null : map.get(key);
    }

    public void put(Key key, Value value) {

        if ( map == null ) {
            map = createMap();
        }

        Set<Value> result = map.computeIfAbsent(key, k -> createValueSet());

        result.add(value);
    }

    private Set<Value> createValueSet() {
        return new HashSet<>();
    }

    private Map<Key, Set<Value>> createMap() {
        return new HashMap<>();
    }

    @Override
    public String toString() {

        String result;

        if ( map == null ) {
            result = "{}";
        }
        else {
            StringBuilder stringBuilder = new StringBuilder();

            for (Entry<Key, Set<Value>> entry : map.entrySet()) {
                stringBuilder.append(entry.getKey()).append(" => {");

                boolean first = true;
                for (Value value : entry.getValue()) {
                    if (!first) {
                        stringBuilder.append(",");

                    }
                    stringBuilder.append("\n");

                    String valueString = value.toString();

                    String prefixedValueString = Utils.getStringWithLinePrefix(valueString, "    ");
                    stringBuilder.append(prefixedValueString);

                    first = false;
                }

                stringBuilder.append("}. \n");

            }
            result = stringBuilder.toString();
        }

        return Utils.getStringWithLinePrefix(result, "");
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final MapOfSets<Key, Value> other = (MapOfSets<Key, Value>) obj;
        return Objects.equals(this.map, other.map);
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 71 * hash + (this.map != null ? this.map.hashCode() : 0);
        return hash;
    }

    public Iterator<Value> iterator() {
        if ( map == null ) {
            return Collections.EMPTY_SET.iterator();
        }
        else {
            return new AllValueIterator(map.keySet().iterator());
        }
    }

    class AllValueIterator implements Iterator<Value>{
        final Iterator<Key> allKeysIterator;

        Iterator<Value> currentSubIterator = null;

        Value next = null;

        AllValueIterator(Iterator<Key> allKeysIterator) {
            this.allKeysIterator = allKeysIterator;
        }

        public boolean hasNext() {
            setupNext();
            return next != null;
        }

        public Value next() {
            setupNext();
            Value result = next;
            next = null;
            return result;
        }

        public void remove() {
            throw new UnsupportedOperationException("Not supported yet.");
        }

        private void setupNext() {
            while (next == null) {
                if ( currentSubIterator != null && currentSubIterator.hasNext()) {
                    next = currentSubIterator.next();
                }
                else {
                    if ( allKeysIterator != null && allKeysIterator.hasNext() ) {
                        currentSubIterator = getValues(allKeysIterator.next()).iterator();
                    }
                    else {
                        break;
                    }
                }
            }
        }
    }
}
