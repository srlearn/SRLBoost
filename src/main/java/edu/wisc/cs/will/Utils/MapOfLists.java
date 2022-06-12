package edu.wisc.cs.will.Utils;

import java.util.*;
import java.util.Map.Entry;

/* A Map that maps Keys to List of values.
 *
 * Each key can be mapped to a list of values.
 *
 * @author twalker
 */
public class MapOfLists<Key, Value> implements Iterable<Value> {

    private Map<Key, List<Value>> map;

    public MapOfLists() {
    }

    public boolean containsKey(Key key) {
        return map != null && map.containsKey(key);
    }

    public void removeValue(Key key, Value value) {
        List<Value> list = map.get(key);

        if ( list != null ) {
            list.remove(value);
            if ( list.isEmpty() ) {
                map.remove(key);
            }
        }
    }

    public void add(Key key, Value e) {
        if ( map == null ) {
            map = createMap();
        }

        List<Value> result = map.get(key);
        if ( result == null ) {
            result = createValueList();
            map.put(key, result);
        }

        result.add(e);
    }


    public List<Value> getValues(Key key) {
        return map == null ? null : map.get(key);
    }

    protected List<Value> createValueList() {
        return new ArrayList<>();
    }

    private Map<Key, List<Value>> createMap() {
        return new HashMap<>();
    }

    @Override
    public String toString() {
        if ( map == null ) {
            return "{}";
        }
        else {
            StringBuilder stringBuilder = new StringBuilder();

            for (Entry<Key, List<Value>> entry : map.entrySet()) {
                stringBuilder.append(entry.getKey()).append(" => ");

                boolean first = true;
                for (Value value : entry.getValue()) {
                    if (!first) {
                        stringBuilder.append(",");
                    }
                    stringBuilder.append("\n").append("   ").append(value);

                    first = false;
                }

                stringBuilder.append(".\n");

            }
            return stringBuilder.toString();
        }
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final MapOfLists<Key, Value> other = (MapOfLists<Key, Value>) obj;
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
