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

    /*
     * Returns the number of Key entries in the map.
     */
    public int size() {
        return map == null ? 0 : map.size();
    }

    public boolean isEmpty() {
        return map == null || map.isEmpty();
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

    public Value getValue(Key key, int index) {
        if ( map == null ) {
            throw new IndexOutOfBoundsException("List does not exist for key " + key + ".");
        }
        else {
            List<Value> list;
            return (((list = map.get(key)) != null) ? list.get(index) : null);
        }
    }

    public void addAllValues(Key key, Collection<? extends Value> c) {
        if ( map == null ) {
            map = createMap();
        }

        List<Value> result = map.get(key);
        if ( result == null ) {
            result = createValueList();
            map.put(key, result);
        }

        result.addAll(c);
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

    public Set<Key> keySet() {
        if ( map != null) {
            return map.keySet();
        }
        else {
            return Collections.EMPTY_SET;
        }
    }

    public Collection<List<Value>> values() {
        if ( map != null ) {
            return map.values();
        }
        else {
            return Collections.EMPTY_SET;
        }
    }

    public Set<Entry<Key, List<Value>>> entrySet() {
        if ( map != null ) {
            return map.entrySet();
        }
        else {
            return Collections.EMPTY_SET;
        }
    }

    protected List<Value> createValueList() {
        return new ArrayList<>();
    }

    private Map<Key, List<Value>> createMap() {
        return new HashMap<>();
    }

    private String toString(String prefix) {
        if ( map == null ) {
            return prefix + "{}";
        }
        else {
            StringBuilder stringBuilder = new StringBuilder();

            for (Entry<Key, List<Value>> entry : map.entrySet()) {
                stringBuilder.append(prefix).append(entry.getKey()).append(" => ");

                boolean first = true;
                for (Value value : entry.getValue()) {
                    if (!first) {
                        stringBuilder.append(",");
                    }
                    stringBuilder.append("\n").append(prefix).append("   ").append(value);

                    first = false;
                }

                stringBuilder.append(".\n");

            }
            return stringBuilder.toString();
        }
    }

    @Override
    public String toString() {
        return toString("");
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
