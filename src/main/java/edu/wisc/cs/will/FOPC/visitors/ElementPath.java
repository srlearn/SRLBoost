package edu.wisc.cs.will.FOPC.visitors;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

public class ElementPath implements Comparable<ElementPath>{

    private ElementPath parent;

    private final int index;

    public ElementPath(ElementPath parent, int index) {
        this.parent = parent;
        this.index = index;
    }

    public ElementPath(int index) {
        this.index = index;
    }

    private List<Integer> asList() {
        List<Integer> list = new ArrayList<>();
        ElementPath ep = this;
        while (ep != null) {
            list.add(0, ep.index);
            ep = ep.parent;
        }
        return list;
    }

    public ElementPath getParent() {
        return parent;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final ElementPath other = (ElementPath) obj;
        if (!Objects.equals(this.parent, other.parent)) {
            return false;
        }
        return this.index == other.index;
    }

    public int compareTo(ElementPath that) {
        List<Integer> thisList = this.asList();
        List<Integer> thatList = that.asList();

        for (int i = 0; i < thisList.size() && i < thatList.size(); i++) {
            if ( thisList.get(i) < thatList.get(i) ) {
                return -1;
            }
            else if ( thisList.get(i) > thatList.get(i) ) {
                return 1;
            }
        }

        // If we made it this far, the lists are the same up
        // to the length of the shortest path.
        // If this is true, then the path that is shorter comes first.
        return thisList.size() - thatList.size();
    }
}
