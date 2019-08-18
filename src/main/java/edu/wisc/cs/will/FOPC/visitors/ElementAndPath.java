package edu.wisc.cs.will.FOPC.visitors;

import java.util.Objects;

import edu.wisc.cs.will.FOPC.SentenceOrTerm;

/*
 *
 * @author twalker
 */
public class ElementAndPath {
    private SentenceOrTerm element;
    private ElementPath path;

    ElementAndPath(SentenceOrTerm element, ElementPath path) {
        this.element = element;
        this.path = path;
    }

    public SentenceOrTerm getElement() {
        return element;
    }

    public ElementPath getPath() {
        return path;
    }

    public void setPath(ElementPath path) {
        this.path = path;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final ElementAndPath other = (ElementAndPath) obj;
        if (!Objects.equals(this.element, other.element)) {
            return false;
        }
        return Objects.equals(this.path, other.path);
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 79 * hash + (this.element != null ? this.element.hashCode() : 0);
        hash = 79 * hash + (this.path != null ? this.path.hashCode() : 0);
        return hash;
    }

    @Override
    public String toString() {
        return "{" + "element=" + element + ", path=" + path + '}';
    }
}
