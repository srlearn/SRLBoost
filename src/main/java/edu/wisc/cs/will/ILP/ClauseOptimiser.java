package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.Utils.Utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/*
 * @author vsc
 * This is a clause optimiser in the style of  [VSC,AS,HB et al, JMLR03].
 */
public class ClauseOptimiser {

    public ClauseOptimiser() {
    }

    List<List<Literal>> bodyToBodies(Literal head, List<Literal> body) {
        if (body.size() == 0) {
            return (List<List<Literal>>) Collections.EMPTY_LIST;
        }
        else if (body.size() == 1) {
            return Collections.singletonList(body);
        }
        else {
            return separateComponents(head, body);
        }
    }

    /**
     * Constructs a new optimised clause.
     */
    private int[] clauseToComponents(Literal head, List<Literal> body) {
        Collection<Variable> headvars = head.collectAllVariables();
        int[] components;

        components = new int[body.size()];
        ArrayList<Collection<Variable>> lvarsets = new ArrayList<>(components.length);

        int i = 0;
        // check independence
        // by dividing into independent components.
        for (Literal lit : body) {
            int component = i;

            Collection<Variable> litvars = lit.collectAllVariables();
            // mark as being in its own component
            components[i] = i;
            // literals have no variable
            if (litvars == null) {
                // component has these variables
                lvarsets.add(i, null);
                continue;
            }
            // head vars are assume to be ground
            litvars.removeAll(headvars);
            // component has these variables
            lvarsets.add(i, litvars);
            for (int j = 0; j < i; j++) {
                // get the variables again
                Collection<Variable> next = lvarsets.get(j);
                for (Variable v : litvars) {
                    if (next.contains(v)) {
                        component = component_merge(j, component, components);
                    }
                }
            }
            components[i] = component;
            i++;
        }
        return components;
    }

    // TODO(@hayesall): This function can likely be removed.
    private List<List<Literal>> separateComponents(Literal head, List<Literal> body) {

        if (body == null) {
            return null;
        }

        try {
            int[] components = clauseToComponents(head, body);
            int total_components = normalise_components(components);

            int[] map = new int[body.size()];
            int[] size = new int[total_components];

            int next_component = 0;
            for (int i = 0; i < body.size(); i++) {
                int component;
                if (i == components[i]) {
                    size[next_component] = 0;
                    map[i] = next_component++;
                }
                component = map[components[i]];
                size[component]++;
            }

            List<List<Literal>> listOfLits = new ArrayList<>(total_components);
            for (int i = 0; i < total_components; i++) {
                listOfLits.add(new ArrayList<>(size[i]));
            }

            for (int i = 0; i < body.size(); i++) {
                listOfLits.get(map[components[i]]).add(body.get(i));
            }
            return listOfLits;
        } catch (Exception e) {
            Utils.reportStackTrace(e);
            Utils.error("Problem running emulator.");
            return null;
        }
    }

    // make sure we are pointing to the representative
    private int deref_component(int j, int[] components) {
        while (components[j] != j) {
            j = components[j];
        }
        return j;
    }

    // if two components share variables
    // make sure one points to the other
    private int component_merge(int j, int component, int[] components) {
        int k = deref_component(j, components);
        if (k > component) {
            components[k] = component;

            return component;
        }
        else {
            components[component] = k;
            return k;
        }
    }

    private int normalise_components(int[] components) {
        int total_components = 0;

        for (int i = 0; i < components.length; i++) {
            components[i] = deref_component(i, components);
            if (components[i] == i) {
                total_components++;
            }
        }
        return total_components;
    }

}
