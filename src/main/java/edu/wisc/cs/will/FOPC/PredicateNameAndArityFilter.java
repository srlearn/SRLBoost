package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Filter;

import java.util.HashMap;
import java.util.Map;

/*
 * @author twalker
 */
public class PredicateNameAndArityFilter implements Filter<PredicateNameAndArity> {

    private final HandleFOPCstrings stringHandler;

    private Map<PredicateName, ArityFilter> nameToArityMap;

    PredicateNameAndArityFilter(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;
    }

    public boolean includeElement(PredicateName predicateName, int arity) {
        boolean result = false;

        if ( nameToArityMap != null) {
            ArityFilter arityFilter = nameToArityMap.get(predicateName);

            if ( arityFilter != null ) {
                result = arityFilter.includeElement(arity);
            }
        }

        return result;
    }

    public void addLiteral(String predicateName, int arity) {
        addLiteral(stringHandler.getPredicateName(predicateName), arity);
    }

    private void addLiteral(PredicateName predicateName, int arity) {
        addArityFilterEntry(predicateName, arity);
    }

    public void addLiteral(PredicateNameAndArity predicateNameArity) {
        addArityFilterEntry(predicateNameArity.getPredicateName(), predicateNameArity.getArity());
    }

    private void addArityFilterEntry(PredicateName predicateName, int arity) {
        if (nameToArityMap == null) {
            nameToArityMap = new HashMap<>();
        }

        ArityFilter arityFilter = nameToArityMap.get(predicateName);

        if (arityFilter == null) {
            arityFilter = new ArityFilter();
            nameToArityMap.put(predicateName, arityFilter);
        }

        if (arity == -1) {
            arityFilter.setIncludeAllArities(true);
        }
        else {
            arityFilter.addArity(arity);
        }
    }

    @Override
    public String toString() {

        StringBuilder sb = new StringBuilder();
        sb.append("{");

        if ( nameToArityMap != null ) {
            for (Map.Entry<PredicateName, ArityFilter> entry : nameToArityMap.entrySet()) {
                PredicateName name = entry.getKey();
                ArityFilter arityFilter = entry.getValue();
                if ( arityFilter.isIncludeAllArities() ) {
                    sb.append(", ");
                    sb.append(name.name).append("/").append("*");
                }
                else {
                    for (Integer arity : arityFilter) {
                        sb.append(", ");
                        sb.append(name.name).append("/").append(arity);

                    }
                }
            }
        }
        sb.append("}");
        return sb.toString();

    }


}
