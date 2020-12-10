package edu.wisc.cs.will.ResThmProver;

/*
 * @author twalker
 */
public enum VariantClauseAction {

    SILENTLY_KEEP_VARIANTS("noAction", false, false),
    WARN_AND_KEEP_VARIANTS("warn", true, false),
    SILENTLY_REMOVE_VARIANTS("silentlyRemove", false, true),
    WARN_AND_REMOVE_VARIANTS("remove", true, true);

    private final String parameterSetting;
    private final boolean warn;
    private final boolean remove;

    VariantClauseAction(String parameterSetting, boolean warn, boolean remove) {
        this.parameterSetting = parameterSetting;
        this.warn = warn;
        this.remove = remove;
    }

    @Override
    public String toString() {
        return parameterSetting;
    }

    public boolean isRemoveEnabled() {
        return remove;
    }

    public boolean isWarnEnabled() {
        return warn;
    }

    public boolean isCheckRequired() {
        return warn || remove;
    }

    public static VariantClauseAction fromString(String setting) {
        for (VariantClauseAction action : values()) {
            if ( setting.equalsIgnoreCase(action.parameterSetting) ) {
                return action;
            }
        }
        return null;
    }
}
