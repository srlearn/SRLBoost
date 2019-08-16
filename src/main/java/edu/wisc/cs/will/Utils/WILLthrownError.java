package edu.wisc.cs.will.Utils;

@SuppressWarnings("serial")
public class WILLthrownError extends RuntimeException { // Should this extend Error instead?
    WILLthrownError(String msg) {
        super(msg);
    }
}
