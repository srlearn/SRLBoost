package edu.wisc.cs.will.Utils;

public class WILLthrownError extends RuntimeException { // Should this extend Error instead?
    WILLthrownError(String msg) {
        super(msg);
    }
}
