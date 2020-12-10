package edu.wisc.cs.will.Utils;

class WILLthrownError extends RuntimeException { // Should this extend Error instead?
    
    private static final long serialVersionUID = 697058652207737070L;

    WILLthrownError(String msg) {
        super(msg);
    }
}
