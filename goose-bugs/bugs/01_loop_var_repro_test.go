package bugs

import "testing"

// Go behaviour for bug 01 (loop_var).
func Test01LoopVar(t *testing.T) {
	if got := LoopVarPointer(); got != 0 {
		t.Errorf("LoopVarPointer() = %d, want 0", got)
	}
}
