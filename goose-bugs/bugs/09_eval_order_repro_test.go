package bugs

import "testing"

// Go behaviour for bug 09 (eval_order).
func Test09EvalOrder(t *testing.T) {
	if got := EvalOrder(); got != 10 { // what gc does; the spec also allows 1
		t.Errorf("EvalOrder() = %d, want 10", got)
	}
}
