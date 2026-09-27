package bugs

import "testing"

// Go behaviour for bug 04 (defer_named_result).
func Test04DeferNamedResult(t *testing.T) {
	if got := DeferNamed(); got != 10 {
		t.Errorf("DeferNamed() = %d, want 10", got)
	}
}
