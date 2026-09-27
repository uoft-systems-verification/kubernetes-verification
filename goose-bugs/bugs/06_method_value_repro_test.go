package bugs

import "testing"

// Go behaviour for bug 06 (method_value).
func Test06MethodValue(t *testing.T) {
	if got := MethodValue(); got != 1 {
		t.Errorf("MethodValue() = %d, want 1", got)
	}
}
