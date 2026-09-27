package crash

import "testing"

// Go behaviour for bug 14 (incdec16).
func Test14Incdec16(t *testing.T) {
	if got := Inc16(41); got != 42 {
		t.Errorf("Inc16(41) = %d, want 42", got)
	}
}
