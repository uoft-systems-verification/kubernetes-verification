package bugs

import "testing"

// Go behaviour for bug 10 (nil_map).
func Test10NilMap(t *testing.T) {
	if got := NilMapLen(); got != 0 {
		t.Errorf("NilMapLen() = %d, want 0", got)
	}
}
