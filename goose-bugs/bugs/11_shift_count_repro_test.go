package bugs

import "testing"

// Go behaviour for bug 11 (shift_count).
func Test11ShiftCount(t *testing.T) {
	if got := Shift8(1, 256); got != 0 {
		t.Errorf("Shift8(1, 256) = %d, want 0", got)
	}
}
