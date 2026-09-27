package bugs

import "testing"

// Go behaviour for bug 08 (op_assign_twice).
func Test08OpAssignTwice(t *testing.T) {
	if got := OpAssignTwice(); got != 11 {
		t.Errorf("OpAssignTwice() = %d, want 11", got)
	}
}
