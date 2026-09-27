package bugs

import "testing"

// Go behaviour for bug 07 (tuple_assign).
func Test07TupleAssign(t *testing.T) {
	if got := TupleAssign(); got != 70 {
		t.Errorf("TupleAssign() = %d, want 70", got)
	}
}
