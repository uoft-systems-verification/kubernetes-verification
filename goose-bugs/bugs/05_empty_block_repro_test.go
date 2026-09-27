package bugs

import "testing"

// Go behaviour for bug 05 (empty_block).
func Test05EmptyBlock(t *testing.T) {
	if got := EmptyBlock(5); got != 16 {
		t.Errorf("EmptyBlock(5) = %d, want 16", got)
	}
}
