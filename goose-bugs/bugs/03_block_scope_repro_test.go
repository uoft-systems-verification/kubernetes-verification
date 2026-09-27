package bugs

import "testing"

// Go behaviour for bug 03 (block_scope).
func Test03BlockScope(t *testing.T) {
	for _, f := range []func(uint64) uint64{BlockScope, BlockScopeVar, BlockScopeNested} {
		if got := f(10); got != 10 {
			t.Errorf("got %d, want 10", got)
		}
	}
}
