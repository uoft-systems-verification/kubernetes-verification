package bugs

import "testing"

// Go behaviour for bug 12 (u32_div).
func Test12U32Div(t *testing.T) {
	if got := DivU32(0x80000000, 2); got != 0x40000000 {
		t.Errorf("DivU32 = %#x, want 0x40000000", got)
	}
}
