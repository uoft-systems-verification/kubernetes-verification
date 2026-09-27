package bugs

import "testing"

// Go behaviour for bug 13 (complement).
func Test13Complement(t *testing.T) {
	if got := Complement(0); got != 0xFFFFFFFFFFFFFFFF {
		t.Errorf("Complement(0) = %#x", got)
	}
}
