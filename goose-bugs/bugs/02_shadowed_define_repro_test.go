package bugs

import "testing"

// Go behaviour for bug 02 (shadowed_define).
func Test02ShadowedDefine(t *testing.T) {
	if got := ShadowDefine(41); got != 42 {
		t.Errorf("ShadowDefine(41) = %d, want 42", got)
	}
	p := new(uint64)
	if got := ShadowForInit(p); got != p {
		t.Errorf("ShadowForInit(p) = %p, want p", got)
	}
}
