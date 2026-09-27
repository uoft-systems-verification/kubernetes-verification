package shadowrepro

import "testing"

// Go behaviour. The goose translation instead returns 1 for the first four
// and nil for ForInit (proved in proof/Repro.v).
func TestGo(t *testing.T) {
	for _, c := range []struct {
		name      string
		got, want int
	}{
		{"Define(41)", Define(41), 42},
		{"VarDecl(41)", VarDecl(41), 42},
		{"IfInit(41)", IfInit(41), 42},
		{"IfInit(-5)", IfInit(-5), 0},
		{"MultiRet(41)", MultiRet(41), 42},
	} {
		if c.got != c.want {
			t.Errorf("%s = %d, want %d", c.name, c.got, c.want)
		}
	}

	p := new(int)
	if got := ForInit(p); got != p {
		t.Errorf("ForInit(p) = %p, want p = %p", got, p)
	}
}
