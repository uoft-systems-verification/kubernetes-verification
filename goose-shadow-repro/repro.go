// Minimal reproduction: goose mistranslates a short variable declaration whose
// right-hand side mentions an outer variable of the same name.
package shadowrepro

// x := x + 1 in a nested block. Go: returns x + 1.
func Define(x int) int {
	{
		x := x + 1
		return x
	}
}

// Same with var. Go: returns x + 1.
func VarDecl(x int) int {
	{
		var x = x + 1
		return x
	}
}

// if-statement initializer. Go: returns x + 1 if it is positive, else 0.
func IfInit(x int) int {
	if x := x + 1; x > 0 {
		return x
	}
	return 0
}

func pair(x int) (int, bool) { return x + 1, true }

// Multi-value define. Go: returns x + 1.
func MultiRet(x int) int {
	{
		x, ok := pair(x)
		_ = ok
		return x
	}
}

// for-statement initializer (the original bug). Go: returns x.
func ForInit(x *int) *int {
	for i, x := 0, x; i < 1; i++ {
		return x
	}
	return nil
}
