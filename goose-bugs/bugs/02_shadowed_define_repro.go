package bugs

// A short variable declaration that shadows a variable used in its own
// initializer reads the new, zero-valued variable.
//
// In Go the scope of x in `x := e` begins after the statement, so e sees the
// outer x. Goose (defineStmt) allocates the new x before evaluating e. Affects
// :=, var, if/for/switch initializers and multi-value :=.
//
// Go: ShadowDefine(x) == x + 1 and ShadowForInit(p) == p.
// Model: ShadowDefine(x) == 1 and ShadowForInit(p) == nil.

func ShadowDefine(x uint64) uint64 {
	{
		x := x + 1
		return x
	}
}

func ShadowForInit(x *uint64) *uint64 {
	for i, x := 0, x; i < 1; i++ {
		return x
	}
	return nil
}
