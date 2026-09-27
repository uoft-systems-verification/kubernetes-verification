package bugs

// Tuple assignment evaluates left-hand operands after earlier stores.
//
// Go evaluates index expressions and pointer indirections on the left, and
// the right-hand sides, before any assignment. Goose (assignStmt) computes
// each left-hand address at its store, after earlier stores.
// Likewise `i, a[i] = 1, 5` writes a[1] instead of a[0].
//
// Go: TupleAssign() == 70 (*p is x, the old p). Model: 7 (writes y).

func TupleAssign() uint64 {
	var x, y uint64
	p := &x
	p, *p = &y, 7
	return x*10 + y
}
