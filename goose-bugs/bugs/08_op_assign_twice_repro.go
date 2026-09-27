package bugs

// Compound assignment evaluates its left operand twice.
//
// assignOpStmt builds `lhs = lhs op rhs`, translating lhs twice; incDecStmt
// does the same for ++/--. Side effects in the left operand run twice:
// *g() += 1, a[f()]++, m[f()] += 1.
//
// Go: OpAssignTwice() == 11 (g runs once). Model: 21.

func OpAssignTwice() uint64 {
	var x, count uint64
	g := func() *uint64 { count++; return &x }
	*g() += 1
	return count*10 + x
}
