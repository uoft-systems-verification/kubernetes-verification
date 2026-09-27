package bugs

// The model and gc evaluate `x + f()` in different orders.
//
// The Go specification leaves the order between reading a variable and a
// call unspecified (its example: `x := []int{a, f()}` may be [1 2] or [2 2]).
// gc evaluates the call first; GooseLang evaluates operands left to right.
// Both are allowed, but a proof about the model then describes a different
// execution than the compiled program.
//
// Go (gc): EvalOrder() == 10. Model: 1.

func EvalOrder() uint64 {
	var x uint64 = 1
	f := func() uint64 { x = 10; return 0 }
	return x + f()
}
