package bugs

// Integer ^x is translated as boolean negation.
//
// unaryExpr returns glang.NotExpr for token.XOR, printed ⟨go.bool⟩!, whose
// only rule is for booleans, so the model gets stuck on an integer. The
// semantics has the right operator, ⟨t⟩^ (GoComplement).
//
// Go: Complement(0) == 0xFFFFFFFFFFFFFFFF. Model: stuck.

func Complement(x uint64) uint64 {
	return ^x
}
