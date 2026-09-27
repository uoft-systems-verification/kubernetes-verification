package bugs

// The shift count is truncated to the type of the shifted value.
//
// binExpr converts both operands of a shift to the left operand's type, so a
// wide count is truncated: uint8(1) << uint64(256) shifts by 0.
//
// Go: Shift8(1, 256) == 0. Model: 1.

func Shift8(x uint8, n uint64) uint8 {
	return x << n
}
