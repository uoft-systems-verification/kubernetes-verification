// Package crash holds bug 14, which makes goose crash, so it cannot share a
// package with the other reproductions.
package crash

// ++ / -- on 16-bit integers crashes goose.
//
// incDecStmt picks the literal 1 by type with cases for 64-, 32- and 8-bit
// integers only; for int16/uint16 the operand stays nil and goose panics
// while printing the translation.
//
// Go: Inc16(41) == 42. Goose: panics (nil pointer dereference in
// glang.BinaryExpr.Coq).
func Inc16(x int16) int16 {
	x++
	return x
}
