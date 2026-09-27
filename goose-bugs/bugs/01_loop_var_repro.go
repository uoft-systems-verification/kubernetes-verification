package bugs

// Loop variables are shared across iterations.
//
// Since Go 1.22 each iteration of a for loop (and of a range loop) has its own
// copy of the loop variables; this module and perennial itself are go >= 1.22.
// Goose allocates the loop variable once, before the loop (forStmt and
// rangeStmt in goose/goose.go), so a variable that escapes an iteration
// through &i, a closure or a goroutine is changed by later iterations.
//
// Go: LoopVarPointer() == 0 (p points to the first iteration's i).
// Model: 1 (the post statement i++ changes the only i).
// Affects e.g. `for i := range xs { go func() { use(i) }() }` written without
// the pre-1.22 `i := i`.

func LoopVarPointer() uint64 {
	var p *uint64
	for i := uint64(0); i < 1; i++ {
		p = &i
	}
	return *p
}
