package bugs

// Everything after an empty block is dropped.
//
// stmtList (goose/goose.go) returns `do: #()` for an empty statement list
// without its continuation, so an empty { } discards the rest of the function.
//
// Go: EmptyBlock(5) == 16. Model: returns #() (unit) for every x.

func EmptyBlock(x uint64) uint64 {
	x = x + 1
	{
	}
	x = x + 10
	return x
}
