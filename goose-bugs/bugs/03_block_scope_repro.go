package bugs

// A variable declared in an explicit block stays in scope after the block.
//
// Goose sequences a block statement with the statements after it
// (stmtList/SeqExpr) and prints the block's `let:` without parentheses, so in
// the Rocq text the let extends over the rest of the function. Applies to
// explicit { ... } blocks (if/for bodies are parenthesized). Also described
// in ../goose-block-scope.md.
//
// Go: each function returns its argument x.
// Model: BlockScope returns 42, BlockScopeVar 42, BlockScopeNested 30.

func BlockScope(x uint64) uint64 {
	{
		x := uint64(42)
		_ = x
	}
	return x
}

func BlockScopeVar(x uint64) uint64 {
	{
		var x = uint64(42)
		_ = x
	}
	return x
}

func BlockScopeNested(x uint64) uint64 {
	{
		x := uint64(20)
		{
			x := uint64(30)
			_ = x
		}
		_ = x
	}
	return x
}
