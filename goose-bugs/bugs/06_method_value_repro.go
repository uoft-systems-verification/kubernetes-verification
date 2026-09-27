package bugs

// A method value does not copy a value receiver.
//
// Go evaluates (copies) the receiver when the method value s.Get is created.
// Goose emits MethodResolve (go.PointerType S) "Get" "s", whose wrapper
// `λ: "$r", MethodResolve S "Get" (![S] "$r")` loads s only when g is called.
//
// Go: MethodValue() == 1. Model: 2.

type S struct{ A uint64 }

func (s S) Get() uint64 { return s.A }

func MethodValue() uint64 {
	s := S{A: 1}
	g := s.Get
	s.A = 2
	return g()
}
