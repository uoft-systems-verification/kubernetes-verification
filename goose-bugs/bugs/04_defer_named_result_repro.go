package bugs

// Deferred calls cannot change named results.
//
// In Go, `return 5` assigns the named result r, then deferred calls run (and
// may change r), and r is returned. Goose translates `return 5` without
// assigning r, and wrap_defer (new/golang/defn/defer.v) computes the return
// value before running deferred calls. Breaks the common idiom
// `defer func() { err = errors.Join(err, f.Close()) }()` and recover handlers.
//
// Go: DeferNamed() == 10. Model: 5.

func DeferNamed() (r uint64) {
	defer func() { r *= 2 }()
	return 5
}
