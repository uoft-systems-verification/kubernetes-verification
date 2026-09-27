package bugs

// len and delete of a nil map get stuck in the model (Rocq semantics).
//
// map.nil is null (new/golang/defn/postlang.v) and go.len on maps is
// `λ: "m", InternalMapLength (Read "m")` (new/golang/defn/map.v), which reads
// the null location; go.delete likewise. Lookups check for nil explicitly.
// Code calling len/delete on a possibly-nil map cannot be verified.
//
// Go: NilMapLen() == 0. Model: stuck.

func NilMapLen() int {
	var m map[uint64]uint64
	return len(m)
}
