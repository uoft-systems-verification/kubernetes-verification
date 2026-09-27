package bugs

// uint32 division is signed (Rocq semantics).
//
// new/golang/defn/predeclared.v defines div_uint32 and remainder_uint32 with
// word.divs / word.mods; every other unsigned type uses divu / modu.
//
// Go: DivU32(0x80000000, 2) == 0x40000000. Model: 0xC0000000.

func DivU32(a, b uint32) uint32 {
	return a / b
}
