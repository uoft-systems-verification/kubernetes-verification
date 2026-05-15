From New.proof Require Import prelude empty_ffi.

Axiom conflict_error: interface.t → Prop.
Axiom conflict_error_dec: ∀ err, Decision (conflict_error err).
Global Existing Instance conflict_error_dec.
