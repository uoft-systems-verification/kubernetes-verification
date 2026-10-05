From New.proof Require Import prelude empty_ffi.
From New.proof Require Export reflect_init.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : reflect.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

(* Trusted: [reflect.DeepEqual] is untranslated; it only reads its arguments
   and returns some boolean. *)
Lemma wp_DeepEqual (a b : interface.t) :
  {{{ is_pkg_init reflect }}}
    @! reflect.DeepEqual #a #b
  {{{ (r : bool), RET #r; True }}}.
Proof. Admitted.

End proof.
