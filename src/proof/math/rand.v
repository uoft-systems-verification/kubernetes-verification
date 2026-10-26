From New.proof Require Export rand_init.
From New.proof Require Import prelude empty_ffi.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : rand.Assumptions}.
Local Set Default Proof Using "All".

(** Trusted standard-library boundary: Int63 returns a nonnegative int64.
    No uniqueness or eventual freshness is assumed. *)
Lemma wp_Int63 :
  {{{ is_pkg_init rand }}}
    @! rand.Int63 #()
  {{{ (n : w64), RET #n; ⌜ 0 ≤ sint.Z n ⌝ }}}.
Proof. Admitted.

End proof.
