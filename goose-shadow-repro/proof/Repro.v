(* Specs proved about the goose translation (gen/code/example_com/shadowrepro.v).
   Each contradicts the Go behaviour checked in repro_test.go.

   The preconditions are satisfiable (is_pkg_init holds after package
   initialization), so the specs are not vacuous. They are partial-correctness
   specs: each translated function either returns the stated value or does not
   return. Both differ from Go, which returns a different value. *)
From New.proof Require Import proof_prelude.
From New.generatedproof Require Import example_com.shadowrepro.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : shadowrepro.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) shadowrepro := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) shadowrepro := build_get_is_pkg_init_wf.

(* Go returns x + 1; the translation always returns 1. *)
Lemma wp_Define (x: w64) :
  {{{ is_pkg_init shadowrepro }}} @! shadowrepro.Define #x {{{ RET #(W64 1); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

Lemma wp_VarDecl (x: w64) :
  {{{ is_pkg_init shadowrepro }}} @! shadowrepro.VarDecl #x {{{ RET #(W64 1); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

Lemma wp_IfInit (x: w64) :
  {{{ is_pkg_init shadowrepro }}} @! shadowrepro.IfInit #x {{{ RET #(W64 1); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

(* pair has no shadowing and is translated correctly. *)
Lemma wp_pair (x: w64) :
  {{{ is_pkg_init shadowrepro }}}
    @! shadowrepro.pair #x
  {{{ RET (#(word.add x (W64 1)), #true); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

(* pair is called with 0 instead of x. *)
Lemma wp_MultiRet (x: w64) :
  {{{ is_pkg_init shadowrepro }}} @! shadowrepro.MultiRet #x {{{ RET #(W64 1); True }}}.
Proof. wp_start. wp_auto. wp_apply wp_pair. wp_end. Qed.

(* Go returns p. The translated loop variable starts as nil, so the
   translation returns null for every p. *)
Lemma wp_ForInit (p: loc) :
  {{{ is_pkg_init shadowrepro }}} @! shadowrepro.ForInit #p {{{ RET #null; True }}}.
Proof.
  wp_start. wp_auto.
  iAssert ("i" ∷ i_ptr ↦ W64 0)%I with "[$i]" as "IH".
  wp_for "IH". rewrite bool_decide_true; last word. wp_auto.
  wp_for_post. wp_end.
Qed.

End proof.
