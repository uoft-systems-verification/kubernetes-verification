(* Bug 01: loop_var. Go code: bugs/01_loop_var_repro.go.
   Each comment below gives the result of running the Go program (checked
   by go test) and the result of the goose translation, which the lemma
   proves (gen/code/example_com/goosebugs/bugs.v). *)
From New.proof Require Import proof_prelude.
From New.generatedproof Require Import example_com.goosebugs.bugs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : bugs.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) bugs := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) bugs := build_get_is_pkg_init_wf.

(* Running the Go program: LoopVarPointer() returns 0
     (go test: Test01LoopVar in bugs/01_loop_var_repro_test.go).
   Translated code, proved below: LoopVarPointer() returns 1,
     because the loop has one i, which the post statement i++ sets to 1
     after p = &i. *)
Lemma wp_LoopVarPointer :
  {{{ is_pkg_init bugs }}} @! bugs.LoopVarPointer #() {{{ RET #(W64 1); True }}}.
Proof.
  wp_start. wp_auto.
  iAssert (∃ (n: w64), "i" ∷ i_ptr ↦ n ∗
             "p" ∷ p_ptr ↦ (if decide (n = W64 0) then null else i_ptr) ∗
             "%Hn" ∷ ⌜uint.Z n ≤ 1⌝)%I with "[$i $p]" as "IH".
  { iPureIntro. word. }
  wp_for "IH".
  case_bool_decide as Hlt.
  - (* the only iteration: n = 0 *)
    assert (n = W64 0) as -> by word.
    wp_auto. wp_for_post.
    iFrame "HΦ i".
    case_decide as Heq; [exfalso; revert Heq; word|].
    iFrame. iPureIntro. word.
  - (* exit: n = 1, and p points to the shared i *)
    assert (n = W64 1) as -> by word.
    wp_auto. wp_end.
Qed.

End proof.
