(* Bug 05: empty_block. Go code: bugs/05_empty_block_repro.go.
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

(* Running the Go program: EmptyBlock(x) returns x + 11
     (go test: Test05EmptyBlock in bugs/05_empty_block_repro_test.go
      runs EmptyBlock(5) and gets 16).
   Translated code, proved below: EmptyBlock(x) returns #() (unit) for every x,
     because everything after the empty block is dropped. *)
Lemma wp_EmptyBlock (x: w64) :
  {{{ is_pkg_init bugs }}} @! bugs.EmptyBlock #x {{{ RET #(); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

End proof.
