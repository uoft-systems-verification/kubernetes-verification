(* Bug 08: op_assign_twice. Go code: bugs/08_op_assign_twice_repro.go.
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

(* Running the Go program: OpAssignTwice() returns 11,
     because *g() += 1 calls g once: count = 1, x = 1
     (go test: Test08OpAssignTwice in bugs/08_op_assign_twice_repro_test.go).
   Translated code, proved below: OpAssignTwice() returns 21,
     because g is called twice: count = 2, x = 1. *)
Lemma wp_OpAssignTwice :
  {{{ is_pkg_init bugs }}} @! bugs.OpAssignTwice #() {{{ RET #(W64 21); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

End proof.
