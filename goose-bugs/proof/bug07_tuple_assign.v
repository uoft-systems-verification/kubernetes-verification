(* Bug 07: tuple_assign. Go code: bugs/07_tuple_assign_repro.go.
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

(* Running the Go program: TupleAssign() returns 70,
     because p, *p = &y, 7 stores 7 into x, through the old p
     (go test: Test07TupleAssign in bugs/07_tuple_assign_repro_test.go).
   Translated code, proved below: TupleAssign() returns 7,
     because *p is evaluated after p = &y, so 7 is stored into y. *)
Lemma wp_TupleAssign :
  {{{ is_pkg_init bugs }}} @! bugs.TupleAssign #() {{{ RET #(W64 7); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

End proof.
