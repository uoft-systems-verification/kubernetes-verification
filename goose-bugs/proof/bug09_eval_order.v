(* Bug 09: eval_order. Go code: bugs/09_eval_order_repro.go.
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

(* Running the Go program: EvalOrder() returns 10,
     because gc calls f, which sets x = 10, before reading x; the Go
     specification also allows 1
     (go test: Test09EvalOrder in bugs/09_eval_order_repro_test.go).
   Translated code, proved below: EvalOrder() returns 1,
     because x is read before f is called. *)
Lemma wp_EvalOrder :
  {{{ is_pkg_init bugs }}} @! bugs.EvalOrder #() {{{ RET #(W64 1); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

End proof.
