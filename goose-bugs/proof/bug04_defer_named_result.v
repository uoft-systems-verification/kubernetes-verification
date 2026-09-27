(* Bug 04: defer_named_result. Go code: bugs/04_defer_named_result_repro.go.
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

(* Running the Go program: DeferNamed() returns 10,
     because return 5 sets r = 5, then the deferred call doubles r
     (go test: Test04DeferNamedResult in bugs/04_defer_named_result_repro_test.go).
   Translated code, proved below: DeferNamed() returns 5,
     because the return value is computed before the deferred call runs. *)
Lemma wp_DeferNamed :
  {{{ is_pkg_init bugs }}} @! bugs.DeferNamed #() {{{ RET #(W64 5); True }}}.
Proof.
  wp_start. iApply wp_with_defer. iIntros (defer) "Hdefer". simpl.
  wp_auto. wp_end.
Qed.

End proof.
