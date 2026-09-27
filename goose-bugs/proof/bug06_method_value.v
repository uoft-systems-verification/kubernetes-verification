(* Bug 06: method_value. Go code: bugs/06_method_value_repro.go.
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

(* Running the Go program: MethodValue() returns 1,
     because g := s.Get copies s while s.A is 1
     (go test: Test06MethodValue in bugs/06_method_value_repro_test.go).
   Translated code, proved below: MethodValue() returns 2,
     because g loads s when it is called, after s.A = 2. *)
Lemma wp_MethodValue :
  {{{ is_pkg_init bugs }}} @! bugs.MethodValue #() {{{ RET #(W64 2); True }}}.
Proof.
  wp_start. wp_auto.
  wp_method_call. wp_call. wp_auto.
  wp_method_call. wp_call. rewrite /bugs.S__Getⁱᵐᵖˡ. wp_auto. wp_end.
Qed.

End proof.
