(* Bug 11: shift_count. Go code: bugs/11_shift_count_repro.go.
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

(* Running the Go program: Shift8(1, 256) returns 0,
     because shifting a uint8 by 8 or more bits gives 0
     (go test: Test11ShiftCount in bugs/11_shift_count_repro_test.go).
   Translated code, proved below: Shift8(1, 256) returns 1,
     because the count is converted to uint8 (256 -> 0) before shifting. *)
Lemma wp_Shift8 :
  {{{ is_pkg_init bugs }}} @! bugs.Shift8 #(W8 1) #(W64 256) {{{ RET #(W8 1); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

End proof.
