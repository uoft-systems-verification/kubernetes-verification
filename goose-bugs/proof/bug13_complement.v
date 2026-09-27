(* Bug 13: complement. Go code: bugs/13_complement_repro.go.
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

(* Running the Go program: Complement(0) returns 0xFFFFFFFFFFFFFFFF
     (go test: Test13Complement in bugs/13_complement_repro_test.go).
   Translated code: gets stuck, because ^x is translated as boolean negation
     ⟨go.bool⟩! applied to a uint64, and no rule applies.
   Being stuck cannot be proved; the lemma below pins down the translation. *)
Lemma complement_translation :
  bugs.Complementⁱᵐᵖˡ =
  (λ: "x", exception_do (let: "x" := GoAlloc go.uint64 "x" in
                         return: (⟨go.bool⟩! (![go.uint64] "x"))))%V.
Proof. reflexivity. Qed.

End proof.
