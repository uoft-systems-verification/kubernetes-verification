(* Bug 10: nil_map. Go code: bugs/10_nil_map_repro.go.
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

(* Running the Go program: NilMapLen() returns 0
     (go test: Test10NilMap in bugs/10_nil_map_repro_test.go).
   Translated code: len(m) on the nil map gets stuck (no step applies),
     because the nil map is the null location and len reads it.
   Being stuck is the absence of a rule, which cannot be proved from the
   go.Semantics assumptions; what is proved below are those two facts. *)
Lemma map_nil_is_null : map.nil = null.
Proof. reflexivity. Qed.

Lemma len_map_reads `{!go.MapSemantics} :
  FuncUnfold go.len [go.MapType go.uint64 go.uint64]
    (λ: "m", InternalMapLength (Read "m"))%V.
Proof. apply _. Qed.

End proof.
