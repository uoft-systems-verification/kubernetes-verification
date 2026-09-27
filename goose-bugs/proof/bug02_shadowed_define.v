(* Bug 02: shadowed_define. Go code: bugs/02_shadowed_define_repro.go.
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

(* Running the Go program: ShadowDefine(x) returns x + 1
     (go test: Test02ShadowedDefine in bugs/02_shadowed_define_repro_test.go
      runs ShadowDefine(41) and gets 42).
   Translated code, proved below: ShadowDefine(x) returns 1 for every x,
     because the right-hand side reads the new, zero-valued x. *)
Lemma wp_ShadowDefine (x: w64) :
  {{{ is_pkg_init bugs }}} @! bugs.ShadowDefine #x {{{ RET #(W64 1); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

(* Running the Go program: ShadowForInit(p) returns p
     (go test: Test02ShadowedDefine in bugs/02_shadowed_define_repro_test.go
      passes a fresh pointer and gets it back).
   Translated code, proved below: ShadowForInit(p) returns nil for every p,
     because the loop's x is initialized from the new, nil x. *)
Lemma wp_ShadowForInit (p: loc) :
  {{{ is_pkg_init bugs }}} @! bugs.ShadowForInit #p {{{ RET #null; True }}}.
Proof.
  wp_start. wp_auto.
  iAssert ("i" ∷ i_ptr ↦ W64 0)%I with "[$i]" as "IH".
  wp_for "IH". rewrite bool_decide_true; last word. wp_auto.
  wp_for_post. wp_end.
Qed.

End proof.
