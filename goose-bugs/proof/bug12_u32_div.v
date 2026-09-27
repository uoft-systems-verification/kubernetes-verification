(* Bug 12: u32_div. Go code: bugs/12_u32_div_repro.go.
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

(* Running the Go program: DivU32(0x80000000, 2) returns 0x40000000 (1073741824)
     (go test: Test12U32Div in bugs/12_u32_div_repro_test.go).
   Translated code, proved below: DivU32(0x80000000, 2) returns 0xC0000000 (3221225472),
     because the uint32 division rule is signed (word.divs). *)
Lemma wp_DivU32 :
  {{{ is_pkg_init bugs }}}
    @! bugs.DivU32 #(W32 2147483648) #(W32 2)
  {{{ RET #(W32 3221225472); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

End proof.
