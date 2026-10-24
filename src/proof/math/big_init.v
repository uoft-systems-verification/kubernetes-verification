Require Export New.generatedproof.math.big.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG : heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : big.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) big := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) big := build_get_is_pkg_init_wf.
End proof.
