From New.proof.math Require Export big_init.
Require Export New.generatedproof.gopkg_in.inf_v0.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG : heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : inf.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) inf := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) inf := build_get_is_pkg_init_wf.
End proof.
