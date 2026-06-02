From New.proof Require Export prelude.
From New.proof.iam_model Require Export common.
Require Export New.generatedproof.iam_model.example.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : example.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) example := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) example := build_get_is_pkg_init_wf.

End proof.
