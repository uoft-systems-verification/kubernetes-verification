From New.proof Require Export prelude.
Require Export New.proof.errors.
From New.proof Require Export io sync fmt.
From New.proof.sync Require Export atomic.
From New.proof.internal Require Export race synctest.
From New.proof Require Export rand_init.
Require Export New.generatedproof.iam_model.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) iammodel := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) iammodel := build_get_is_pkg_init_wf.

End proof.
