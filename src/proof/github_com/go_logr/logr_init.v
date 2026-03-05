Require Export New.generatedproof.github_com.go_logr.logr.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : logr.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) logr := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) logr := build_get_is_pkg_init_wf.

End proof.
