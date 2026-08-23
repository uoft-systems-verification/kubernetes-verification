Require Export New.generatedproof.regexp.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : regexp.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) regexp := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) regexp := build_get_is_pkg_init_wf.

End proof.
