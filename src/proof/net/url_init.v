Require Export New.generatedproof.net.url.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : url.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) url := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) url := build_get_is_pkg_init_wf.

End proof.
