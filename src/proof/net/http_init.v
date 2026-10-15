Require Export New.generatedproof.net.http.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : http.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) http := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) http := build_get_is_pkg_init_wf.

End proof.
