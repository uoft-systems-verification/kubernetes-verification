Require Export New.generatedproof.k8s_io.apiserver.pkg.storage.names.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : names.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) names := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) names := build_get_is_pkg_init_wf.

End proof.
