Require Export New.generatedproof.k8s_io.kubernetes.pkg.registry.core.serviceaccount.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : serviceaccount.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) serviceaccount := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) serviceaccount := build_get_is_pkg_init_wf.

End proof.
