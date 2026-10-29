Require Export New.generatedproof.k8s_io.kubernetes.pkg.registry.apps.daemonset.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : daemonset.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) daemonset := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) daemonset := build_get_is_pkg_init_wf.

End proof.
