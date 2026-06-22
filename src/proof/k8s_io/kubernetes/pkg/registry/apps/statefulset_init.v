Require Export New.generatedproof.k8s_io.kubernetes.pkg.registry.apps.statefulset.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : statefulset.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) statefulset := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) statefulset := build_get_is_pkg_init_wf.

End proof.
