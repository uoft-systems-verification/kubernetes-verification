From New.proof.k8s_io.component_base Require Export featuregate_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.features.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : features.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) features := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) features := build_get_is_pkg_init_wf.

End proof.
