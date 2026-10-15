From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export equality_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.controller.deployment.util.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : util.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) util := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) util := build_get_is_pkg_init_wf.

End proof.
