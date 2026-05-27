From New.proof.k8s_io.apimachinery.pkg.api Require Export resource_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.apis.core.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : core.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) pkg_id.core := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) pkg_id.core := build_get_is_pkg_init_wf.

End proof.
