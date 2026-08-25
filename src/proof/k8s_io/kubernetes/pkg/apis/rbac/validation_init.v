From New.proof.k8s_io.apimachinery.pkg.api.validation Require Export path_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta.v1 Require Export validation_init.
From New.proof.k8s_io.apimachinery.pkg.util.validation Require Export field_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export rbac_init.
From New.proof.k8s_io.kubernetes.pkg.apis.core Require Export validation_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.apis.rbac.validation.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : validation.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) validation := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) validation := build_get_is_pkg_init_wf.

End proof.
