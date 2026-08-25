From New.proof Require Export context.
From New.proof.k8s_io.api.rbac Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta.v1 Require Export validation_init.
From New.proof.k8s_io.apimachinery.pkg Require Export runtime_init.
From New.proof.k8s_io.apimachinery.pkg.util.validation Require Export field_init.
From New.proof.k8s_io.apiserver.pkg.endpoints Require Export request_init.
From New.proof.k8s_io.apiserver.pkg.registry Require Export rest_init.
From New.proof.k8s_io.apiserver.pkg.storage Require Export names_init.
From New.proof.k8s_io.kubernetes.pkg.api Require Export legacyscheme_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export rbac_init.
From New.proof.k8s_io.kubernetes.pkg.apis.rbac Require Export v1_init validation_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.registry.rbac.clusterrole.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : clusterrole.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) clusterrole := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) clusterrole := build_get_is_pkg_init_wf.

End proof.
