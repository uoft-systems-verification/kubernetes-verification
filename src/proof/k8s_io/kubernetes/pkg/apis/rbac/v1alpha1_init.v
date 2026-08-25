From New.proof Require Export fmt unsafe.
From New.proof.k8s_io.api.rbac Require Export v1alpha1_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg Require Export conversion_init runtime_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export rbac_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.apis.rbac.v1alpha1.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : v1alpha1.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) v1alpha1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) v1alpha1 := build_get_is_pkg_init_wf.

End proof.
