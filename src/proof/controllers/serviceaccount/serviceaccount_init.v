From New.proof Require Export prelude.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.kubernetes_model Require Export apimodel_init.
Require Export New.generatedproof.controllers.serviceaccount.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : serviceaccount.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) serviceaccount := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) serviceaccount := build_get_is_pkg_init_wf.

End proof.
