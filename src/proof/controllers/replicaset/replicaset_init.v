From New.proof Require Export fmt.
From New.proof Require Export prelude.
From New.proof Require Export sort_init.
From New.proof Require Export wp_helpers.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers Require Export common.
From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From New.proof.k8s_io.apimachinery.pkg Require Export labels_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller_init.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof.controllers Require Export common_init.
Require Export New.generatedproof.controllers.replicaset.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : replicaset.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) replicaset := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) replicaset := build_get_is_pkg_init_wf.

End proof.
