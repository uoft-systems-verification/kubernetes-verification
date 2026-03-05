From New.proof Require Export context fmt time.
From New.proof Require Export prelude.
From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg Require Export labels_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From New.proof.k8s_io.apimachinery.pkg.types Require Export types_init.
From New.proof.k8s_io.apimachinery.pkg.util Require Export runtime_init.
From New.proof.k8s_io.apiserver.pkg.util Require Export feature_init.
From New.proof.k8s_io.client_go Require Export kubernetes_init.
From New.proof.k8s_io.client_go.kubernetes.typed.apps Require Export v1_init.
From New.proof.k8s_io.client_go.listers.apps Require Export v1_init.
From New.proof.k8s_io.client_go.listers.core Require Export v1_init.
From New.proof.k8s_io.client_go.tools Require Export cache_init.
From New.proof.k8s_io.client_go.util Require Export workqueue_init.
From New.proof.k8s_io.klog Require Export klog_init.
From New.proof.k8s_io.kubernetes.pkg.api.v1 Require Export pod_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller_init.
From New.proof.k8s_io.kubernetes.pkg.controller.replicaset Require Export metrics_init.
From New.proof.k8s_io.kubernetes.pkg Require Export features_init.
From New.proof.k8s_io.utils Require Export clock_init.
From New.proof.k8s_io.utils Require Export ptr_init.
From New.proof Require Export sort_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.controller.replicaset.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : replicaset.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) replicaset := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) replicaset := build_get_is_pkg_init_wf.

End proof.
