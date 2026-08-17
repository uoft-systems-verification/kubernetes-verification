From New.proof Require Export wp_helpers.
From New.proof.string Require Export prefix_suffix.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers Require Export common.
From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller_init.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof Require Export reflect_init strconv_init strings.
From New.proof.controllers Require Export common_init.
Require Export New.generatedproof.controllers.statefulset.
From New.proof Require Import proof_prelude.

Section init.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : statefulset.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) statefulset :=
  define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) statefulset :=
  build_get_is_pkg_init_wf.
End init.
