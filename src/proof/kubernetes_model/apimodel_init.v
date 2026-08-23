From New.proof Require Export prelude.
From New.proof Require Export sync fmt time context.
From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.api.rbac Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg Require Export conversion_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export equality_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export meta_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export validation_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta.v1 Require Export validation_init.
From New.proof.k8s_io.apimachinery.pkg Require Export labels_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From New.proof.k8s_io.apimachinery.pkg.types Require Export types_init.
From New.proof.k8s_io.apimachinery.pkg.util Require Export uuid_init.
From New.proof.k8s_io.apimachinery.pkg.util.validation Require Export field_init.
From New.proof.k8s_io.apiserver.pkg.endpoints Require Export request_init.
From New.proof.k8s_io.apiserver.pkg.registry Require Export rest_init.
From New.proof.k8s_io.apiserver.pkg.registry.generic Require Export registry_init.
From New.proof.k8s_io.kubernetes.pkg.api Require Export legacyscheme_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export apps_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export core_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export rbac_init.
From New.proof.k8s_io.kubernetes.pkg.apis.apps Require Export install_init.
From New.proof.k8s_io.kubernetes.pkg.apis.apps Require Export v1_init.
From New.proof.k8s_io.kubernetes.pkg.apis.core Require Export v1_init.
From New.proof.k8s_io.kubernetes.pkg.apis.rbac Require Export install_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller_init.
From New.proof.k8s_io.kubernetes.pkg.registry.apps Require Export deployment_init.
From New.proof.k8s_io.kubernetes.pkg.registry.apps Require Export replicaset_init.
From New.proof.k8s_io.kubernetes.pkg.registry.apps Require Export statefulset_init.
From New.proof.k8s_io.kubernetes.pkg.registry.core Require Export pod_init.
From New.proof.k8s_io.kubernetes.pkg.registry.core Require Export persistentvolumeclaim_init.
From New.proof.k8s_io.kubernetes.pkg.registry.core Require Export serviceaccount_init.
From New.proof.k8s_io.kubernetes.pkg.registry.rbac Require Export clusterrole_init.
From New.proof Require Export strconv_init.
From New.proof Require Export rand_init.
From New.proof Require Export reflect_init.
Require Export New.generatedproof.kubernetes_model.apimodel.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) apimodel := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) apimodel := build_get_is_pkg_init_wf.

End proof.
