From New.proof Require Export prelude.
From New.proof Require Export sync fmt time context.
From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export meta_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export validation_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg Require Export labels_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From New.proof.k8s_io.apimachinery.pkg.types Require Export types_init.
From New.proof.k8s_io.apimachinery.pkg.util Require Export uuid_init.
From New.proof.k8s_io.apimachinery.pkg.util.validation Require Export field_init.
From New.proof.k8s_io.apiserver.pkg.registry Require Export rest_init.
From New.proof.k8s_io.kubernetes.pkg.api Require Export legacyscheme_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export apps_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export core_init.
From New.proof.k8s_io.kubernetes.pkg.apis.apps Require Export v1_init.
From New.proof.k8s_io.kubernetes.pkg.apis.core Require Export v1_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller_init.
From New.proof.k8s_io.kubernetes.pkg.registry.apps Require Export replicaset_init.
From New.proof.k8s_io.kubernetes.pkg.registry.core Require Export pod_init.
From New.proof Require Export strconv_init.
From New.proof Require Export rand_init.
Require Export New.generatedproof.kubernetes_model.apimodel.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.kubernetes_model.apimodel.apimodel := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.kubernetes_model.apimodel.apimodel := build_get_is_pkg_init_wf.

End proof.
