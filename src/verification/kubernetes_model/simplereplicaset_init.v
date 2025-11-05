From New.proof Require Export context fmt.
From verification Require Export prelude.
From verification.k8s_io.api.apps Require Export v1_init.
From verification.k8s_io.api.core Require Export v1_init.
From verification.k8s_io.apimachinery.pkg.api Require Export errors_init.
From verification.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From verification.k8s_io.apimachinery.pkg Require Export labels_init.
From verification.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From verification.k8s_io.apimachinery.pkg.types Require Export types_init.
From verification.k8s_io.apimachinery.pkg.util Require Export runtime_init.
From verification.k8s_io.client_go.listers.apps Require Export v1_init.
From verification.k8s_io.client_go.listers.core Require Export v1_init.
From verification.k8s_io.client_go.tools Require Export cache_init.
From verification.k8s_io.klog Require Export klog_init.
From verification.k8s_io.kubernetes.pkg Require Export controller_init.
From verification Require Export sort_init.
From verification.kubernetes_model Require Export simpleapiserver_init.
Require Export New.generatedproof.kubernetes_model.simplereplicaset.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.kubernetes_model.simplereplicaset.simplereplicaset := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.kubernetes_model.simplereplicaset.simplereplicaset := build_get_is_pkg_init_wf.

End proof.
