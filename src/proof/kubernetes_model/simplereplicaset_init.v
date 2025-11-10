From New.proof Require Export fmt.
From proof Require Export prelude.
From proof.k8s_io.api.apps Require Export v1_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof.k8s_io.apimachinery.pkg.api Require Export errors_init.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From proof.k8s_io.apimachinery.pkg Require Export labels_init.
From proof.k8s_io.kubernetes.pkg Require Export controller_init.
From proof.kubernetes_model Require Export apimodel_init.
Require Export New.generatedproof.kubernetes_model.simplereplicaset.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.kubernetes_model.simplereplicaset.simplereplicaset := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.kubernetes_model.simplereplicaset.simplereplicaset := build_get_is_pkg_init_wf.

End proof.
