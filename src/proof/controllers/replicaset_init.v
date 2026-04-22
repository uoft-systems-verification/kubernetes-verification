From New.proof Require Export fmt.
From New.proof Require Export prelude.
From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From New.proof.k8s_io.apimachinery.pkg Require Export labels_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller_init.
From New.proof.simple Require Export apimodel_init.
Require Export New.generatedproof.controllers.replicaset.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.controllers.replicaset.replicaset := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.controllers.replicaset.replicaset := build_get_is_pkg_init_wf.

End proof.
