From New.proof Require Export prelude.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller_init.
From New.proof.kubernetes_model Require Export apimodel_init.
Require Export New.generatedproof.controllers.common.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.controllers.common.common := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.controllers.common.common := build_get_is_pkg_init_wf.

End proof.
