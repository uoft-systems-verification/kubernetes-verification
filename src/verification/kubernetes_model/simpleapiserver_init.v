From New.proof Require Export context fmt.
From verification Require Export prelude.
From verification.k8s_io.api.core Require Export v1_init.
From verification.k8s_io.apimachinery.pkg.api Require Export errors_init.
From verification.k8s_io.apimachinery.pkg.api Require Export meta_init.
From verification.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From verification.k8s_io.apimachinery.pkg Require Export labels_init.
From verification.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From verification.k8s_io.apimachinery.pkg.types Require Export types_init.
From verification Require Export time_init.
From verification Require Export strconv_init.
From verification Require Export rand_init.
Require Export New.generatedproof.kubernetes_model.simpleapiserver.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.kubernetes_model.simpleapiserver.simpleapiserver := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.kubernetes_model.simpleapiserver.simpleapiserver := build_get_is_pkg_init_wf.

End proof.
