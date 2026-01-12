From New.proof.k8s_io.apimachinery.pkg.api Require Export validation_init.
From New.proof.k8s_io.apimachinery.pkg.util.validation Require Export field_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export core_init.
From New.proof.k8s_io.kubernetes.pkg.apis.core Require Export v1_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.apis.core.validation.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.apis.core.validation.validation := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.apis.core.validation.validation := build_get_is_pkg_init_wf.

End proof.
