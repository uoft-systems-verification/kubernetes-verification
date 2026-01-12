From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.util Require Export runtime_init.
From New.proof.k8s_io.kubernetes.pkg.api Require Export legacyscheme_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export core_init.
From New.proof.k8s_io.kubernetes.pkg.apis.core Require Export validation_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.registry.core.pod.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.registry.core.pod.pod := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.registry.core.pod.pod := build_get_is_pkg_init_wf.

End proof.
