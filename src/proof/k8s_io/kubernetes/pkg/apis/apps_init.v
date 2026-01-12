From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export core_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.apis.apps.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.apis.apps.apps := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.apis.apps.apps := build_get_is_pkg_init_wf.

End proof.
