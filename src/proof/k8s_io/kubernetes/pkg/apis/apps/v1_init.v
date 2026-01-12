From New.proof.k8s_io.kubernetes.pkg.apis Require Export apps_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.apis.apps.v1.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.apis.apps.v1.v1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.apis.apps.v1.v1 := build_get_is_pkg_init_wf.

End proof.
