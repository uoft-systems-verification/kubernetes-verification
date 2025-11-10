Require Export New.generatedproof.k8s_io.kubernetes.pkg.api.v1.pod.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.api.v1.pod.pod := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.api.v1.pod.pod := build_get_is_pkg_init_wf.

End proof.
