From New.proof.k8s_io.component_base Require Export featuregate_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.features.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.features.features := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.features.features := build_get_is_pkg_init_wf.

End proof.
