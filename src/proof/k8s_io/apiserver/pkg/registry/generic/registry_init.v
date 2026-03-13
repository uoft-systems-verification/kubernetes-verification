Require Export New.generatedproof.k8s_io.apiserver.pkg.registry.generic.registry.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.apiserver.pkg.registry.generic.registry.registry := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.apiserver.pkg.registry.generic.registry.registry := build_get_is_pkg_init_wf.

End proof.
