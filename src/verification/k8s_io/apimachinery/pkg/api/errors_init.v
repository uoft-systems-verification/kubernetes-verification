Require Export New.generatedproof.k8s_io.apimachinery.pkg.api.errors.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.apimachinery.pkg.api.errors.errors := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.apimachinery.pkg.api.errors.errors := build_get_is_pkg_init_wf.

End proof.
