From New.proof.k8s_io.apimachinery.pkg Require Export runtime_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.api.legacyscheme.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.api.legacyscheme.legacyscheme := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.api.legacyscheme.legacyscheme := build_get_is_pkg_init_wf.

End proof.
