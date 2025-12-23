From New.proof Require Export prelude.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
Require Export New.generatedproof.k8s_io.apimachinery.pkg.api.meta.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.apimachinery.pkg.api.meta.meta := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.apimachinery.pkg.api.meta.meta := build_get_is_pkg_init_wf.

End proof.
