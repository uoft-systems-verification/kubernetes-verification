From New.proof Require Export prelude.
From New.proof.k8s_io.apimachinery.pkg Require Export types_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From New.proof.k8s_io.utils Require Export ptr_init.
From New.proof Require Export time.
Require Export New.generatedproof.k8s_io.apimachinery.pkg.apis.meta.v1.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 := build_get_is_pkg_init_wf.

End proof.
