Require Export New.generatedproof.k8s_io.api.apps.v1.
From New.proof.k8s_io.api.core Require Export v1_init.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.api.apps.v1.v1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.api.apps.v1.v1 := build_get_is_pkg_init_wf.

End proof.
