Require Export New.generatedproof.math.rand.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.math.rand.rand := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.math.rand.rand := build_get_is_pkg_init_wf.

End proof.
