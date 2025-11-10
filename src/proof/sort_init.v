Require Export New.generatedproof.sort.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.sort.sort := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.sort.sort := build_get_is_pkg_init_wf.

End proof.
