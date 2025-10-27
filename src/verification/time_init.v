Require Export New.generatedproof.time.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.time.time := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.time.time := build_get_is_pkg_init_wf.

End proof.
