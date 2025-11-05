Require Export New.generatedproof.strconv.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.strconv.strconv := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.strconv.strconv := build_get_is_pkg_init_wf.

End proof.
