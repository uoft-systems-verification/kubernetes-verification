Require Export New.generatedproof.reflect.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.reflect.reflect := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.reflect.reflect := build_get_is_pkg_init_wf.

End proof.
