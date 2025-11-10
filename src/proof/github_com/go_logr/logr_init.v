Require Export New.generatedproof.github_com.go_logr.logr.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.github_com.go_logr.logr.logr := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.github_com.go_logr.logr.logr := build_get_is_pkg_init_wf.

End proof.
