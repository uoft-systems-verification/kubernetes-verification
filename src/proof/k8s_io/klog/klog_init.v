Require Export New.generatedproof.k8s_io.klog.v2.
From proof.github_com.go_logr Require Export logr_init.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.klog.v2.klog := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.klog.v2.klog := build_get_is_pkg_init_wf.

End proof.
