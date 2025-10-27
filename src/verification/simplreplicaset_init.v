Require Export New.generatedproof.k8s_io.kubernetes.pkg.controller.simplreplicaset.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit simplreplicaset := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf simplreplicaset := build_get_is_pkg_init_wf.

End proof.
