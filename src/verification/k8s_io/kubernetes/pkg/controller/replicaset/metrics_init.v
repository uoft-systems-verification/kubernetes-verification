From verification.k8s_io.component_base Require Export metrics_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.controller.replicaset.metrics.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.controller.replicaset.metrics.metrics := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.controller.replicaset.metrics.metrics := build_get_is_pkg_init_wf.

End proof.
