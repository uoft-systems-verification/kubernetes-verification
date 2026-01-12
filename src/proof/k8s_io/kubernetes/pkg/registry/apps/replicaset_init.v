From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.util Require Export runtime_init.
From New.proof.k8s_io.kubernetes.pkg.api Require Export legacyscheme_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export apps_init.
From New.proof.k8s_io.kubernetes.pkg.apis.apps Require Export validation_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.registry.apps.replicaset.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.registry.apps.replicaset.replicaset := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.registry.apps.replicaset.replicaset := build_get_is_pkg_init_wf.

End proof.
