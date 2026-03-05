From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.util Require Export runtime_init.
From New.proof.k8s_io.kubernetes.pkg.api Require Export legacyscheme_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export apps_init.
From New.proof.k8s_io.kubernetes.pkg.apis.apps Require Export validation_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.registry.apps.replicaset.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : replicaset.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) replicaset := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) replicaset := build_get_is_pkg_init_wf.

End proof.
