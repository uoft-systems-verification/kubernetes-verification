From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.util Require Export runtime_init.
From New.proof.k8s_io.kubernetes.pkg.api Require Export legacyscheme_init.
From New.proof.k8s_io.kubernetes.pkg.apis Require Export core_init.
From New.proof.k8s_io.kubernetes.pkg.apis.core Require Export validation_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.registry.core.pod.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : pod.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) pod := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) pod := build_get_is_pkg_init_wf.

End proof.
