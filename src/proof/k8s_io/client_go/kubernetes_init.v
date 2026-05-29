From New.proof.k8s_io.client_go.kubernetes.typed.core Require Export v1_init.
Require Export New.generatedproof.k8s_io.client_go.kubernetes.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : kubernetes.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) kubernetes := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) kubernetes := build_get_is_pkg_init_wf.

End proof.
