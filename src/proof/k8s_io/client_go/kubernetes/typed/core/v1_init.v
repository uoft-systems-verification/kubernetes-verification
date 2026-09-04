From New.proof Require Export context.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.types Require Export types_init.
From New.proof.k8s_io.apimachinery.pkg Require Export watch_init.
From New.proof.k8s_io.client_go Require Export gentype_init.
From New.proof.k8s_io.client_go.applyconfigurations.core Require Export v1_init.
From New.proof.k8s_io.client_go Require Export rest_init.
Require Export New.generatedproof.k8s_io.client_go.kubernetes.typed.core.v1.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : v1.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) v1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) v1 := build_get_is_pkg_init_wf.

End proof.
