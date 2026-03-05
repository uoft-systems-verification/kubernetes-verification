From New.proof Require Export fmt.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg Require Export labels_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export meta_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg Require Export runtime_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.controller.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : controller.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) controller := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) controller := build_get_is_pkg_init_wf.

End proof.
