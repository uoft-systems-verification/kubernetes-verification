Require Export New.generatedproof.k8s_io.klog.v2.
From New.proof Require Import proof_prelude.
From New.proof.github_com.go_logr Require Export logr_init.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : klog.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) klog := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) klog := build_get_is_pkg_init_wf.

End proof.
