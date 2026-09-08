From New.proof.k8s_io.apimachinery.pkg Require Export runtime_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From New.proof.k8s_io.client_go.tools Require Export cache_init.
Require Export New.generatedproof.k8s_io.client_go.listers.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : listers.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) listers := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) listers := build_get_is_pkg_init_wf.

End proof.
