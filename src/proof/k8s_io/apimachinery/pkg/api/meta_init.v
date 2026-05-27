From New.proof Require Export prelude.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
Require Export New.generatedproof.k8s_io.apimachinery.pkg.api.meta.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : meta.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) meta := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) meta := build_get_is_pkg_init_wf.

End proof.
