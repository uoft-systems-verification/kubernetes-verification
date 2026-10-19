From New.proof Require Export prelude.
Require Export New.generatedproof.k8s_io.apimachinery.pkg.util.sets.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : sets.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) sets := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) sets := build_get_is_pkg_init_wf.
End proof.
