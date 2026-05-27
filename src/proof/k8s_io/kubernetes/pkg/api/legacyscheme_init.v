From New.proof.k8s_io.apimachinery.pkg Require Export runtime_init.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.api.legacyscheme.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : legacyscheme.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) legacyscheme := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) legacyscheme := build_get_is_pkg_init_wf.

End proof.
