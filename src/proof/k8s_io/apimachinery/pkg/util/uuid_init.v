Require Export New.generatedproof.k8s_io.apimachinery.pkg.util.uuid.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : uuid.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) uuid := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) uuid := build_get_is_pkg_init_wf.

End proof.
