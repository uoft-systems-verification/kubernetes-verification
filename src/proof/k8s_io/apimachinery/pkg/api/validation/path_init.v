From New.proof Require Export fmt strings.
Require Export New.generatedproof.k8s_io.apimachinery.pkg.api.validation.path.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : path.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) path := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) path := build_get_is_pkg_init_wf.

End proof.
