Require Export New.generatedproof.k8s_io.apimachinery.pkg.util.validation.field.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : field.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) field := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) field := build_get_is_pkg_init_wf.

End proof.
