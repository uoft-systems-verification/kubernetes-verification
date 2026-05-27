Require Export New.generatedproof.k8s_io.component_base.featuregate.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : featuregate.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) featuregate := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) featuregate := build_get_is_pkg_init_wf.

End proof.
