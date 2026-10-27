Require Export New.generatedproof.k8s_io.client_go.kubernetes.scheme.
From New.proof Require Import proof_prelude.
Section init.
Context `{hG : heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : scheme.Assumptions}.
Collection W := sem + package_sem.
#[global] Instance : IsPkgInit (iProp Σ) scheme := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) scheme := build_get_is_pkg_init_wf.
End init.
