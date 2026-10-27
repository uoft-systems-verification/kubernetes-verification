Require Export New.generatedproof.bytes.
From New.proof Require Import proof_prelude.
Section init.
Context `{hG : heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : bytes.Assumptions}.
Collection W := sem + package_sem.
#[global] Instance : IsPkgInit (iProp Σ) bytes := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) bytes := build_get_is_pkg_init_wf.
End init.
