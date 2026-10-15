Require Export New.generatedproof.encoding.json.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : json.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) json := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) json := build_get_is_pkg_init_wf.

End proof.
