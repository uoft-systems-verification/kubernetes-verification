Require Export New.generatedproof.gopkg_in.evanphx.json_patch_v4.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : jsonpatch.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) jsonpatch := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) jsonpatch := build_get_is_pkg_init_wf.

End proof.
