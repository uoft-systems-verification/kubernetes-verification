From verification Require Export prelude.
From New.proof Require Export std.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.controller.simplreplicaset.
From Perennial Require Import base.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit simplreplicaset := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf simplreplicaset := build_get_is_pkg_init_wf.

End proof.
