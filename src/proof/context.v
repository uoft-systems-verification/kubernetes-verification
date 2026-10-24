(* Initialization support for the context translation used by this project. *)
From New Require Export generatedproof.context.
From New.proof Require Import sync.atomic sync time errors.

Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : context.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) context := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) context := build_get_is_pkg_init_wf.

End init.
