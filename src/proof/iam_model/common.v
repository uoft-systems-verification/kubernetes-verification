From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance PolicyID_zero_val : ZeroVal iammodel.PolicyID.t := _.

#[global] Instance PolicyID_into_val_inj : go.IntoValInj iammodel.PolicyID.t := _.

#[global] Instance PolicyID_safe_map_key policy_id :
  SafeMapKey (K:=iammodel.PolicyID.t) iammodel.PolicyID policy_id.
Proof.
  constructor. iIntros (stk E Ψ) "HΨ". wp_auto. done.
Qed.

End proof.
