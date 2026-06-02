From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export iammodel_init.
From New.proof.iam_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance PolicyID_zero_val : ZeroVal iammodel.PolicyID.t := _.

#[global] Instance IdentityID_zero_val : ZeroVal iammodel.IdentityID.t := _.

#[global] Instance PolicyID_into_val_inj : go.IntoValInj iammodel.PolicyID.t := _.

#[global] Instance IdentityID_into_val_inj : go.IntoValInj iammodel.IdentityID.t := _.

#[global] Instance PolicyID_into_val_typed :
  IntoValTypedUnderlying iammodel.PolicyID.t iammodel.PolicyIDⁱᵐᵖˡ := _.

#[global] Instance IdentityID_into_val_typed :
  IntoValTypedUnderlying iammodel.IdentityID.t iammodel.IdentityIDⁱᵐᵖˡ := _.

#[global] Instance PolicyID_into_val_typed_named :
  IntoValTyped iammodel.PolicyID.t iammodel.PolicyID := _.

#[global] Instance IdentityID_into_val_typed_named :
  IntoValTyped iammodel.IdentityID.t iammodel.IdentityID := _.

#[global] Instance PolicyID_safe_map_key policy_id :
  SafeMapKey (K:=iammodel.PolicyID.t) iammodel.PolicyID policy_id.
Proof.
  constructor. iIntros (stk E Ψ) "HΨ". wp_auto. done.
Qed.

#[global] Instance IdentityID_safe_map_key identity :
  SafeMapKey (K:=iammodel.IdentityID.t) iammodel.IdentityID identity.
Proof.
  constructor. iIntros (stk E Ψ) "HΨ". wp_auto. done.
Qed.

Lemma wp_generatePolicyID :
  {{{ True }}}
    @! iammodel.generatePolicyID #()
  {{{ (policy_id : iammodel.PolicyID.t), RET #policy_id; True }}}.
Proof.
Admitted.

Lemma wp_State__generateNewPolicyIDAndUpdate
    l used_policy_ids_l (used_policy_ids : gmap iammodel.PolicyID.t unit) :
  {{{ l.[(iammodel.State.t), "usedPolicyIds"] ↦ used_policy_ids_l ∗
      used_policy_ids_l ↦$ used_policy_ids
  }}}
    l @! (go.PointerType iammodel.State) @! "generateNewPolicyIDAndUpdate" #()
  {{{ policy_id, RET #policy_id;
      ⌜ used_policy_ids !! policy_id = None ⌝ ∗
      l.[(iammodel.State.t), "usedPolicyIds"] ↦ used_policy_ids_l ∗
      used_policy_ids_l ↦$ <[policy_id := tt]> used_policy_ids
  }}}.
Proof.
  iIntros (Φ) "(Hused_policy_ids_addr & Hused_policy_ids) HΦ".
  wp_method_call.
  rewrite /iammodel.State__generateNewPolicyIDAndUpdateⁱᵐᵖˡ. wp_call.
  wp_auto.
  set I := (
    "Hused_policy_ids_addr" ∷ l.[(iammodel.State.t), "usedPolicyIds"] ↦ used_policy_ids_l ∗
    "Hused_policy_ids" ∷ used_policy_ids_l ↦$ used_policy_ids
  )%I.
  iAssert I with "[$Hused_policy_ids_addr $Hused_policy_ids]" as "Hloop".
  wp_for "Hloop".
  wp_apply (wp_generatePolicyID with "[//]").
  iIntros (policy_id) "_". wp_auto.
  wp_apply (wp_map_lookup2 iammodel.PolicyID (go.StructType []) with
    "[$Hused_policy_ids]").
  iIntros "Hused_policy_ids".
  destruct (used_policy_ids !! policy_id) as [[]|] eqn:Hlookup.
  - wp_auto.
    wp_for_post. iFrame.
  - wp_auto.
    wp_apply (wp_map_insert iammodel.PolicyID with "[$Hused_policy_ids]").
    iIntros "Hused_policy_ids". wp_auto.
    iApply wp_for_post_return.
    rewrite return_val_unseal /return_val_def.
    rewrite exception_do_unseal /exception_do_def. wp_auto.
    iApply "HΦ". iFrame. done.
Unshelve.
  all: unfold iammodel.PolicyID.t; apply _.
Qed.

End proof.
