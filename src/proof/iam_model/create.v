From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export common.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Context `{!iamModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__CreatePolicy γ l resource :
  {{{ "#Hiam" ∷ is_iam γ l ∗
      "%Hresource_nonempty" ∷ ⌜ resource ≠ ""%go ⌝
  }}}
    l @! (go.PointerType iammodel.State) @! "CreatePolicy" #resource
  {{{ policy_id, RET (#policy_id, #interface.nil);
      "Hpolicy" ∷ own_iam_policy_frag γ policy_id 1
        (iammodel.IdentityPolicy.mk policy_id resource)
  }}}.
Proof.
  iIntros (Φ) "(#Hiam & %Hresource_nonempty) HΦ".
  iDestruct "Hiam" as (mu_l) "[#Hmu #Hiam_inv]".
  wp_method_call. rewrite /iammodel.State__CreatePolicyⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  replace (bool_decide (resource = ""%go)) with false by
    (symmetry; apply bool_decide_eq_false_2; done).
  wp_auto.
  wp_apply wp_Mutex__Lock;
    [iFrame "#"; iEval (rewrite is_pkg_init_unfold /=);
     iSplit; [iModIntro; iEval (rewrite !is_pkg_init_unfold /=); done|done]|].
  iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_State__generateNewPolicyIDAndUpdate with
    "[Hinv_Hstate_used_policy_ids_addr Hinv_Hown_phys_used_policy_ids]").
  { iFrame. }
  iIntros (policy_id)
    "(%Hpolicy_id_fresh & Hinv_Hstate_used_policy_ids_addr &
      Hinv_Hown_phys_used_policy_ids)".
  assert (phys_policies !! policy_id = None) as Hpolicy_fresh.
  { destruct (phys_policies !! policy_id) as [old_policy|] eqn:Hlookup; [|done].
    pose proof (Hinv_Hexisting_policy_used policy_id old_policy Hlookup) as Hused.
    rewrite Hpolicy_id_fresh in Hused. done. }
  assert (∀ identity policy_ids,
    abs_identities !! identity = Some policy_ids →
    policy_ids !! policy_id = None) as Hpolicy_unattached.
  { intros identity policy_ids Hidentity.
    destruct (policy_ids !! policy_id) as [[]|] eqn:Hattached; [|done].
    destruct (Hinv_Hattached_policy_exists
      identity policy_ids policy_id Hidentity Hattached) as [old_policy Hpolicy].
    rewrite Hpolicy_fresh in Hpolicy. done. }
  wp_auto.
  wp_apply (wp_map_insert iammodel.PolicyID with "[$Hinv_Hown_phys_policies]").
  iIntros "Hinv_Hown_phys_policies". wp_auto.
  iApply fupd_wp.
  iMod (own_policy_insert_vs
    (γ:=γ.(γ_policies)) (policies:=phys_policies)
    (policy_id:=policy_id)
    (policy:=iammodel.IdentityPolicy.mk policy_id resource)
    Hpolicy_fresh with "Hinv_Hown_policies_auth")
    as "[Hinv_Hown_policies_auth Hpolicy]".
  iMod (insert_unattached_policy_vs
    (γ:=γ.(γ_resource_access)) (identities:=abs_identities)
    (policies:=phys_policies) (observed_resources:=observed_resources)
    (policy_id:=policy_id)
    (policy:=iammodel.IdentityPolicy.mk policy_id resource)
    Hpolicy_unattached with "Hinv_Hown_attachments_auth")
    as "Hinv_Hown_attachments_auth".
  iModIntro.
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (iam_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#".
    iSplit.
    - iEval (rewrite is_pkg_init_unfold /=).
      iSplit; [iModIntro; iEval (rewrite !is_pkg_init_unfold /=); done|done].
    - iNext. iSplit.
      + iPureIntro.
      intros identity policy_ids policy_id' Hidentity Hattached.
      destruct (decide (policy_id' = policy_id)) as [->|Hne].
      * exists (iammodel.IdentityPolicy.mk policy_id resource).
        rewrite lookup_insert_eq. done.
      * destruct (Hinv_Hattached_policy_exists
          identity policy_ids policy_id' Hidentity Hattached)
          as [policy' Hpolicy'].
        exists policy'. rewrite lookup_insert_ne; done.
      + iPureIntro.
        intros policy_id' policy' Hlookup.
        destruct (decide (policy_id' = policy_id)) as [->|Hne].
        * rewrite lookup_insert_eq in Hlookup. inversion Hlookup. subst policy'.
          rewrite lookup_insert_eq. done.
        * assert (Hne' : policy_id ≠ policy_id') by congruence.
          rewrite lookup_insert_ne in Hlookup; [exact Hne'|].
          rewrite lookup_insert_ne; [exact Hne'|].
          exact (Hinv_Hexisting_policy_used policy_id' policy' Hlookup). }
  iApply "HΦ". iFrame.
Unshelve.
  all: unfold iammodel.PolicyID.t; apply _.
Qed.

End proof.
