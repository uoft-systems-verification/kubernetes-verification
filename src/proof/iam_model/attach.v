From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export common.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Context `{!iamModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__AttachIdentityPolicy
    γ l identity policy_ids policy_id policy resource attachments q :
  {{{ "#Hiam" ∷ is_iam γ l ∗
      "Hidentity" ∷ own_iam_identity_frag γ identity 1 policy_ids ∗
      "Hpolicy" ∷ own_iam_policy_frag γ policy_id q policy ∗
      "Hattachments" ∷ own_iam_attachments_frag γ resource 1 attachments ∗
      "%Hresource_eq" ∷ ⌜ resource = policy.(iammodel.IdentityPolicy.Resource') ⌝
  }}}
    l @! (go.PointerType iammodel.State) @! "AttachIdentityPolicy" #identity #policy_id
  {{{ n, RET #interface.nil;
      "Hidentity" ∷ own_iam_identity_frag γ identity 1 (<[policy_id := tt]> policy_ids) ∗
      "Hpolicy" ∷ own_iam_policy_frag γ policy_id q policy ∗
      "Hattachments" ∷ own_iam_attachments_frag γ resource 1 (<[identity := n]> attachments) ∗
      "%Hn_positive" ∷ ⌜ (1 ≤ n)%nat ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hiam & Hidentity & Hpolicy & Hattachments & %Hresource_eq) HΦ".
  iDestruct "Hiam" as (mu_l) "[#Hmu #Hiam_inv]".
  wp_method_call. rewrite /iammodel.State__AttachIdentityPolicyⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock;
    [iFrame "#"; iEval (rewrite is_pkg_init_unfold /=);
     iSplit; [iModIntro; iEval (rewrite !is_pkg_init_unfold /=); done|done]|].
  iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  iDestruct (own_identities_auth_frag_lookup with
    "Hinv_Hown_identities_auth Hidentity") as %Hidentity_lookup.
  iDestruct (own_policies_auth_frag_lookup with
    "Hinv_Hown_policies_auth Hpolicy") as %Hpolicy_lookup.
  iDestruct (big_sepM2_dom with "Hinv_Hown_phys_identities_inner") as %Hidentity_maps_dom.
  assert (is_Some (phys_identities !! identity)) as [policy_ids_l Hphys_identity_lookup].
  { apply elem_of_dom. rewrite Hidentity_maps_dom.
    apply elem_of_dom. eexists. exact Hidentity_lookup. }
  rewrite exception_do_unseal /exception_do_def.
  wp_apply (wp_map_lookup2 iammodel.IdentityID
    (go.MapType iammodel.PolicyID (go.StructType [])) with
    "[$Hinv_Hown_phys_identities]") as "Hinv_Hown_phys_identities".
  rewrite Hphys_identity_lookup /=.
  wp_auto.
  wp_apply (wp_map_lookup2 iammodel.PolicyID iammodel.IdentityPolicy
    with "[$Hinv_Hown_phys_policies]") as "Hinv_Hown_phys_policies".
  rewrite Hpolicy_lookup /=. wp_auto.
  iDestruct (big_sepM2_delete _ phys_identities abs_identities
    identity policy_ids_l policy_ids Hphys_identity_lookup Hidentity_lookup
    with "Hinv_Hown_phys_identities_inner")
    as "[Hown_policy_ids Hinv_Hown_phys_identities_inner]".
  wp_apply (wp_map_lookup2 iammodel.PolicyID (go.StructType []) with
    "[$Hown_policy_ids]") as "Hown_policy_ids".
  destruct (policy_ids !! policy_id) as [[]|] eqn:Hattached.
  - wp_auto.
    assert (<[policy_id:=tt]> policy_ids = policy_ids) as Hpolicy_ids_same.
    { apply insert_id. done. }
    assert (<[identity:=<[policy_id:=tt]> policy_ids]> abs_identities =
      abs_identities) as Hidentities_same.
    { rewrite Hpolicy_ids_same. apply insert_id. done. }
    iApply fupd_wp.
    iMod (attach_identity_policy_vs
      (γ:=γ.(γ_resource_access))
      (identities:=abs_identities)
      (identities':=abs_identities)
      (policies:=phys_policies)
      (observed_resources:=observed_resources)
      (identity:=identity)
      (policy_ids:=policy_ids)
      (policy_id:=policy_id)
      (policy:=policy)
      (resource:=resource)
      (attachments:=attachments)
      with "Hinv_Hown_attachments_auth Hattachments")
      as (n) "(Hinv_Hown_attachments_auth & Hattachments & %Hn_positive)".
    { exact Hpolicy_lookup. }
    { symmetry. exact Hresource_eq. }
    { exact Hidentity_lookup. }
    { symmetry. exact Hidentities_same. }
    iModIntro.
    iAssert (([∗ map] policy_ids_l'; policy_ids' ∈
      phys_identities; abs_identities, policy_ids_l' ↦$ policy_ids')%I)
      with "[Hown_policy_ids Hinv_Hown_phys_identities_inner]"
      as "Hinv_Hown_phys_identities_inner".
    { rewrite (big_sepM2_delete _ phys_identities abs_identities
        identity policy_ids_l policy_ids Hphys_identity_lookup Hidentity_lookup).
      iFrame. }
    iCombineNamed "Hinv_*" as "H".
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (iam_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#%".
      iEval (rewrite is_pkg_init_unfold /=).
      iSplit; [iModIntro; iEval (rewrite !is_pkg_init_unfold /=); done|done]. }
    iApply ("HΦ" $! n). rewrite Hpolicy_ids_same. iFrame. done.
  - wp_auto.
    wp_apply (wp_map_insert iammodel.PolicyID with "[$Hown_policy_ids]").
    iIntros "Hown_policy_ids". wp_auto.
    iApply fupd_wp.
    iMod (own_identity_update_vs
      (γ:=γ.(γ_identities))
      (identities:=abs_identities)
      (identity:=identity)
      (policy_ids:=policy_ids)
      (policy_ids':=<[policy_id:=tt]> policy_ids)
      with "Hinv_Hown_identities_auth Hidentity")
      as "[Hinv_Hown_identities_auth Hidentity]".
    iMod (attach_identity_policy_vs
      (γ:=γ.(γ_resource_access))
      (identities:=abs_identities)
      (identities':=<[identity:=<[policy_id:=tt]> policy_ids]> abs_identities)
      (policies:=phys_policies)
      (observed_resources:=observed_resources)
      (identity:=identity)
      (policy_ids:=policy_ids)
      (policy_id:=policy_id)
      (policy:=policy)
      (resource:=resource)
      (attachments:=attachments)
      with "Hinv_Hown_attachments_auth Hattachments")
      as (n) "(Hinv_Hown_attachments_auth & Hattachments & %Hn_positive)".
    { exact Hpolicy_lookup. }
    { symmetry. exact Hresource_eq. }
    { exact Hidentity_lookup. }
    { done. }
    iModIntro.
    assert ((<[identity:=<[policy_id:=tt]> policy_ids]> abs_identities) !!
      identity = Some (<[policy_id:=tt]> policy_ids)) as Hidentity_lookup_update.
    { rewrite lookup_insert_eq. done. }
    iAssert (([∗ map] policy_ids_l'; policy_ids' ∈
      phys_identities; <[identity:=<[policy_id:=tt]> policy_ids]> abs_identities,
      policy_ids_l' ↦$ policy_ids')%I)
      with "[Hown_policy_ids Hinv_Hown_phys_identities_inner]"
      as "Hinv_Hown_phys_identities_inner".
    { rewrite (big_sepM2_delete _ phys_identities
        (<[identity:=<[policy_id:=tt]> policy_ids]> abs_identities)
        identity policy_ids_l (<[policy_id:=tt]> policy_ids)
        Hphys_identity_lookup Hidentity_lookup_update).
      rewrite delete_insert_eq. iFrame. }
    iCombineNamed "Hinv_*" as "H".
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (iam_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#".
      iSplit.
      - iEval (rewrite is_pkg_init_unfold /=).
        iSplit; [iModIntro; iEval (rewrite !is_pkg_init_unfold /=); done|done].
      - iNext. iSplit.
        + iPureIntro.
          intros identity' policy_ids' policy_id' Hidentity' Hattached'.
          destruct (decide (identity' = identity)) as [->|Hidentity_ne].
          * rewrite lookup_insert_eq in Hidentity'. inversion Hidentity'. subst policy_ids'.
            destruct (decide (policy_id' = policy_id)) as [->|Hpolicy_ne].
            -- exists policy. done.
            -- assert (policy_id ≠ policy_id') as Hpolicy_ne' by congruence.
               replace ((<[policy_id:=tt]> policy_ids) !! policy_id')
                 with (policy_ids !! policy_id') in Hattached'.
               2:{ symmetry. apply lookup_insert_ne. exact Hpolicy_ne'. }
               destruct (Hinv_Hattached_policy_exists
                 identity policy_ids policy_id' Hidentity_lookup Hattached')
                 as [policy' Hpolicy'].
               exists policy'. done.
          * assert (identity ≠ identity') as Hidentity_ne' by congruence.
            replace ((<[identity:=<[policy_id:=tt]> policy_ids]> abs_identities) !! identity')
              with (abs_identities !! identity') in Hidentity'.
            2:{ symmetry. apply lookup_insert_ne. exact Hidentity_ne'. }
            destruct (Hinv_Hattached_policy_exists
              identity' policy_ids' policy_id' Hidentity' Hattached')
              as [policy' Hpolicy'].
            exists policy'. done.
        + iPureIntro. exact Hinv_Hexisting_policy_used. }
    iApply ("HΦ" $! n). iFrame. done.
Unshelve.
  all: unfold iammodel.IdentityID.t, iammodel.PolicyID.t; apply _.
Qed.

End proof.
