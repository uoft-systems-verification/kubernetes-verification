From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export common.
From iris.algebra Require Import gmap gset.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Context `{!iamModelG Σ}.
Local Set Default Proof Using "All".

Lemma attachment_counts_dom_nonempty abs_identities policies resource :
  dom (attachment_counts abs_identities policies resource) =
  dom (filter (λ '(_, policy_ids),
    attached_policies_for_resource policies policy_ids resource ≠ ∅)
    abs_identities :
    gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit)).
Proof.
  apply set_eq. intros identity.
  rewrite !elem_of_dom. split.
  - intros [n Hcount].
    unfold attachment_counts, attachment_ref_counts,
      counted_reversed_reference.reverse_index, attachment_state in Hcount.
    rewrite !map_lookup_imap in Hcount.
    destruct (abs_identities !! identity) as [policy_ids|] eqn:Hidentity;
      simpl in Hcount; [|discriminate Hcount].
    unfold counted_reversed_reference.reference_count in Hcount.
    rewrite resource_count_refs_lookup in Hcount.
    rewrite resources_for_identity_counts_lookup_default in Hcount.
    destruct (decide
      (0 < size (attached_policies_for_resource policies policy_ids resource))%nat)
      as [Hpositive|Hnot_positive]; simpl in Hcount;
      [|discriminate Hcount].
    exists policy_ids. apply map_lookup_filter_Some. split; [done|].
    intros Hempty. rewrite Hempty size_empty in Hpositive. lia.
  - intros [policy_ids Hlookup].
    apply map_lookup_filter_Some in Hlookup as [Hidentity Hnonempty].
    exists (size (attached_policies_for_resource policies policy_ids resource)).
    unfold attachment_counts, attachment_ref_counts,
      counted_reversed_reference.reverse_index, attachment_state.
    rewrite !map_lookup_imap Hidentity /=.
    unfold counted_reversed_reference.reference_count.
    rewrite resource_count_refs_lookup.
    rewrite resources_for_identity_counts_lookup_default.
    destruct (decide
      (0 < size (attached_policies_for_resource policies policy_ids resource))%nat)
      as [Hpositive|Hnot_positive]; simpl; [done|].
    exfalso. apply Hnonempty.
    apply leibniz_equiv, size_empty_inv. lia.
Qed.

Lemma wp_State__Snapshot γ l resource dq attachments :
  {{{ "#Hiam" ∷ is_iam γ l ∗
      "Hattachments" ∷ own_iam_attachments_frag γ resource dq attachments
  }}}
    l @! (go.PointerType iammodel.State) @! "Snapshot" #()
  {{{ identities_l policies_l phys_identities abs_identities policies,
      RET (#identities_l, #policies_l);
      "Hattachments" ∷ own_iam_attachments_frag γ resource dq attachments ∗
      "Hidentities" ∷ identities_l ↦$ phys_identities ∗
      "Hidentities_inner" ∷ ([∗ map] policy_ids_l; policy_ids ∈
        phys_identities; abs_identities, policy_ids_l ↦$ policy_ids) ∗
      "Hpolicies" ∷ policies_l ↦$ policies ∗
      "%Hattachments_consistent" ∷ ⌜
        attachments = attachment_counts abs_identities policies resource ⌝ ∗
      "%Hidentities_with_access" ∷ ⌜
        dom attachments =
        dom (filter (λ '(_, policy_ids),
          attached_policies_for_resource policies policy_ids resource ≠ ∅)
          abs_identities) ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hiam & Hattachments) HΦ".
  iDestruct "Hiam" as (mu_l) "[#Hmu #Hiam_inv]".
  wp_method_call. rewrite /iammodel.State__Snapshotⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock;
    [iFrame "#"; iEval (rewrite is_pkg_init_unfold /=);
     iSplit; [iModIntro; iEval (rewrite !is_pkg_init_unfold /=); done|done]|].
  iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  iDestruct (own_attachments_frag_valid_pure with
    "Hinv_Hown_attachments_auth Hattachments") as
    %[Hattachments_consistent _].
  rewrite exception_do_unseal /exception_do_def.
  rewrite do_return_unseal.
  wp_pures.
  wp_apply (wp_copyIdentities with
    "[$Hinv_Hown_phys_identities $Hinv_Hown_phys_identities_inner]").
  iIntros (identities_l phys_identities_copy)
    "(Hinv_Hown_phys_identities &
      Hinv_Hown_phys_identities_inner & Hidentities & Hidentities_inner)".
  wp_auto.
  wp_apply (wp_copyPolicies with "[$Hinv_Hown_phys_policies]").
  iIntros (policies_l) "[Hinv_Hown_phys_policies Hpolicies]".
  iCombineNamed "Hinv_*" as "H".
  wp_auto.
  rewrite /exception.do_return_def.
  wp_auto.
  wp_apply (wp_Mutex__Unlock _ (iam_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#%".
    iEval (rewrite is_pkg_init_unfold /=).
    iSplit; [iModIntro; iEval (rewrite !is_pkg_init_unfold /=); done|done]. }
  iApply "HΦ". iFrame.
  iPureIntro. split.
  - done.
  - rewrite Hattachments_consistent.
    apply attachment_counts_dom_nonempty.
Qed.

End proof.
