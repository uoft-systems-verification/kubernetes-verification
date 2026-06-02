From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export common.
From iris.algebra Require Import gmap gset.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : iammodel.Assumptions}.
Context `{!iamModelG Σ}.
Local Set Default Proof Using "All".

Definition policy_map_resource_count
    (resource : iammodel.ResourceName.t)
    (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t) : nat :=
  size (dom (filter
    (λ '(_, policy), policy.(iammodel.IdentityPolicy.Resource') = resource)
    policies) : gset iammodel.PolicyID.t).

Lemma attachment_counts_lookup_attached_size
    identities policies identity policy_ids resource n :
  identities !! identity = Some policy_ids →
  attachment_counts identities policies resource !! identity = Some n →
  n = size (attached_policies_for_resource policies policy_ids resource).
Proof.
  intros Hidentity Hcount.
  unfold attachment_counts, attachment_ref_counts,
    counted_reversed_reference.reverse_index in Hcount.
  rewrite map_lookup_imap in Hcount.
  unfold attachment_state in Hcount.
  rewrite map_lookup_imap Hidentity /= in Hcount.
  unfold counted_reversed_reference.reference_count in Hcount.
  rewrite resource_count_refs_lookup in Hcount.
  rewrite resources_for_identity_counts_lookup_default in Hcount.
  destruct (decide (0 < size (attached_policies_for_resource policies policy_ids resource))%nat);
    simplify_eq; done.
Qed.

Lemma attached_policies_for_resource_fmap_count
    phys_policies policies resource :
  (∀ policy_id policy,
    policies !! policy_id = Some policy →
    phys_policies !! policy_id = Some policy) →
  size (attached_policies_for_resource phys_policies
    (fmap (λ _, tt) policies) resource) =
  policy_map_resource_count resource policies.
Proof.
  intros Hpolicies.
  unfold attached_policies_for_resource, policy_map_resource_count.
  apply f_equal, set_eq. intros policy_id.
  rewrite !elem_of_dom.
  split.
  - intros [[] Hlookup].
    apply map_lookup_filter_Some in Hlookup as [Hpolicy_id Hmatches].
    apply lookup_fmap_Some in Hpolicy_id as [policy [_ Hpolicy]].
    exists policy. apply map_lookup_filter_Some. split; [done|].
    unfold policy_matches_resource in Hmatches.
    rewrite (Hpolicies _ _ Hpolicy) in Hmatches.
    apply bool_decide_eq_true in Hmatches. done.
  - intros [policy Hlookup].
    apply map_lookup_filter_Some in Hlookup as [Hpolicy Hresource].
    exists tt. apply map_lookup_filter_Some. split.
    + rewrite lookup_fmap Hpolicy /=. done.
    + unfold policy_matches_resource.
      rewrite (Hpolicies _ _ Hpolicy) Hresource.
      apply bool_decide_eq_true_2. done.
Qed.

Lemma own_policy_map_lookup_pure γ phys_policies policies q :
  own_iam_policies_auth γ phys_policies -∗
  ([∗ map] policy_id ↦ policy ∈ policies,
    own_iam_policy_frag γ policy_id q policy) -∗
  ⌜ ∀ policy_id policy,
    policies !! policy_id = Some policy →
    phys_policies !! policy_id = Some policy ⌝.
Proof.
  iIntros "Hauth Hpolicies".
  iInduction policies as [|policy_id policy policies Hfresh] "IH" using map_ind.
  - iPureIntro. intros policy_id policy. rewrite lookup_empty. done.
  - iDestruct (big_sepM_insert with "Hpolicies") as "[Hpolicy Hpolicies]";
      first done.
    iDestruct (own_policies_auth_frag_lookup with "Hauth Hpolicy")
      as %Hpolicy_lookup.
    iPoseProof ("IH" with "Hauth Hpolicies") as "%IH".
    iPureIntro. intros policy_id' policy' Hlookup.
    destruct (decide (policy_id' = policy_id)) as [->|Hne].
    + rewrite lookup_insert_eq in Hlookup. simplify_eq. done.
    + apply lookup_insert_Some in Hlookup as [[Heq _]|[_ Hlookup]].
      * congruence.
      * apply IH; done.
Qed.

Lemma own_identity_policies_dom_subset γ abs_identities identity_policies q q_policy :
  own_iam_identities_auth γ abs_identities -∗
  ([∗ map] identity ↦ policies ∈ identity_policies,
    own_iam_identity_frag γ identity q (fmap (λ _, tt) policies) ∗
    [∗ map] policy_id ↦ policy ∈ policies,
      own_iam_policy_frag γ policy_id q_policy policy) -∗
  ⌜ dom identity_policies ⊆ dom abs_identities ⌝.
Proof.
  iIntros "Hauth Hidentity_policies".
  iInduction identity_policies as [|identity policies identity_policies Hfresh]
    "IH" using map_ind.
  - iPureIntro. rewrite dom_empty_L. Timeout 10 set_solver.
  - iDestruct (big_sepM_insert with "Hidentity_policies")
      as "[[Hidentity _] Hidentity_policies]"; first done.
    iDestruct (own_identities_auth_frag_lookup with "Hauth Hidentity")
      as %Hidentity_lookup.
    iPoseProof ("IH" with "Hauth Hidentity_policies") as "%IH".
    iPureIntro.
    apply elem_of_dom_2 in Hidentity_lookup.
    rewrite dom_insert_L. Timeout 10 set_solver.
Qed.

Lemma identity_policies_attachment_counts_pure
    γ abs_identities phys_policies observed_resources
    resource dq attachments identity_policies q q_policy :
  dom identity_policies ⊆ dom attachments →
  own_iam_attachments_auth γ abs_identities phys_policies observed_resources -∗
  own_iam_attachments_frag γ resource dq attachments -∗
  own_iam_identities_auth γ abs_identities -∗
  own_iam_policies_auth γ phys_policies -∗
  ([∗ map] identity ↦ policies ∈ identity_policies,
    own_iam_identity_frag γ identity q (fmap (λ _, tt) policies) ∗
    [∗ map] policy_id ↦ policy ∈ policies,
      own_iam_policy_frag γ policy_id q_policy policy) -∗
  ⌜ ∀ identity policies,
    identity_policies !! identity = Some policies →
    attachments !! identity =
      Some (policy_map_resource_count resource policies) ⌝.
Proof.
  iIntros (Hdom_subset)
    "Hattachments_auth Hattachments Hidentities_auth Hpolicies_auth Hidentity_policies".
  iPoseProof (own_attachments_frag_valid_pure with
    "Hattachments_auth Hattachments") as "%Hattachments_valid".
  destruct Hattachments_valid as [Hattachments_eq _].
  iInduction identity_policies as [|identity policies identity_policies Hfresh]
    "IH" using map_ind forall (Hdom_subset).
  - iPureIntro. intros identity policies. rewrite lookup_empty. done.
  - iDestruct (big_sepM_insert with "Hidentity_policies")
      as "[[Hidentity Hpolicies] Hidentity_policies]"; first done.
    iDestruct (own_identities_auth_frag_lookup with
      "Hidentities_auth Hidentity") as %Hidentity_abs.
    iPoseProof (own_policy_map_lookup_pure with
      "Hpolicies_auth Hpolicies") as "%Hpolicies_lookup".
    assert (Hcurrent : attachments !! identity =
      Some (policy_map_resource_count resource policies)).
    { assert (is_Some (attachments !! identity)) as [n Hattachment_lookup].
      { apply elem_of_dom.
        apply Hdom_subset.
        rewrite dom_insert_L. Timeout 10 set_solver. }
      rewrite Hattachment_lookup. f_equal.
      rewrite Hattachments_eq in Hattachment_lookup.
      pose proof (attachment_counts_lookup_attached_size
        abs_identities phys_policies identity (fmap (λ _, tt) policies)
        resource n Hidentity_abs Hattachment_lookup) as Hn.
      rewrite Hn.
      apply attached_policies_for_resource_fmap_count.
      exact Hpolicies_lookup. }
    assert (Hdom_subset' : dom identity_policies ⊆ dom attachments).
    { intros identity' Hin.
      apply Hdom_subset.
      rewrite dom_insert_L. Timeout 10 set_solver. }
    iPoseProof ("IH" $! Hdom_subset' with
      "Hattachments_auth Hattachments Hidentities_auth Hpolicies_auth Hidentity_policies")
      as "%IH".
    iPureIntro. intros identity' policies' Hlookup.
    destruct (decide (identity' = identity)) as [->|Hne].
    + rewrite lookup_insert_eq in Hlookup. simplify_eq. done.
    + apply lookup_insert_Some in Hlookup as [[Heq _]|[_ Hlookup]].
      * congruence.
      * apply IH; done.
Qed.

Definition for_map_postcondition_no_break P bv : iProp Σ :=
  (⌜ bv = continue_val ⌝ ∗ P) ∨
  (⌜ bv = execute_val ⌝ ∗ P).

Lemma wp_map_for_range_return
  `{!ZeroVal K} `{!EqDecision K} `{!Countable K} `{!ZeroVal V}
  `{!go.IntoValInj K} `{!TypedPointsto K} `{!IntoValTyped K key_type} :
  ∀ (P : list K → Z → iProp Σ) stk E (body : func.t) elem_type mref
    (m : gmap K V) dq,
  ∀ Φ,
  mref ↦${dq} m -∗
  (∀ keys,
     ⌜ list_to_set keys = dom m ∧ length keys = size m ∧ NoDup keys ⌝ -∗
     (P keys 0 ∗
      □ (∀ i key v, ⌜ keys !! (Z.to_nat i) = Some key ∧ m !! key = Some v ⌝ -∗
          P keys i -∗
          WP #body #key #v @ stk; E
            {{ bv, for_map_postcondition_no_break (P keys (i + 1)%Z) bv }}) ∗
      (mref ↦${dq} m -∗ P keys (Z.of_nat (size m)) -∗ Φ execute_val))
  ) -∗
  WP map.for_range key_type elem_type #mref #body @ stk; E {{ Φ }}.
Proof.
  iIntros (P stk E body elem_type mref m dq Φ) "Hm HΦ".
  wp_call.
  iDestruct (own_map_not_nil with "[$]") as %?.
  wp_if_destruct; first by exfalso.
  rewrite own_map_unseal. iNamed "Hm".
  wp_apply (_internal_wp_untyped_start_read with "Hown") as "Hown".
  wp_apply (wp_InternalMapForRange with "[//]"). iIntros "%ks %Hdom'".
  eapply go.is_map_domain_pure in Hdom'; last done.
  destruct Hdom' as [Hks_nodup Hks].
  assert (Forall (λ kv, ∃ (k : K), kv = #k) ks) as Heq.
  { rewrite Forall_forall. intros kv Hk.
    specialize (Hks kv). specialize (Hdom kv).
    rewrite -Hks in Hk. apply Hdom in Hk. done. }
  apply Forall_exists_Forall2_l in Heq as [keys Heq].
  apply Forall2_fmap_2 in Heq. rewrite -list_eq_Forall2 in Heq.
  rewrite list_fmap_id in Heq. subst ks.
  iAssert (⌜ _ ⌝)%I with "[]" as "%Hfacts".
  2: iDestruct ("HΦ" $! keys with "[]") as "(HP & #Hiter & HΦ)".
  2: iPureIntro; exact Hfacts.
  { iPureIntro. eassert _ as Hl.
    2:{ split; first eexact Hl.
        apply NoDup_fmap in Hks_nodup; last tc_solve.
        rewrite <- (size_list_to_set (C:=gset K)); last done.
        rewrite Hl. rewrite size_dom //. }
    rewrite sets.set_eq. intros k.
    rewrite elem_of_list_to_set.
    specialize (Hks #k). specialize (Hagree k).
    rewrite list_elem_of_fmap_inj in Hks.
    rewrite -Hks. rewrite Hagree. rewrite elem_of_dom.
    by destruct lookup. }
  pose (i := 0%Z : Z).
  change (P keys 0) with (P keys i).
  iFreeze "Hiter".
  replace (into_val <$> keys) with (into_val <$> (drop (Z.to_nat i) keys)).
  2:{ rewrite drop_0 //. }
  iThaw "Hiter".
  iAssert (⌜ (0 ≤ i ≤ Z.of_nat (length keys))%Z ⌝)%I as "-#Hi".
  { subst i. iPureIntro. split; [lia|apply Nat2Z.is_nonneg]. }
  generalize i. clear i. intros i.
  iLöb as "IH" forall (i). iDestruct "Hi" as %Hi_bounds.
  destruct Hi_bounds as [Hi_nonneg Hi_upper].
  destruct (decide (i < Z.of_nat (length keys))%Z).
  2:{
    assert (i = Z.of_nat (length keys)) by lia. subst.
    rewrite Nat2Z.id drop_all /=.
    wp_auto. wp_apply "Hown". iIntros "Hown".
    wp_auto.
    destruct Hfacts as (_ & Hkeys_len & _).
    rewrite Hkeys_len.
    iAssert (own_map_def mref dq m) with "[Hown]" as "Hm".
    { iExists mv, mp. iFrame "Hown". iFrame "%". }
    iApply ("HΦ" with "Hm HP").
  }
  list_elem keys i as key.
  destruct (m !! key) eqn:Hlookup.
  2:{
    exfalso. apply not_elem_of_dom_2 in Hlookup as Hkey_m.
    destruct Hfacts as [Hfact _]. rewrite <- Hfact in Hkey_m.
    rewrite elem_of_list_to_set in Hkey_m.
    rewrite list_elem_of_lookup in Hkey_m. Timeout 10 naive_solver.
  }
  iSpecialize ("Hiter" $! i key v with "[//] HP").
  erewrite drop_S; last done. rewrite fmap_cons foldr_cons.
  rewrite Hagree Hlookup /=. wp_apply (wp_wand with "Hiter").
  iIntros (execv) "Hpost".
  iDestruct "Hpost" as "[[-> H]|[-> H]]".
  - wp_auto. rewrite continue_val_unseal. wp_auto.
    replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
    iApply ("IH" with "[$Hown] H HΦ").
    iPureIntro. lia.
  - wp_auto. rewrite execute_val_unseal. wp_auto.
    replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
    iApply ("IH" with "[$Hown] H HΦ").
    iPureIntro. lia.
Qed.

Lemma wp_State__ListIdentities
    γ l resource dq attachments identity_policies q q_policy :
  {{{ "#Hiam" ∷ is_iam γ l ∗
      "Hattachments" ∷ own_iam_attachments_frag γ resource dq attachments ∗
      "Hidentity_policies" ∷ ([∗ map] identity ↦ policies ∈ identity_policies,
        own_iam_identity_frag γ identity q (fmap (λ _, tt) policies) ∗
        [∗ map] policy_id ↦ policy ∈ policies,
          own_iam_policy_frag γ policy_id q_policy policy) ∗
      "%Hattachments_dom" ∷ ⌜ dom attachments = dom identity_policies ⌝
  }}}
    l @! (go.PointerType iammodel.State) @! "ListIdentities" #()
  {{{ sl identity_list, RET #sl;
      "Hsl" ∷ sl ↦* identity_list ∗
      "Hattachments" ∷ own_iam_attachments_frag γ resource dq attachments ∗
      "Hidentity_policies" ∷ ([∗ map] identity ↦ policies ∈ identity_policies,
        own_iam_identity_frag γ identity q (fmap (λ _, tt) policies) ∗
        [∗ map] policy_id ↦ policy ∈ policies,
          own_iam_policy_frag γ policy_id q_policy policy) ∗
      "%Hidentity_list_nodup" ∷ ⌜ NoDup identity_list ⌝ ∗
      "%Hidentity_list_contains_attachments" ∷ ⌜
        dom attachments ⊆ list_to_set (C:=gset iammodel.IdentityID.t) identity_list ⌝ ∗
      "%Hattachment_counts" ∷ ⌜ ∀ identity policies,
        identity_policies !! identity = Some policies →
        attachments !! identity = Some (policy_map_resource_count resource policies) ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hiam & Hattachments & Hidentity_policies & %Hattachments_dom) HΦ".
  iDestruct "Hiam" as (mu_l) "[#Hmu #Hiam_inv]".
  wp_method_call. rewrite /iammodel.State__ListIdentitiesⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock;
    [iFrame "#"; iEval (rewrite is_pkg_init_unfold /=);
     iSplit; [iModIntro; iEval (rewrite !is_pkg_init_unfold /=); done|done]|].
  iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  rewrite exception_do_unseal /exception_do_def.
  wp_apply wp_slice_make2.
  { word. }
  iIntros (sl) "[Hsl Hcap]".
  wp_auto.
  pose (I := (λ (keys : list iammodel.IdentityID.t) (i : Z),
    (∃ (sl_current : slice.t) (identity_current : iammodel.IdentityID.t),
      "identities" ∷ identities_ptr ↦ sl_current ∗
      "Hsl" ∷ sl_current ↦* take (Z.to_nat i) keys ∗
      "Hcap" ∷ own_slice_cap iammodel.IdentityID.t sl_current (DfracOwn 1) ∗
      "identity" ∷ identity_ptr ↦ identity_current ∗
      "%Hi_nonneg" ∷ ⌜ (0 ≤ i)%Z ⌝)%I)).
  wp_apply (wp_map_for_range_return I with "[$Hinv_Hown_phys_identities]").
  iIntros (keys) "%Hkeys".
  destruct Hkeys as (Hkeys_dom & Hkeys_length & Hkeys_nodup).
  iSplitL "identities Hsl Hcap identity".
  { iExists sl, ""%go. iFrame. iPureIntro. word. }
  iSplit.
  - iModIntro.
    iIntros (i identity policy_ids_l) "%Hiter HI".
    destruct Hiter as [Hidentity_lookup Hphys_identity_lookup].
    iDestruct "HI" as (sl_current identity_current)
      "(identities & Hsl & Hcap & identity & %Hi_nonneg)".
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros (sl0) "[Hsl0 _]". wp_auto.
    wp_apply (wp_slice_append with "[$Hsl $Hcap $Hsl0]").
    iIntros (sl') "(Hsl & Hcap & Hsl0)".
    wp_auto.
    iRight. iSplit; first done.
    iExists sl', identity.
    assert (take (Z.to_nat (i + 1)) keys =
            take (Z.to_nat i) keys ++ [identity]) as Htake_succ.
    { assert (Z.to_nat (i + 1) = S (Z.to_nat i)) as -> by lia.
      apply take_S_r. done. }
    rewrite Htake_succ.
    iFrame.
    iPureIntro. lia.
  - iIntros "Hinv_Hown_phys_identities HI".
    iDestruct "HI" as (sl_current identity_current)
      "(identities & Hsl & Hcap & identity & %Hi_nonneg)".
    rewrite Nat2Z.id -Hkeys_length.
    replace (take (length keys) keys) with keys by
      (symmetry; apply take_ge; done).
    wp_auto.
    rewrite return_val_unseal /return_val_def. wp_auto.
    iDestruct (big_sepM2_dom with "Hinv_Hown_phys_identities_inner")
      as %Hidentity_maps_dom.
    iPoseProof (own_identity_policies_dom_subset with
      "Hinv_Hown_identities_auth Hidentity_policies")
      as "%Hidentity_policies_abs_dom".
    assert (Hidentity_list_contains_attachments :
      dom attachments ⊆ list_to_set keys).
    { rewrite Hattachments_dom.
      etrans; first exact Hidentity_policies_abs_dom.
      rewrite -Hidentity_maps_dom -Hkeys_dom. done. }
    assert (Hidentity_policies_attachments_dom :
      dom identity_policies ⊆ dom attachments).
    { rewrite Hattachments_dom. done. }
    iPoseProof (identity_policies_attachment_counts_pure
      γ abs_identities phys_policies observed_resources resource dq attachments
      identity_policies q q_policy Hidentity_policies_attachments_dom with
      "Hinv_Hown_attachments_auth Hattachments
       Hinv_Hown_identities_auth Hinv_Hown_policies_auth Hidentity_policies")
      as "%Hattachment_counts".
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (iam_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#%".
      iEval (rewrite is_pkg_init_unfold /=).
      iSplit.
      - iEval (rewrite !is_pkg_init_unfold /=). done.
      - done. }
    iApply "HΦ". iFrame.
    iSplit; first done.
    iSplit; done.
Unshelve.
all: try done.
Qed.

End proof.
