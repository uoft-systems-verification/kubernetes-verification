From New.proof Require Import prelude empty_ffi.
From New.proof.iam_model Require Export example_init.
From New.proof.iam_model Require Import snapshot create attach detach.
From New.proof.iam_model.example Require Import util.
From New.code.iam_model Require Export example.
From iris.algebra Require Import gmap gset.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : example.Assumptions}.
Context `{!iamModelG Σ}.
Local Set Default Proof Using "All".

Definition delete_policy_id_list
    (policy_ids : gmap iammodel.PolicyID.t unit)
    (policy_id_list : list iammodel.PolicyID.t) :
    gmap iammodel.PolicyID.t unit :=
  foldl (λ policy_ids policy_id, delete policy_id policy_ids)
    policy_ids policy_id_list.

Lemma processed_prefix_keep_identity
    (current : list iammodel.IdentityID.t) i identity
    (desired : gmap iammodel.IdentityID.t unit) :
  current !! i = Some identity →
  identity ∈ dom desired →
  list_to_set (C:=gset iammodel.IdentityID.t) (take (S i) current) ∖ dom desired =
  list_to_set (C:=gset iammodel.IdentityID.t) (take i current) ∖ dom desired.
Proof.
  intros Hlookup Hdesired.
  apply set_eq. intros identity'.
  rewrite !elem_of_difference !elem_of_list_to_set.
  rewrite (take_S_r _ _ _ Hlookup).
  rewrite elem_of_app. simpl.
  Timeout 10 set_solver.
Qed.

Lemma processed_prefix_remove_identity
    (current : list iammodel.IdentityID.t) i identity
    (desired : gmap iammodel.IdentityID.t unit)
    (all : gset iammodel.IdentityID.t) :
  current !! i = Some identity →
  identity ∉ dom desired →
  all ∖ (list_to_set (C:=gset iammodel.IdentityID.t)
    (take (S i) current) ∖ dom desired) =
  (all ∖ (list_to_set (C:=gset iammodel.IdentityID.t)
    (take i current) ∖ dom desired)) ∖ {[identity]}.
Proof.
  intros Hlookup Hdesired.
  apply set_eq. intros identity'.
  rewrite !elem_of_difference !elem_of_singleton.
  rewrite (take_S_r _ _ _ Hlookup).
  rewrite !elem_of_list_to_set elem_of_app. simpl.
  Timeout 10 set_solver.
Qed.

Lemma drop_succ_subset_current
    (current : list iammodel.IdentityID.t) i identity identity' :
  current !! i = Some identity →
  identity' ∈ list_to_set (C:=gset iammodel.IdentityID.t) (drop (S i) current) →
  identity' ∈ list_to_set (C:=gset iammodel.IdentityID.t) (drop i current).
Proof.
  intros Hlookup Hin.
  rewrite (drop_S current identity i Hlookup).
  rewrite elem_of_list_to_set elem_of_cons.
  right. rewrite elem_of_list_to_set in Hin. done.
Qed.

Lemma current_not_in_drop_succ
    (current : list iammodel.IdentityID.t) i identity :
  NoDup current →
  current !! i = Some identity →
  identity ∉ list_to_set (C:=gset iammodel.IdentityID.t) (drop (S i) current).
Proof.
  intros Hnodup Hlookup Hin.
  rewrite elem_of_list_to_set in Hin.
  apply list_elem_of_lookup_1 in Hin as [j Hdrop_lookup].
  rewrite lookup_drop in Hdrop_lookup.
  pose proof (NoDup_lookup _ _ _ _ Hnodup Hlookup Hdrop_lookup) as Heq.
  lia.
Qed.

Lemma delete_policy_id_list_lookup_notin
    policy_ids processed policy_id :
  policy_id ∉ list_to_set (C:=gset iammodel.PolicyID.t) processed →
  delete_policy_id_list policy_ids processed !! policy_id =
  policy_ids !! policy_id.
Proof.
  revert policy_ids.
  induction processed as [|processed_policy_id processed IH];
    intros policy_ids Hnotin; [done|].
  unfold delete_policy_id_list in *; simpl.
  assert (policy_id ∉ list_to_set (C:=gset iammodel.PolicyID.t) processed)
    as Hnotin_tail.
  { intros Hin. apply Hnotin.
    rewrite !elem_of_list_to_set in Hin |- *.
    right. done. }
  rewrite (IH (delete processed_policy_id policy_ids) Hnotin_tail).
  apply lookup_delete_ne; intros ->; exfalso; apply Hnotin;
    rewrite elem_of_list_to_set; left; done.
Qed.

Lemma delete_policy_id_list_lookup_remaining
    policy_ids policy_id_list i policy_id :
  NoDup policy_id_list →
  list_to_set (C:=gset iammodel.PolicyID.t) policy_id_list ⊆ dom policy_ids →
  policy_id_list !! i = Some policy_id →
  delete_policy_id_list policy_ids (take i policy_id_list) !! policy_id = Some tt.
Proof.
  intros Hnodup Hsubset Hlookup.
  assert (policy_id ∉ list_to_set (C:=gset iammodel.PolicyID.t)
    (take i policy_id_list)) as Hnotin_take.
  { intros Hin.
    rewrite elem_of_list_to_set in Hin.
    apply list_elem_of_lookup_1 in Hin as [j Htake_lookup].
    apply lookup_take_Some in Htake_lookup as [Hlookup_j Hj].
    pose proof (NoDup_lookup _ _ _ _ Hnodup Hlookup_j Hlookup) as ->.
    lia. }
  pose proof (delete_policy_id_list_lookup_notin
    policy_ids (take i policy_id_list) policy_id Hnotin_take) as Hlookup_after.
  rewrite Hlookup_after.
  assert (policy_id ∈ dom policy_ids) as Hpolicy_id_dom.
  { apply Hsubset.
    rewrite elem_of_list_to_set.
    eapply list_elem_of_lookup_2. exact Hlookup. }
  apply elem_of_dom in Hpolicy_id_dom as [[] Hpolicy_id_lookup].
  exact Hpolicy_id_lookup.
Qed.

Lemma delete_policy_id_list_snoc policy_ids processed policy_id :
  delete_policy_id_list policy_ids (processed ++ [policy_id]) =
  delete policy_id (delete_policy_id_list policy_ids processed).
Proof.
  unfold delete_policy_id_list.
  rewrite foldl_app /=. done.
Qed.

Lemma dom_lookup_removed `{Countable K} (m m' : gmap K nat) k :
  k ∈ dom m →
  m' !! k = None →
  (∀ k', k' ≠ k → m' !! k' = m !! k') →
  dom m' = dom m ∖ {[k]}.
Proof.
  intros Hk Hnone Hother.
  apply set_eq. intros k'.
  rewrite elem_of_difference elem_of_singleton !elem_of_dom.
  split.
  - intros [n Hlookup].
    split.
    + destruct (decide (k' = k)) as [->|Hne].
      * rewrite Hnone in Hlookup. done.
      * exists n. rewrite -Hlookup. symmetry. apply Hother. done.
    + intros ->. rewrite Hnone in Hlookup. done.
  - intros [[n Hlookup] Hne].
    exists n. rewrite Hother; done.
Qed.

Lemma attachment_counts_lookup_nonempty
    identities policies identity policy_ids resource :
  identities !! identity = Some policy_ids →
  attached_policies_for_resource policies policy_ids resource ≠ ∅ →
  attachment_counts identities policies resource !! identity =
    Some (size (attached_policies_for_resource policies policy_ids resource)).
Proof.
  intros Hidentity Hnonempty.
  unfold attachment_counts, attachment_ref_counts,
    counted_reversed_reference.reverse_index, attachment_state.
  rewrite !map_lookup_imap Hidentity /=.
  unfold counted_reversed_reference.reference_count.
  rewrite resource_count_refs_lookup.
  pose proof (resources_for_identity_counts_lookup_default
    policies policy_ids resource) as Hdefault.
  destruct (resources_for_identity_counts policies policy_ids !! resource)
    as [n|] eqn:Hlookup; simpl in Hdefault.
  - assert (0 < n)%nat as Hpositive.
    { rewrite Hdefault.
      destruct (decide
        (size (attached_policies_for_resource policies policy_ids resource) = 0)%nat)
        as [Hsize_zero|Hsize_nonzero]; [|lia].
      exfalso. apply Hnonempty.
      apply leibniz_equiv, size_empty_inv. done. }
    change (default 0%nat (Some n)) with n.
    destruct (decide (0 < n)%nat) as [_|Hnot_positive]; [|lia].
    f_equal. exact Hdefault.
  - symmetry in Hdefault.
    apply size_empty_inv in Hdefault.
    exfalso. apply Hnonempty. apply leibniz_equiv. exact Hdefault.
Qed.

Lemma wp_ReconcileIdentityAccess
    γ l desired_l
    (desired : gmap iammodel.IdentityID.t unit)
    resource attachments abs_identities policies q_policy :
  {{{ "#Hpkg" ∷ is_pkg_init example ∗
      "#Hglobal_l" ∷ (global_addr iammodel.ModelState) ↦□ l ∗
      "#Hiam" ∷ is_iam γ l ∗
      "Hdesired" ∷ desired_l ↦$ desired ∗
      "Hattachments" ∷ own_iam_attachments_frag γ resource 1 attachments ∗
      "Hidentities" ∷ ([∗ map] identity ↦ policy_ids ∈ abs_identities,
        own_iam_identity_frag γ identity 1 policy_ids) ∗
      "Hpolicies" ∷ ([∗ map] policy_id ↦ policy ∈ policies,
        own_iam_policy_frag γ policy_id q_policy policy) ∗
      "%Hattachments_identities" ∷ ⌜ dom attachments ⊆ dom abs_identities ⌝ ∗
      "%Hdesired_identities" ∷ ⌜ dom desired ⊆ dom abs_identities ⌝ ∗
      "%Habs_identities_policies" ∷ ⌜ ∀ identity policy_ids,
        abs_identities !! identity = Some policy_ids →
        dom policy_ids ⊆ dom policies ⌝ ∗
      "%Hresource_nonempty" ∷ ⌜ resource ≠ ""%go ⌝
  }}}
    @! example.ReconcileIdentityAccess #desired_l #resource
  {{{ attachments' abs_identities', RET #interface.nil;
      desired_l ↦$ desired ∗
      own_iam_attachments_frag γ resource 1 attachments' ∗
      ([∗ map] identity ↦ policy_ids ∈ abs_identities',
        own_iam_identity_frag γ identity 1 policy_ids) ∗
      ([∗ map] policy_id ↦ policy ∈ policies,
        own_iam_policy_frag γ policy_id q_policy policy) ∗
      ⌜ dom attachments' = dom desired ⌝ ∗
      ⌜ dom abs_identities' = dom abs_identities ⌝ ∗
      (if decide (dom desired ⊆ dom attachments) then True else
       ∃ policy_id,
         own_iam_policy_frag γ policy_id 1
           (iammodel.IdentityPolicy.mk policy_id resource))
  }}}.
Proof.
  wp_start as "H".
  iNamed "H".
  wp_auto.
  wp_apply (wp_State__Snapshot with
    "[$Hiam $Hattachments $Hidentities $Hpolicies]").
  iIntros (identities_l policies_l phys_identities snap_abs_identities snap_policies)
    "(Hattachments & Hidentities & Hpolicies & Hsnapshot_identities &
      Hsnapshot_identities_inner & Hsnapshot_policies &
      %Hidentity_frags_consistent & %Hpolicy_frags_consistent &
      %Hattachments_consistent & %Hsnapshot_access)".
  wp_auto.
  wp_apply (wp_identitiesWithPolicyForResource with
    "[$Hpkg $Hsnapshot_identities $Hsnapshot_identities_inner $Hsnapshot_policies]").
  iIntros (current_sl current)
    "(Hsnapshot_identities & Hsnapshot_identities_inner & Hsnapshot_policies &
      Hcurrent & %Hcurrent_nodup & %Hcurrent_dom)".
  wp_auto.
  iDestruct (own_slice_len with "Hcurrent") as
    %[Hcurrent_len Hcurrent_len_nonneg].
  iAssert (
    ∃ (i : w64)
      (attachments_i : gmap iammodel.IdentityID.t nat)
      (abs_identities_i :
        gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
      (last_identity : iammodel.IdentityID.t),
      "Hattachments" ∷ own_iam_attachments_frag γ resource 1 attachments_i ∗
      "Hidentities" ∷ ([∗ map] identity ↦ policy_ids ∈ abs_identities_i,
        own_iam_identity_frag γ identity 1 policy_ids) ∗
      "identity" ∷ identity_ptr ↦ last_identity ∗
      "i" ∷ i_ptr ↦ i ∗
      "%Hi_bounds" ∷ ⌜
        (0 ≤ sint.Z i ≤ Z.of_nat (length current))%Z ⌝ ∗
      "%Hattachments_dom_i" ∷ ⌜
        dom attachments_i =
        dom attachments ∖
          (list_to_set (C:=gset iammodel.IdentityID.t)
            (take (Z.to_nat (sint.Z i)) current) ∖ dom desired) ⌝ ∗
      "%Habs_identities_dom_i" ∷ ⌜
        dom abs_identities_i = dom abs_identities ⌝ ∗
      "%Hunprocessed_identities" ∷ ⌜ ∀ identity policy_ids,
        identity ∈ list_to_set (C:=gset iammodel.IdentityID.t)
          (drop (Z.to_nat (sint.Z i)) current) →
        abs_identities !! identity = Some policy_ids →
        abs_identities_i !! identity = Some policy_ids ⌝ ∗
      "%Hunprocessed_attachments" ∷ ⌜ ∀ identity,
        identity ∈ list_to_set (C:=gset iammodel.IdentityID.t)
          (drop (Z.to_nat (sint.Z i)) current) →
        attachments_i !! identity = attachments !! identity ⌝
  )%I with
    "[Hattachments Hidentities identity i]"
    as "HI".
  { iExists (W64 0), attachments, abs_identities, ""%go.
    iFrame.
    iPureIntro. split_and!.
    - word.
    - apply Nat2Z.is_nonneg.
    - rewrite take_0 list_to_set_nil. Timeout 10 set_solver.
    - done.
    - intros identity policy_ids _ Hlookup. done.
    - intros identity _. done.
  }
  wp_for "HI".
  wp_if_destruct.
  - destruct Hi_bounds as [Hi_nonneg Hi_upper].
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len current_sl))%Z)
      as [_|Hidx_bad]; last first.
    { exfalso. apply Hidx_bad. split; done. }
    assert (0 ≤ sint.Z i < Z.of_nat (length current))%Z as Hi_current.
    { split; [done|].
      rewrite Hcurrent_len.
      word. }
    list_elem current (sint.Z i) as current_identity.
    wp_apply (wp_load_slice_index
      (V:=iammodel.IdentityID.t) (t:=iammodel.IdentityID)
      current_sl (sint.Z i) current (DfracOwn 1) current_identity
      with "[$Hcurrent]").
    { done. }
    { done. }
    iIntros "Hcurrent".
    wp_auto.
    wp_apply (wp_map_lookup2 iammodel.IdentityID (go.StructType [])
      with "[$Hdesired]").
    iIntros "Hdesired".
    destruct (desired !! current_identity) as [[]|] eqn:Hkeep.
    + wp_auto.
      wp_for_post.
      iFrame "HΦ".
      iFrame "Hdesired resource desired policies identities Hpolicies current
        Hsnapshot_identities Hsnapshot_identities_inner Hsnapshot_policies Hcurrent".
      iExists (word.add i (W64 1)), attachments_i, abs_identities_i,
        current_identity.
      iFrame.
      iPureIntro. split_and!.
      * word.
      * destruct Hi_current as [_ Hi_lt_current].
        replace (sint.Z (word.add i (W64 1))) with
          (sint.Z i + 1)%Z by word.
        lia.
      * rewrite Hattachments_dom_i.
        replace (Z.to_nat (sint.Z (word.add i (W64 1)))) with
          (S (sint.nat i)) by word.
        assert (list_to_set (C:=gset iammodel.IdentityID.t)
            (take (S (sint.nat i)) current) ∖ dom desired =
          list_to_set (C:=gset iammodel.IdentityID.t)
            (take (sint.nat i) current) ∖ dom desired) as Hprocessed_keep.
        { apply (processed_prefix_keep_identity current (sint.nat i)
            current_identity desired); [exact Hcurrent_identity_lookup|].
          apply elem_of_dom. eexists. exact Hkeep. }
        rewrite Hprocessed_keep. done.
      * done.
      * intros identity policy_ids Hin Hlookup.
        apply Hunprocessed_identities; [|done].
        apply (drop_succ_subset_current current (sint.nat i) current_identity).
        -- exact Hcurrent_identity_lookup.
        -- replace (Z.to_nat (sint.Z (word.add i (W64 1)))) with
            (S (sint.nat i)) in Hin by word.
           done.
      * intros identity Hin.
        apply Hunprocessed_attachments.
        apply (drop_succ_subset_current current (sint.nat i) current_identity).
        -- exact Hcurrent_identity_lookup.
        -- replace (Z.to_nat (sint.Z (word.add i (W64 1)))) with
            (S (sint.nat i)) in Hin by word.
           done.
    + wp_auto.
      assert (current_identity ∈ list_to_set
        (C:=gset iammodel.IdentityID.t) current) as Hcurrent_identity_in_current.
      { apply elem_of_list_to_set. eapply list_elem_of_lookup_2.
        exact Hcurrent_identity_lookup. }
      assert (current_identity ∈ dom
        (attachment_counts snap_abs_identities snap_policies resource))
        as Hcurrent_identity_in_attachments.
      { rewrite Hsnapshot_access -Hcurrent_dom.
        exact Hcurrent_identity_in_current. }
      assert (current_identity ∈ dom abs_identities) as Hcurrent_identity_in_abs.
      { apply Hattachments_identities. exact Hcurrent_identity_in_attachments. }
      apply elem_of_dom in Hcurrent_identity_in_abs as
        [current_policy_ids Hcurrent_policy_ids_lookup].
      assert (current_identity ∈ list_to_set
        (C:=gset iammodel.IdentityID.t) (drop (sint.nat i) current))
        as Hcurrent_identity_unprocessed.
      { rewrite (drop_S current current_identity (sint.nat i)
          Hcurrent_identity_lookup).
        rewrite elem_of_list_to_set elem_of_cons. left. done. }
      pose proof (Hunprocessed_identities current_identity current_policy_ids
        Hcurrent_identity_unprocessed Hcurrent_policy_ids_lookup)
        as Hcurrent_policy_ids_i_lookup.
      pose proof (Hunprocessed_attachments current_identity
        Hcurrent_identity_unprocessed) as Hcurrent_attachment_i_lookup.
      wp_apply (wp_policiesForResource with
        "[$Hpkg $Hsnapshot_identities $Hsnapshot_identities_inner
          $Hsnapshot_policies]").
      iIntros (policy_ids_sl policy_id_list)
        "(Hsnapshot_identities & Hsnapshot_identities_inner &
          Hsnapshot_policies & Hpolicy_ids_sl &
          %Hpolicy_id_list_nodup & %Hpolicy_id_list_dom)".
      wp_auto.
      pose proof (Hidentity_frags_consistent current_identity current_policy_ids
        Hcurrent_policy_ids_lookup) as Hsnap_current_policy_ids_lookup.
      assert (policy_ids_for_identity snap_abs_identities current_identity =
        current_policy_ids) as Hpolicy_ids_for_identity_current.
      { unfold policy_ids_for_identity.
        rewrite Hsnap_current_policy_ids_lookup. done. }
      rewrite Hpolicy_ids_for_identity_current in Hpolicy_id_list_dom.
      assert (attached_policies_for_resource snap_policies
        current_policy_ids resource ≠ ∅) as Hcurrent_attached_nonempty.
      { assert (current_identity ∈ dom (filter (λ '(_, policy_ids),
            attached_policies_for_resource snap_policies policy_ids resource ≠ ∅)
            snap_abs_identities)) as Hcurrent_in_filter.
        { rewrite -Hcurrent_dom. exact Hcurrent_identity_in_current. }
        apply elem_of_dom in Hcurrent_in_filter as
          [snap_policy_ids Hsnap_policy_ids_filter].
        apply map_lookup_filter_Some in Hsnap_policy_ids_filter as
          [Hsnap_policy_ids_lookup Hsnap_policy_ids_nonempty].
        rewrite Hsnap_current_policy_ids_lookup in Hsnap_policy_ids_lookup.
        inversion Hsnap_policy_ids_lookup. subst. done. }
      assert (length policy_id_list =
        size (attached_policies_for_resource snap_policies
          current_policy_ids resource)) as Hpolicy_id_list_len.
      { rewrite -Hpolicy_id_list_dom.
        symmetry. apply size_list_to_set. done. }
      assert (attachments_i !! current_identity =
        Some (length policy_id_list)) as Hattachments_i_current_count.
      { rewrite Hcurrent_attachment_i_lookup.
        rewrite (attachment_counts_lookup_nonempty
          snap_abs_identities snap_policies current_identity current_policy_ids
          resource Hsnap_current_policy_ids_lookup Hcurrent_attached_nonempty).
        f_equal. symmetry. exact Hpolicy_id_list_len. }
      assert (list_to_set (C:=gset iammodel.PolicyID.t) policy_id_list
        ⊆ dom current_policy_ids) as Hpolicy_id_list_subset_current.
      { rewrite Hpolicy_id_list_dom.
        intros policy_id Hin.
        unfold attached_policies_for_resource in Hin.
        apply elem_of_dom in Hin as [[] Hlookup].
        apply map_lookup_filter_Some in Hlookup as [Hlookup _].
        apply elem_of_dom. eexists. exact Hlookup. }
      iDestruct (own_slice_len with "Hpolicy_ids_sl") as
        %[Hpolicy_ids_len Hpolicy_ids_len_nonneg].
      iDestruct (big_sepM_delete _ abs_identities_i current_identity
        current_policy_ids with "Hidentities")
        as "[Hidentity Hidentities_rest]".
      { exact Hcurrent_policy_ids_i_lookup. }
      wp_alloc inner_i_ptr as "inner_i".
      iAssert (∃ (j : w64)
          (attachments_j : gmap iammodel.IdentityID.t nat)
          (policy_ids_j : gmap iammodel.PolicyID.t unit)
          (last_policy_id : iammodel.PolicyID.t),
        "inner_i" ∷ inner_i_ptr ↦ j ∗
        "policyID" ∷ policyID_ptr ↦ last_policy_id ∗
        "Hattachments" ∷ own_iam_attachments_frag γ resource 1 attachments_j ∗
        "Hidentity" ∷ own_iam_identity_frag γ current_identity 1 policy_ids_j ∗
        "%Hinner_bounds" ∷ ⌜
          (0 ≤ sint.Z j ≤ Z.of_nat (length policy_id_list))%Z ⌝ ∗
        "%Hpolicy_ids_j" ∷ ⌜ policy_ids_j =
          delete_policy_id_list current_policy_ids
            (take (Z.to_nat (sint.Z j)) policy_id_list) ⌝ ∗
        "%Hattachments_j_current" ∷ ⌜
          if decide (Z.to_nat (sint.Z j) < length policy_id_list)%nat then
            attachments_j !! current_identity =
              Some (length policy_id_list - Z.to_nat (sint.Z j))%nat
          else
            attachments_j !! current_identity = None ⌝ ∗
        "%Hattachments_j_other" ∷ ⌜ ∀ identity,
          identity ≠ current_identity →
          attachments_j !! identity = attachments_i !! identity ⌝
      )%I with
        "[inner_i policyID Hattachments Hidentity]" as "Hinner".
      { iExists (W64 0), attachments_i, current_policy_ids, ""%go.
        iFrame.
        iPureIntro. split_and!.
        - word.
        - apply Nat2Z.is_nonneg.
        - rewrite take_0. done.
        - rewrite Z2Nat.inj_0 /=.
          destruct (decide (0 < length policy_id_list)%nat)
            as [_|Hnot_positive].
          + rewrite Nat.sub_0_r. exact Hattachments_i_current_count.
          + exfalso. apply Hcurrent_attached_nonempty.
            apply leibniz_equiv, size_empty_inv.
            rewrite -Hpolicy_id_list_len. lia.
        - intros identity Hne. done. }
      wp_pures.
      wp_for "Hinner".
      wp_if_destruct.
      * assert (0 ≤ sint.Z j < Z.of_nat (length policy_id_list))%Z
          as Hj_current.
        { destruct Hinner_bounds as [Hj_nonneg Hj_upper].
          split; [done|].
          rewrite Hpolicy_ids_len. word. }
        list_elem policy_id_list (sint.Z j) as current_policy_id.
        wp_bind (GoLoad iammodel.PolicyID _)%E.
        destruct (decide
          (0 ≤ sint.Z j < sint.Z (slice.len policy_ids_sl))%Z)
          as [_|Hbounds_bad]; last word.
        wp_apply (wp_load_slice_index
          (V:=go_string) (t:=iammodel.PolicyID)
          policy_ids_sl (sint.Z j) policy_id_list (DfracOwn 1)
          current_policy_id with "[$Hpolicy_ids_sl]").
        { word. }
        { iPureIntro. exact Hcurrent_policy_id_lookup. }
        iIntros "Hpolicy_ids_sl".
        wp_auto.
        assert (delete_policy_id_list
          (policy_ids_for_identity snap_abs_identities current_identity)
          (take (sint.nat j) policy_id_list) !! current_policy_id = Some tt)
          as Hattached.
        { apply delete_policy_id_list_lookup_remaining; [done|done|].
          exact Hcurrent_policy_id_lookup. }
        assert (current_policy_id ∈
          attached_policies_for_resource snap_policies
            (policy_ids_for_identity snap_abs_identities current_identity)
            resource) as Hcurrent_policy_id_attached.
        { rewrite -Hpolicy_id_list_dom.
          rewrite elem_of_list_to_set.
          eapply list_elem_of_lookup_2. exact Hcurrent_policy_id_lookup. }
        unfold attached_policies_for_resource in Hcurrent_policy_id_attached.
        apply elem_of_dom in Hcurrent_policy_id_attached as
          [[] Hcurrent_policy_id_filter].
        apply map_lookup_filter_Some in Hcurrent_policy_id_filter as
          [Hcurrent_policy_id_in_identity Hcurrent_policy_id_matches].
        unfold policy_matches_resource in Hcurrent_policy_id_matches.
        destruct (snap_policies !! current_policy_id) as [snap_policy|]
          eqn:Hsnap_policy_lookup; [|done].
        apply bool_decide_eq_true in Hcurrent_policy_id_matches.
        assert (current_policy_id ∈ dom
          (policy_ids_for_identity snap_abs_identities current_identity))
          as Hcurrent_policy_id_dom.
        { apply elem_of_dom. eexists. exact Hcurrent_policy_id_in_identity. }
        assert (current_policy_id ∈ dom policies) as Hcurrent_policy_id_policies.
        { eapply Habs_identities_policies; [exact Hcurrent_policy_ids_lookup|].
          exact Hcurrent_policy_id_dom. }
        apply elem_of_dom in Hcurrent_policy_id_policies as
          [policy Hpolicy_lookup].
        pose proof (Hpolicy_frags_consistent current_policy_id policy
          Hpolicy_lookup) as Hsnap_policy_lookup_old.
        rewrite Hsnap_policy_lookup in Hsnap_policy_lookup_old.
        inversion Hsnap_policy_lookup_old. subst snap_policy.
        iDestruct (big_sepM_lookup_acc with "Hpolicies")
          as "[Hpolicy Hpolicies_close]".
        { exact Hpolicy_lookup. }
        wp_apply (wp_State__DetachIdentityPolicy γ l current_identity
          (delete_policy_id_list
            (policy_ids_for_identity snap_abs_identities current_identity)
            (take (sint.nat j) policy_id_list))
          current_policy_id policy resource attachments_j q_policy
          with "[$Hiam $Hidentity $Hpolicy $Hattachments]").
        { iPureIntro. split.
          - exact Hattached.
          - symmetry. exact Hcurrent_policy_id_matches. }
        iIntros (attachments_next)
          "(Hidentity & Hpolicy & Hattachments & %Hattachments_next)".
        iDestruct ("Hpolicies_close" with "Hpolicy") as "Hpolicies".
        wp_auto.
        assert (attachments_j !! current_identity =
          Some (length policy_id_list - sint.nat j)) as Hattachments_j_count.
        { destruct (decide (sint.nat j < length policy_id_list)%nat)
            as [_|Hnot_lt]; [exact Hattachments_j_current|].
          exfalso. lia. }
        wp_for_post.
        iFrame "HΦ Hpolicy_ids_sl Hidentities_rest Hpolicies".
        iFrame.
        iPureIntro. split_and!.
        -- word.
        -- destruct Hj_current as [_ Hj_lt].
           replace (sint.Z (word.add j (W64 1))) with
             (sint.Z j + 1)%Z by word.
           lia.
        -- replace (Z.to_nat (sint.Z (word.add j (W64 1)))) with
             (S (sint.nat j)) by word.
           rewrite (take_S_r _ _ _ Hcurrent_policy_id_lookup).
           rewrite delete_policy_id_list_snoc. done.
        -- destruct Hattachments_next as
             [[Hattachments_one ->]|
              [n [Hattachments_n [Hn_ge ->]]]].
           ++ rewrite Hattachments_j_count in Hattachments_one.
              inversion Hattachments_one as [Hcount_one].
              destruct (decide
                (sint.nat (word.add j (W64 1)) < length policy_id_list)%nat)
                as [Hnext_lt|_].
              ** exfalso.
                 replace (sint.nat (word.add j (W64 1))) with
                   (S (sint.nat j)) in Hnext_lt by word.
                 lia.
              ** rewrite lookup_delete_eq. done.
           ++ rewrite Hattachments_j_count in Hattachments_n.
              inversion Hattachments_n as [Hcount_n]. subst n.
              destruct (decide
                (sint.nat (word.add j (W64 1)) < length policy_id_list)%nat)
                as [Hnext_lt|Hnext_not_lt].
              ** rewrite lookup_insert_eq. f_equal.
                 replace (sint.nat (word.add j (W64 1))) with
                   (S (sint.nat j)) by word.
                 lia.
              ** exfalso.
                 replace (sint.nat (word.add j (W64 1))) with
                   (S (sint.nat j)) in Hnext_not_lt by word.
                 lia.
        -- intros identity' Hne.
           destruct Hattachments_next as
             [[_ ->]|[n [_ [_ ->]]]].
           ++ rewrite lookup_delete_ne; [done|apply Hattachments_j_other; done].
           ++ rewrite lookup_insert_ne; [done|apply Hattachments_j_other; done].
      * assert (sint.nat j = length policy_id_list) as Hj_done.
        { destruct Hinner_bounds as [Hj_nonneg Hj_upper_bound].
          assert (Z.of_nat (length policy_id_list) =
            sint.Z (slice.len policy_ids_sl)) as Hpolicy_ids_len_Z.
          { rewrite Hpolicy_ids_len.
            unfold sint.nat.
            rewrite Z2Nat.id; done. }
          assert (sint.Z j ≤ sint.Z (slice.len policy_ids_sl))%Z
            as Hj_upper_len.
          { lia. }
          apply Nat2Z.inj.
          replace (Z.of_nat (sint.nat j)) with (sint.Z j) by word.
          rewrite Hpolicy_ids_len_Z. lia. }
        set (policy_ids_done :=
          delete_policy_id_list
            (policy_ids_for_identity snap_abs_identities current_identity)
            policy_id_list).
        assert (attachments_j !! current_identity = None)
          as Hattachments_j_current_none.
        { destruct (decide (sint.nat j < length policy_id_list)%nat)
            as [Hlt|_]; [lia|exact Hattachments_j_current]. }
        assert (dom attachments_j = dom attachments_i ∖ {[current_identity]})
          as Hattachments_j_dom.
        { apply dom_lookup_removed.
          - apply elem_of_dom. eexists. exact Hattachments_i_current_count.
          - exact Hattachments_j_current_none.
          - exact Hattachments_j_other. }
        iAssert ([∗ map] identity↦policy_ids ∈
          <[current_identity:=policy_ids_done]> abs_identities_i,
          own_iam_identity_frag γ identity 1 policy_ids)%I
          with "[Hidentity Hidentities_rest]" as "Hidentities".
        { rewrite <- (insert_delete_eq abs_identities_i current_identity
            policy_ids_done).
          rewrite big_sepM_insert.
          { apply lookup_delete_eq. }
          iFrame "Hidentities_rest".
          iExactEq "Hidentity". f_equal.
          unfold policy_ids_done.
          rewrite Hj_done.
          replace (take (length policy_id_list) policy_id_list)
            with policy_id_list; [done|].
          symmetry. apply take_ge. apply Nat.le_refl. }
        wp_for_post.
        iFrame "HΦ".
        iFrame "Hdesired resource desired policies identities Hpolicies current
          Hsnapshot_identities Hsnapshot_identities_inner Hsnapshot_policies Hcurrent".
        iExists (word.add i (W64 1)), attachments_j,
          (<[current_identity:=policy_ids_done]> abs_identities_i),
          current_identity.
        iFrame.
        iPureIntro. split_and!.
        -- word.
        -- destruct Hi_current as [_ Hi_lt_current].
           replace (sint.Z (word.add i (W64 1))) with
             (sint.Z i + 1)%Z by word.
           lia.
        -- rewrite Hattachments_j_dom Hattachments_dom_i.
           replace (Z.to_nat (sint.Z (word.add i (W64 1)))) with
             (S (sint.nat i)) by word.
           symmetry.
           apply processed_prefix_remove_identity; [exact Hcurrent_identity_lookup|].
           intros Hdesired.
           apply elem_of_dom in Hdesired as [[] Hdesired_lookup].
           rewrite Hkeep in Hdesired_lookup. done.
        -- rewrite dom_insert_L Habs_identities_dom_i.
           apply set_eq. intros identity'.
           rewrite elem_of_union elem_of_singleton.
           split.
           ++ intros [->|Hin]; [|done].
              apply elem_of_dom. eexists. exact Hcurrent_policy_ids_lookup.
           ++ intros Hin. right. done.
        -- intros identity' policy_ids Hin Hlookup.
           assert (identity' ≠ current_identity) as Hne.
           { intros ->.
             apply (current_not_in_drop_succ current (sint.nat i)
               current_identity Hcurrent_nodup Hcurrent_identity_lookup).
             replace (Z.to_nat (sint.Z (word.add i (W64 1)))) with
               (S (sint.nat i)) in Hin by word.
             exact Hin. }
           change ((<[current_identity:=policy_ids_done]> abs_identities_i)
             !! identity' = Some policy_ids).
           rewrite lookup_insert_ne.
           { intros Heq. apply Hne. symmetry. exact Heq. }
           apply Hunprocessed_identities; [|done].
           apply (drop_succ_subset_current current (sint.nat i) current_identity).
           ++ exact Hcurrent_identity_lookup.
           ++ replace (Z.to_nat (sint.Z (word.add i (W64 1)))) with
                (S (sint.nat i)) in Hin by word.
              exact Hin.
        -- intros identity' Hin.
           assert (identity' ≠ current_identity) as Hne.
           { intros ->.
             apply (current_not_in_drop_succ current (sint.nat i)
               current_identity Hcurrent_nodup Hcurrent_identity_lookup).
             replace (Z.to_nat (sint.Z (word.add i (W64 1)))) with
               (S (sint.nat i)) in Hin by word.
             exact Hin. }
           rewrite (Hattachments_j_other identity' Hne).
           apply Hunprocessed_attachments.
           apply (drop_succ_subset_current current (sint.nat i) current_identity).
           ++ exact Hcurrent_identity_lookup.
           ++ replace (Z.to_nat (sint.Z (word.add i (W64 1)))) with
                (S (sint.nat i)) in Hin by word.
              exact Hin.
  - assert (sint.nat i = length current) as Hi_done.
    { destruct Hi_bounds as [Hi_nonneg Hi_upper_bound].
      assert (Z.of_nat (length current) =
        sint.Z (slice.len current_sl)) as Hcurrent_len_Z.
      { rewrite Hcurrent_len.
        unfold sint.nat.
        rewrite Z2Nat.id; done. }
      assert (sint.Z i ≤ sint.Z (slice.len current_sl))%Z
        as Hi_upper_len.
      { lia. }
      apply Nat2Z.inj.
      replace (Z.of_nat (sint.nat i)) with (sint.Z i) by word.
      rewrite Hcurrent_len_Z. lia. }
    assert (list_to_set (C:=gset iammodel.IdentityID.t) current =
      dom (attachment_counts snap_abs_identities snap_policies resource))
      as Hcurrent_attachments_dom.
    { rewrite Hcurrent_dom. symmetry. exact Hsnapshot_access. }
    wp_apply (wp_missingIdentities with "[$Hpkg $Hdesired $Hcurrent]").
    iIntros (missing_sl missing)
      "(Hdesired & Hcurrent & Hmissing & %Hmissing_nodup & %Hmissing_dom)".
    iDestruct (own_slice_len with "Hmissing") as
      %[Hmissing_len Hmissing_len_nonneg].
    wp_auto.
    wp_if_destruct.
    + assert (missing = []) as Hmissing_empty.
      { apply nil_length_inv. rewrite Hmissing_len e. done. }
      rewrite Hmissing_empty list_to_set_nil in Hmissing_dom.
      assert (dom desired ⊆ list_to_set (C:=gset iammodel.IdentityID.t) current)
        as Hdesired_current.
      { intros identity Hdesired.
        destruct (decide (identity ∈ list_to_set
          (C:=gset iammodel.IdentityID.t) current)) as [|Hnot_current]; [done|].
        assert (identity ∈ (∅ : gset iammodel.IdentityID.t)) as Hin_empty.
        { rewrite Hmissing_dom.
          apply elem_of_difference. split; done. }
        rewrite elem_of_empty in Hin_empty. done. }
      assert (dom attachments_i = dom desired) as Hattachments_i_dom_done.
      { rewrite Hattachments_dom_i Hi_done.
        replace (take (length current) current) with current.
        2:{ symmetry. apply take_ge. apply Nat.le_refl. }
        rewrite Hcurrent_attachments_dom.
        apply set_eq. intros identity.
        rewrite elem_of_difference.
        split.
        - intros [Hcurrent Hnot_removed].
          destruct (decide (identity ∈ dom desired)) as [|Hnot_desired];
            [done|].
          exfalso. apply Hnot_removed.
          apply elem_of_difference. split; done.
        - intros Hdesired.
          split.
          + rewrite -Hcurrent_attachments_dom.
            apply Hdesired_current. done.
          + intros Hremoved.
            apply elem_of_difference in Hremoved as [_ Hnot_desired].
            done. }
      iApply ("HΦ" $! attachments_i abs_identities_i).
      iFrame.
      iSplit; [iPureIntro; exact Hattachments_i_dom_done|].
      iSplit; [iPureIntro; exact Habs_identities_dom_i|].
      destruct (decide (dom desired ⊆
        dom (attachment_counts snap_abs_identities snap_policies resource)))
        as [_|Hnot_subset]; [done|].
      exfalso. apply Hnot_subset.
      rewrite -Hcurrent_attachments_dom. exact Hdesired_current.
    + wp_apply (wp_State__CreatePolicy with "[$Hiam]").
      { iPureIntro. exact Hresource_nonempty. }
      iIntros (policy_id) "Hpolicy_new".
      wp_auto.
      assert (¬ dom desired ⊆
        dom (attachment_counts snap_abs_identities snap_policies resource))
        as Hdesired_not_attachments.
      { intros Hsubset.
        destruct missing as [|missing_head missing_tail] eqn:Hmissing_cases.
        - simpl in Hmissing_len.
          assert (sint.nat (slice.len missing_sl) = 0%nat) as Hlen_zero
            by lia.
          apply n0. word.
          - assert (missing_head ∈ list_to_set
              (C:=gset iammodel.IdentityID.t)
              (missing_head :: missing_tail)) as Hhead_in_missing.
          { rewrite elem_of_list_to_set. left. }
          rewrite Hmissing_dom in Hhead_in_missing.
          apply elem_of_difference in Hhead_in_missing as
            [Hhead_desired Hhead_not_current].
          apply Hhead_not_current.
          rewrite Hcurrent_attachments_dom.
          apply Hsubset. exact Hhead_desired. }
      iAssert (∃ (j : w64)
          (attachments_j : gmap iammodel.IdentityID.t nat)
          (abs_identities_j :
            gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
          (last_identity : iammodel.IdentityID.t),
        "Hattachments" ∷ own_iam_attachments_frag γ resource 1 attachments_j ∗
        "Hidentities" ∷ ([∗ map] identity↦policy_ids ∈ abs_identities_j,
          own_iam_identity_frag γ identity 1 policy_ids) ∗
        "Hpolicy_new" ∷ own_iam_policy_frag γ policy_id 1
          (iammodel.IdentityPolicy.mk policy_id resource) ∗
        "Hmissing" ∷ missing_sl ↦* missing ∗
        "identity" ∷ identity_ptr ↦ last_identity ∗
        "i" ∷ i_ptr ↦ j ∗
        "%Hattach_bounds" ∷ ⌜
          (0 ≤ sint.Z j ≤ Z.of_nat (length missing))%Z ⌝ ∗
        "%Hattachments_dom_j" ∷ ⌜
          dom attachments_j =
          dom attachments_i ∪
            list_to_set (C:=gset iammodel.IdentityID.t)
              (take (sint.nat j) missing) ⌝ ∗
        "%Habs_identities_dom_j" ∷ ⌜
          dom abs_identities_j = dom abs_identities ⌝
      )%I with
        "[Hattachments Hidentities Hpolicy_new Hmissing
          identity i]" as "Hattach".
      { iExists (W64 0), attachments_i, abs_identities_i, ""%go.
        iFrame. iPureIntro. split_and!.
        - word.
        - apply Nat2Z.is_nonneg.
        - rewrite take_0 list_to_set_nil. Timeout 10 set_solver.
        - exact Habs_identities_dom_i. }
      wp_for "Hattach".
      wp_if_destruct.
      * destruct Hattach_bounds as [Hj_nonneg Hj_upper].
        destruct (decide
          (0 ≤ sint.Z j < sint.Z (slice.len missing_sl))%Z)
          as [_|Hidx_bad]; last first.
        { exfalso. apply Hidx_bad. split; done. }
        assert (0 ≤ sint.Z j < Z.of_nat (length missing))%Z
          as Hj_current.
        { split; [done|].
          rewrite Hmissing_len. word. }
        list_elem missing (sint.Z j) as current_identity.
        wp_apply (wp_load_slice_index
          (V:=iammodel.IdentityID.t) (t:=iammodel.IdentityID)
          missing_sl (sint.Z j) missing (DfracOwn 1) current_identity
          with "[$Hmissing]").
        { done. }
        { done. }
        iIntros "Hmissing".
        wp_auto.
        assert (current_identity ∈ list_to_set
          (C:=gset iammodel.IdentityID.t) missing)
          as Hcurrent_identity_in_missing.
        { apply elem_of_list_to_set. eapply list_elem_of_lookup_2.
          exact Hcurrent_identity_lookup. }
        assert (current_identity ∈ dom desired) as Hcurrent_identity_desired.
        { rewrite Hmissing_dom in Hcurrent_identity_in_missing.
          apply elem_of_difference in Hcurrent_identity_in_missing as [Hin _].
          exact Hin. }
        assert (current_identity ∈ dom abs_identities_j)
          as Hcurrent_identity_abs_j.
        { rewrite Habs_identities_dom_j.
          apply Hdesired_identities. exact Hcurrent_identity_desired. }
        apply elem_of_dom in Hcurrent_identity_abs_j as
          [policy_ids Hpolicy_ids_lookup].
        iDestruct (big_sepM_delete _ abs_identities_j current_identity
          policy_ids with "Hidentities")
          as "[Hidentity Hidentities_rest]".
        { exact Hpolicy_ids_lookup. }
        wp_apply (wp_State__AttachIdentityPolicy γ l current_identity
          policy_ids policy_id (iammodel.IdentityPolicy.mk policy_id resource)
          resource attachments_j 1
          with "[$Hiam $Hidentity $Hpolicy_new $Hattachments]").
        { iPureIntro. done. }
        iIntros (n_att)
          "(Hidentity & Hpolicy_new & Hattachments & %Hn_att_positive)".
        wp_auto.
        iAssert ([∗ map] identity↦policy_ids ∈
          <[current_identity:=<[policy_id:=tt]> policy_ids]> abs_identities_j,
          own_iam_identity_frag γ identity 1 policy_ids)%I
          with "[Hidentity Hidentities_rest]" as "Hidentities".
        { rewrite <- (insert_delete_eq abs_identities_j current_identity
            (<[policy_id:=tt]> policy_ids)).
          rewrite big_sepM_insert.
          { apply lookup_delete_eq. }
          iFrame. }
        wp_for_post.
        iFrame "HΦ Hdesired Hpolicies Hsnapshot_identities
          Hsnapshot_identities_inner Hsnapshot_policies Hcurrent policyID".
        iExists (word.add j (W64 1)),
          (<[current_identity:=n_att]> attachments_j),
          (<[current_identity:=<[policy_id:=tt]> policy_ids]> abs_identities_j),
          current_identity.
        iFrame.
        iPureIntro. split_and!.
        -- word.
        -- destruct Hj_current as [_ Hj_lt].
           replace (sint.Z (word.add j (W64 1))) with
             (sint.Z j + 1)%Z by word.
           lia.
        -- rewrite dom_insert_L Hattachments_dom_j.
           replace (Z.to_nat (sint.Z (word.add j (W64 1)))) with
             (S (sint.nat j)) by word.
           rewrite (take_S_r _ _ _ Hcurrent_identity_lookup).
           apply set_eq. intros identity'.
           rewrite !elem_of_union !elem_of_singleton !elem_of_list_to_set
             elem_of_app /=.
           Timeout 10 set_solver.
        -- rewrite dom_insert_L Habs_identities_dom_j.
           apply set_eq. intros identity'.
           rewrite elem_of_union elem_of_singleton.
           split.
           ++ intros [->|Hin]; [|done].
              apply Hdesired_identities. exact Hcurrent_identity_desired.
           ++ intros Hin. right. done.
      * assert (sint.nat j = length missing) as Hj_done.
        { destruct Hattach_bounds as [Hj_nonneg Hj_upper_bound].
          assert (Z.of_nat (length missing) =
            sint.Z (slice.len missing_sl)) as Hmissing_len_Z.
          { rewrite Hmissing_len.
            unfold sint.nat.
            rewrite Z2Nat.id; done. }
          assert (sint.Z j ≤ sint.Z (slice.len missing_sl))%Z
            as Hj_upper_len.
          { lia. }
          apply Nat2Z.inj.
          replace (Z.of_nat (sint.nat j)) with (sint.Z j) by word.
          rewrite Hmissing_len_Z. lia. }
        assert (dom attachments_j = dom desired) as Hattachments_final_dom.
        { rewrite Hattachments_dom_j Hattachments_dom_i Hi_done Hj_done.
          replace (take (length current) current) with current.
          2:{ symmetry. apply take_ge. apply Nat.le_refl. }
          replace (take (length missing) missing) with missing.
          2:{ symmetry. apply take_ge. apply Nat.le_refl. }
          rewrite Hcurrent_attachments_dom Hmissing_dom.
          apply set_eq. intros identity.
          rewrite elem_of_union !elem_of_difference.
          split.
          - intros [[Hattached Hnot_removed]|[Hdesired Hnot_attached]];
              [|done].
            destruct (decide (identity ∈ dom desired)) as [|Hnot_desired];
              [done|].
            exfalso. apply Hnot_removed. split; done.
          - intros Hdesired.
            destruct (decide (identity ∈ dom
              (attachment_counts snap_abs_identities snap_policies resource)))
              as [Hattached|Hnot_attached].
            + left. split; [done|].
              intros Hremoved.
              destruct Hremoved as [_ Hnot_desired].
              done.
            + right. split; [done|].
              rewrite Hcurrent_attachments_dom. done. }
        iApply ("HΦ" $! attachments_j abs_identities_j).
        iFrame.
        iSplit; [iPureIntro; exact Hattachments_final_dom|].
        iSplit; [iPureIntro; exact Habs_identities_dom_j|].
        destruct (decide (dom desired ⊆
          dom (attachment_counts snap_abs_identities snap_policies resource)))
          as [Hsubset|_].
        { exfalso. apply Hdesired_not_attachments. exact Hsubset. }
        iExists policy_id. iFrame.
        Unshelve.
        all: try (unfold iammodel.IdentityID.t, iammodel.PolicyID.t; apply _).
Qed.

End proof.
