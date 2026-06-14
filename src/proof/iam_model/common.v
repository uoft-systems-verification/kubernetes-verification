From New.proof Require Import prelude empty_ffi.
From New.proof Require Import external_wp.
From New.proof.map Require Import for_range.
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

Lemma is_pkg_init_errors_trivial :
  ⊢ (is_pkg_init errors : iProp Σ).
Proof.
  iEval (rewrite is_pkg_init_unfold /=). iSplit; iModIntro; done.
Qed.

Lemma is_pkg_init_race_trivial :
  ⊢ (is_pkg_init race : iProp Σ).
Proof.
  iEval (rewrite is_pkg_init_unfold /=). iSplit; iModIntro; done.
Qed.

Lemma is_pkg_init_synctest_trivial :
  ⊢ (is_pkg_init synctest : iProp Σ).
Proof.
  iEval (rewrite is_pkg_init_unfold /=). iSplit; iModIntro; done.
Qed.

Lemma is_pkg_init_atomic_trivial :
  ⊢ (is_pkg_init atomic : iProp Σ).
Proof.
  iEval (rewrite is_pkg_init_unfold /=). iSplit; iModIntro; done.
Qed.

Lemma is_pkg_init_sync_trivial :
  ⊢ (is_pkg_init sync : iProp Σ).
Proof.
  iEval (rewrite is_pkg_init_unfold /=).
  iSplit.
  - iModIntro. iSplit; [iApply is_pkg_init_synctest_trivial|].
    iSplit; [iApply is_pkg_init_race_trivial|].
    iSplit; [iApply is_pkg_init_atomic_trivial|done].
  - iModIntro. done.
Qed.

Lemma is_pkg_init_io_trivial :
  ⊢ (is_pkg_init io : iProp Σ).
Proof.
  iEval (rewrite is_pkg_init_unfold /=).
  iSplit.
  - iModIntro. iSplit; [iApply is_pkg_init_errors_trivial|].
    iSplit; [iApply is_pkg_init_sync_trivial|done].
  - iModIntro. done.
Qed.

Lemma is_pkg_init_fmt_trivial :
  ⊢ (is_pkg_init fmt : iProp Σ).
Proof.
  iEval (rewrite is_pkg_init_unfold /=).
  iSplit.
  - iModIntro. iSplit; [iApply is_pkg_init_io_trivial|done].
  - iModIntro. done.
Qed.

Definition processed_map `{Countable K} {A}
    (keys : list K) (i : Z) (m : gmap K A) : gmap K A :=
  filter (λ '(k, _), k ∈ list_to_set (C:=gset K) (take (Z.to_nat i) keys)) m.

Lemma current_key_not_in_take `{EqDecision A} `{Countable A} (keys : list A) i key :
  NoDup keys →
  keys !! Z.to_nat i = Some key →
  (0 ≤ i)%Z →
  key ∉ list_to_set (C:=gset A) (take (Z.to_nat i) keys).
Proof.
  intros Hnodup Hlookup Hi_nonneg Hin.
  rewrite elem_of_list_to_set in Hin.
  apply list_elem_of_lookup_1 in Hin as [j Htake_lookup].
  apply lookup_take_Some in Htake_lookup as [Hlookup_j Hj].
  pose proof (NoDup_lookup _ _ _ _ Hnodup Hlookup_j Hlookup) as ->.
  lia.
Qed.

Lemma processed_map_empty `{Countable K} {A} (keys : list K) (m : gmap K A) :
  processed_map keys 0 m = ∅.
Proof.
  apply map_eq. intros key.
  rewrite /processed_map map_lookup_filter lookup_empty take_0.
  destruct (m !! key); simpl; [|done].
  destruct (decide (key ∈ list_to_set (C:=gset K) [])); [|done].
  rewrite elem_of_list_to_set elem_of_nil in e. done.
Qed.

Lemma processed_map_lookup_not_current `{Countable K} {A}
    (keys : list K) i key (m : gmap K A) :
  NoDup keys →
  keys !! Z.to_nat i = Some key →
  (0 ≤ i)%Z →
  processed_map keys i m !! key = None.
Proof.
  intros Hnodup Hlookup Hi_nonneg.
  rewrite /processed_map. apply map_lookup_filter_None_2. right.
  intros x Hx Hin. simpl in Hin.
  exact ((current_key_not_in_take keys i key Hnodup Hlookup Hi_nonneg) Hin).
Qed.

Lemma processed_map_insert `{Countable K} {A}
    (keys : list K) i key (m : gmap K A) v :
  NoDup keys →
  (0 ≤ i)%Z →
  keys !! Z.to_nat i = Some key →
  m !! key = Some v →
  processed_map keys (i + 1) m = <[key:=v]> (processed_map keys i m).
Proof.
  intros Hnodup Hi_nonneg Hkey_lookup Hm_lookup.
  apply map_eq. intros key'.
  destruct (decide (key' = key)) as [->|Hne].
  - rewrite lookup_insert_eq /processed_map.
    apply map_lookup_filter_Some_2; [done|].
    simpl.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite (take_S_r _ _ _ Hkey_lookup).
    rewrite elem_of_list_to_set elem_of_app /=. right. Timeout 10 set_solver.
  - replace (<[key:=v]> (processed_map keys i m) !! key') with
      (processed_map keys i m !! key').
    2:{ symmetry. apply lookup_insert_ne.
        intro Heq. apply Hne. symmetry. exact Heq. }
    assert (Hin_iff : key' ∈ list_to_set (C:=gset K)
        (take (Z.to_nat (i + 1)) keys) ↔
      key' ∈ list_to_set (C:=gset K) (take (Z.to_nat i) keys)).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite (take_S_r _ _ _ Hkey_lookup).
      rewrite !elem_of_list_to_set elem_of_app /= elem_of_cons elem_of_nil.
      split; intros Hin.
      - destruct Hin as [Hin|Hin]; [done|].
        destruct Hin as [Heq|[]]. subst. contradiction.
      - left. done. }
    destruct (m !! key') as [v'|] eqn:Hm_lookup'.
    + destruct (decide (key' ∈ list_to_set (C:=gset K)
        (take (Z.to_nat i) keys))) as [Hin|Hnot].
      * rewrite /processed_map.
        transitivity (Some v').
        -- apply map_lookup_filter_Some_2; [done|].
           simpl. apply Hin_iff. done.
        -- symmetry. apply map_lookup_filter_Some_2; [done|done].
      * rewrite /processed_map.
        transitivity (@None A).
        -- apply map_lookup_filter_None_2. right.
           intros x Hx Hin_succ. simpl in Hin_succ.
           apply Hnot. apply Hin_iff. done.
        -- symmetry. apply map_lookup_filter_None_2. right.
           intros x Hx Hin_old. done.
    + rewrite /processed_map.
      transitivity (@None A).
      * apply map_lookup_filter_None_2. left. done.
      * symmetry. apply map_lookup_filter_None_2. left. done.
Qed.

Lemma processed_map_all `{Countable K} {A} (keys : list K) (m : gmap K A) :
  list_to_set keys = dom m →
  length keys = size m →
  processed_map keys (Z.of_nat (size m)) m = m.
Proof.
  intros Hdom Hlen. apply map_eq. intros key.
  destruct (m !! key) as [v|] eqn:Hlookup.
  - rewrite /processed_map. apply map_lookup_filter_Some_2; [done|].
    simpl. rewrite Nat2Z.id. replace (size m) with (length keys) by done.
    replace (take (length keys) keys) with keys
      by (symmetry; apply take_ge; lia).
    rewrite Hdom elem_of_dom. eexists. exact Hlookup.
  - rewrite /processed_map. apply map_lookup_filter_None_2. left. done.
Qed.

Lemma wp_copyIdentities
    (src : map.t)
    (phys_identities : gmap iammodel.IdentityID.t map.t)
    (abs_identities : gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit))
    dq_src dq_inner :
  {{{ "Hsrc" ∷ src ↦${dq_src} phys_identities ∗
      "Hinner" ∷ ([∗ map] policy_ids_l; policy_ids ∈
        phys_identities; abs_identities,
        policy_ids_l ↦${dq_inner} policy_ids)
  }}}
    @! iammodel.copyIdentities #src
  {{{ dst phys_identities_copy, RET #dst;
      "Hsrc" ∷ src ↦${dq_src} phys_identities ∗
      "Hinner" ∷ ([∗ map] policy_ids_l; policy_ids ∈
        phys_identities; abs_identities,
        policy_ids_l ↦${dq_inner} policy_ids) ∗
      "Hdst" ∷ dst ↦$ phys_identities_copy ∗
      "Hdst_inner" ∷ ([∗ map] policy_ids_l; policy_ids ∈
        phys_identities_copy; abs_identities,
        policy_ids_l ↦$ policy_ids)
  }}}.
Proof.
  wp_start as "H".
  iNamed "H".
  wp_auto.
  rewrite exception_do_unseal /exception_do_def.
  wp_apply wp_map_make1 as "%identities_l Hdst".
  wp_apply (wp_map_for_range_return_func (key_type:=iammodel.IdentityID)
    (λ (keys : list iammodel.IdentityID.t) i,
      ∃ (last_policy_ids_l : map.t) (last_identity : iammodel.IdentityID.t)
        (dst_phys : gmap iammodel.IdentityID.t map.t),
        "Hinner" ∷ ([∗ map] policy_ids_l; policy_ids ∈
          phys_identities; abs_identities, policy_ids_l ↦${dq_inner} policy_ids) ∗
        "policyIDs" ∷ policyIDs_ptr ↦ last_policy_ids_l ∗
        "identity" ∷ identity_ptr ↦ last_identity ∗
        "identities" ∷ identities_ptr ↦ identities_l ∗
        "Hdst" ∷ identities_l ↦$ dst_phys ∗
        "Hdst_inner" ∷ ([∗ map] policy_ids_l; policy_ids ∈
          dst_phys; processed_map keys i abs_identities,
          policy_ids_l ↦$ policy_ids))%I
    with "Hsrc").
  { done. }
  iIntros (keys) "%Hkeys".
  iSplitL "Hinner policyIDs identity identities Hdst".
  { iExists map.nil, (""%go : iammodel.IdentityID.t), ∅. iFrame.
    rewrite processed_map_empty big_sepM2_empty. done. }
  iSplitL "".
  { iModIntro. iIntros (i identity policy_ids_l) "%Hiter Hloop".
    destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
    destruct Hiter as [Hi_bounds [Hidentity_lookup Hphys_lookup]].
    destruct Hi_bounds as [Hi_nonneg Hi_upper].
    iDestruct "Hloop" as (last_policy_ids_l last_identity dst_phys)
      "(Hinner & policyIDs & identity & identities & Hdst & Hdst_inner)".
    iDestruct (big_sepM2_dom with "Hinner") as %Hinner_dom.
    assert (is_Some (abs_identities !! identity)) as [policy_ids Habs_lookup].
    { apply elem_of_dom. rewrite -Hinner_dom.
      apply elem_of_dom. eexists. exact Hphys_lookup. }
    assert (processed_map keys i abs_identities !! identity = None)
      as Hprocessed_fresh.
    { apply processed_map_lookup_not_current; done. }
    iDestruct (big_sepM2_dom with "Hdst_inner") as %Hdst_dom.
    assert (dst_phys !! identity = None) as Hdst_fresh.
    { apply not_elem_of_dom. intros Hdst_in.
      rewrite Hdst_dom in Hdst_in.
      apply elem_of_dom in Hdst_in as [? Hprocessed_some].
      rewrite Hprocessed_fresh in Hprocessed_some. done. }
    assert (processed_map keys (i + 1) abs_identities =
      <[identity:=policy_ids]> (processed_map keys i abs_identities))
      as Hprocessed_insert.
    { apply processed_map_insert; done. }
    iDestruct (big_sepM2_lookup_acc _ _ _ identity policy_ids_l policy_ids
      Hphys_lookup Habs_lookup with "Hinner") as "[HpolicyIDs_src Hinner_close]".
    wp_pures.
    simpl subst'.
    wp_auto.
    wp_apply wp_map_make1 as "%policyIDsCopy_l HpolicyIDsCopy".
    wp_apply (wp_map_for_range_return_func (key_type:=iammodel.PolicyID)
      (λ (policy_keys : list iammodel.PolicyID.t) j,
        ∃ (last_policy_id : iammodel.PolicyID.t) (policy_ids_copy_l : map.t),
          "policyID" ∷ policyID_ptr ↦ last_policy_id ∗
          "policyIDsCopy" ∷ policyIDsCopy_ptr ↦ policy_ids_copy_l ∗
          "HpolicyIDsCopy" ∷ policy_ids_copy_l ↦$
            processed_map policy_keys j policy_ids)%I
      with "HpolicyIDs_src").
    { done. }
    iIntros (policy_keys) "%Hpolicy_keys".
    iSplitL "policyID policyIDsCopy HpolicyIDsCopy".
    { iExists (""%go : iammodel.PolicyID.t), policyIDsCopy_l. iFrame.
      rewrite processed_map_empty. iFrame. }
    iSplitL "".
    { iModIntro. iIntros (j policy_id []) "%Hpolicy_iter Hinner_loop".
      destruct Hpolicy_keys as [Hpolicy_keys_dom
        [Hpolicy_keys_len Hpolicy_keys_nodup]].
      destruct Hpolicy_iter as [Hj_bounds [Hpolicy_key_lookup Hpolicy_lookup]].
      destruct Hj_bounds as [Hj_nonneg Hj_upper].
      iDestruct "Hinner_loop" as (last_policy_id policy_ids_copy_l)
        "(policyID & policyIDsCopy & HpolicyIDsCopy)".
      wp_pures.
      simpl subst'.
      wp_auto.
      wp_apply (wp_map_insert iammodel.PolicyID with "[$HpolicyIDsCopy]").
      iIntros "HpolicyIDsCopy". wp_auto.
      iRight. iSplit; [done|].
      iExists policy_id, policy_ids_copy_l. iFrame.
      rewrite -processed_map_insert; done. }
    iIntros "HpolicyIDs_src Hinner_done".
    iDestruct "Hinner_done" as (last_policy_id policy_ids_copy_l)
      "(policyID & policyIDsCopy & HpolicyIDsCopy)".
    destruct Hpolicy_keys as [Hpolicy_keys_dom
      [Hpolicy_keys_len Hpolicy_keys_nodup]].
    rewrite (processed_map_all policy_keys policy_ids
      Hpolicy_keys_dom Hpolicy_keys_len).
    iDestruct ("Hinner_close" with "HpolicyIDs_src") as "Hinner".
    wp_auto.
    wp_apply (wp_map_insert iammodel.IdentityID with "[$Hdst]").
    iIntros "Hdst". wp_auto.
    iAssert (([∗ map] policy_ids_l'; policy_ids' ∈
      <[identity:=policy_ids_copy_l]> dst_phys;
      processed_map keys (i + 1) abs_identities,
      policy_ids_l' ↦$ policy_ids')%I)
      with "[HpolicyIDsCopy Hdst_inner]" as "Hdst_inner".
    { rewrite Hprocessed_insert.
      rewrite (big_sepM2_insert _ dst_phys
        (processed_map keys i abs_identities)
        identity policy_ids_copy_l policy_ids Hdst_fresh Hprocessed_fresh).
      iFrame. }
    iRight. iSplit; [done|].
    iExists policy_ids_l, identity, (<[identity:=policy_ids_copy_l]> dst_phys).
    iFrame. }
  iIntros "Hsrc Hloop".
  iDestruct "Hloop" as (last_policy_ids_l last_identity dst_phys)
    "(Hinner & policyIDs & identity & identities & Hdst & Hdst_inner)".
  destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
  iDestruct (big_sepM2_dom with "Hinner") as %Hinner_dom.
  assert (Habs_size : size abs_identities = size phys_identities).
  { rewrite -(size_dom phys_identities) -(size_dom abs_identities).
    rewrite Hinner_dom. done. }
  replace (processed_map keys (Z.of_nat (size phys_identities)) abs_identities)
    with abs_identities.
  2:{ rewrite -Habs_size. symmetry. apply processed_map_all.
      - rewrite Hkeys_dom Hinner_dom. done.
      - rewrite Habs_size. done. }
  wp_auto.
  rewrite return_val_unseal /return_val_def. wp_auto.
  iApply ("HΦ" $! identities_l dst_phys). iFrame.
Unshelve.
  all: unfold iammodel.IdentityID.t, iammodel.PolicyID.t; apply _.
Qed.

Lemma wp_copyPolicies
    (src : map.t) (policies : gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t) dq :
  {{{ "Hsrc" ∷ src ↦${dq} policies }}}
    @! iammodel.copyPolicies #src
  {{{ dst, RET #dst;
      "Hsrc" ∷ src ↦${dq} policies ∗
      "Hdst" ∷ dst ↦$ policies
  }}}.
Proof.
  wp_start as "H".
  iNamed "H".
  wp_auto.
  rewrite exception_do_unseal /exception_do_def.
  wp_apply wp_map_make1 as "%policies_l Hdst".
  wp_apply (wp_map_for_range_return_func (key_type:=iammodel.PolicyID)
    (λ (keys : list iammodel.PolicyID.t) i,
      ∃ (last_policy : iammodel.IdentityPolicy.t)
        (last_policy_id : iammodel.PolicyID.t),
        "policy" ∷ policy_ptr ↦ last_policy ∗
        "policyID" ∷ policyID_ptr ↦ last_policy_id ∗
        "policies" ∷ policies_ptr ↦ policies_l ∗
        "Hdst" ∷ policies_l ↦$ processed_map keys i policies)%I
    with "Hsrc").
  { done. }
  iIntros (keys) "%Hkeys".
  iSplitL "policy policyID policies Hdst".
  { iExists (zero_val _), (""%go : iammodel.PolicyID.t). iFrame.
    rewrite processed_map_empty. iFrame. }
  iSplitL "".
  { iModIntro. iIntros (i policy_id policy) "%Hiter Hloop".
    destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
    destruct Hiter as [Hi_bounds [Hpolicy_id_lookup Hpolicy_lookup]].
    destruct Hi_bounds as [Hi_nonneg Hi_upper].
    iDestruct "Hloop" as (last_policy last_policy_id)
      "(policy & policyID & policies & Hdst)".
    wp_pures.
    simpl subst'.
    wp_auto.
    wp_apply (wp_map_insert iammodel.PolicyID with "[$Hdst]").
    iIntros "Hdst". wp_auto.
    iRight. iSplit; [done|].
    iExists policy, policy_id. iFrame.
    rewrite -processed_map_insert; done. }
  iIntros "Hsrc Hloop".
  iDestruct "Hloop" as (last_policy last_policy_id)
    "(policy & policyID & policies & Hdst)".
  destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
  rewrite (processed_map_all keys policies Hkeys_dom Hkeys_len).
  wp_auto.
  rewrite return_val_unseal /return_val_def. wp_auto.
  iApply ("HΦ" $! policies_l). iFrame.
Unshelve.
  all: unfold iammodel.PolicyID.t; apply _.
Qed.

Lemma wp_generatePolicyID :
  {{{ True }}}
    @! iammodel.generatePolicyID #()
  {{{ (policy_id : iammodel.PolicyID.t), RET #policy_id; True }}}.
Proof.
  wp_start as "_".
  rewrite exception_do_unseal /exception_do_def.
  wp_bind (@! rand.Int63 #())%E.
  iApply (wp_rand_Int63 with "[] [HΦ]").
  { iEval (rewrite is_pkg_init_unfold /=). done. }
  iNext.
  iIntros (n) "_".
  wp_auto.
  wp_apply (wp_slice_literal (V:=interface.t) (t:=go.any)).
  iSplitR; first done.
  iIntros (args) "[Hargs _]". wp_auto.
  wp_apply (wp_fmt_Sprintf with "[$Hargs]").
  { iApply is_pkg_init_fmt_trivial. }
  iIntros (policy_id) "_".
  wp_auto.
  rewrite return_val_unseal /return_val_def. wp_auto.
  iApply "HΦ". done.
Qed.

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
