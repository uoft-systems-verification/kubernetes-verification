From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv common.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG Σ}.
Context `{!mono_gsetG types.UID.t Σ}.

Lemma tombed_uid_delete_eq_used_uid_sub
  (abs_state : gmap KKey.t KObjectV.t) (used_uid tombed_uid : gset types.UID.t) key kobj :
  tombed_uid = used_uid ∖ map_to_set (C:=gset types.UID.t)
    (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj)) abs_state →
  map_Forall
    (λ (k' : KKey.t) (obj' : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta kobj) =
    ObjectMetaV.UID' (KObjectV.objectmeta obj') → key = k') abs_state →
  ObjectMetaV.UID' (KObjectV.objectmeta kobj) ∈ used_uid →
  abs_state !! key = Some kobj →
  tombed_uid ∪ {[ObjectMetaV.UID' (KObjectV.objectmeta kobj)]} =
  used_uid ∖ map_to_set (C:=gset types.UID.t)
    (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj)) (delete key abs_state).
Proof.
  intros Htombed Hunique_id Huid_in Hlookup_abs.
  set (uid := ObjectMetaV.UID' (KObjectV.objectmeta kobj)).
  set (uids := λ m : gmap KKey.t KObjectV.t,
    map_to_set (C:=gset types.UID.t)
      (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj))
      m).
  assert (uid ∉ uids (delete key abs_state)) as Huid_not_in_deleted.
  { intros Hcontra.
    rewrite /uids elem_of_map_to_set in Hcontra.
    destruct Hcontra as (key' & obj' & Hlookup_abs' & Huid_eq).
    apply lookup_delete_Some in Hlookup_abs' as [Hkey_neq Hlookup_abs'].
    pose proof (map_Forall_lookup_1 _ _ _ _ Hunique_id Hlookup_abs') as Hkey_eq.
    apply Hkey_neq.
    eapply Hkey_eq.
    symmetry; exact Huid_eq.
  }
  assert (uids abs_state = {[uid]} ∪ uids (delete key abs_state)) as Hmap_to_set_delete.
  { rewrite /uids.
    rewrite <- (insert_delete_id abs_state key kobj Hlookup_abs) at 1.
    assert (delete key abs_state !! key = None) as Hlookup_delete.
    { apply lookup_delete_eq. }
    rewrite (map_to_set_insert_L
      (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj))
      (delete key abs_state) key kobj Hlookup_delete).
    reflexivity.
  }
  rewrite /uids in Huid_not_in_deleted, Hmap_to_set_delete.
  rewrite Htombed Hmap_to_set_delete.
  change (
    (used_uid ∖ ({[uid]} ∪ uids (delete key abs_state))) ∪ {[uid]} =
    used_uid ∖ uids (delete key abs_state)
  ).
  apply set_eq. intros uid'.
  change (
    uid' ∈ (used_uid ∖ ({[uid]} ∪ uids (delete key abs_state))) ∪ {[uid]} ↔
    uid' ∈ used_uid ∖ uids (delete key abs_state)
  ).
  rewrite !elem_of_union !elem_of_difference !elem_of_singleton.
  destruct (decide (uid' = uid)) as [->|Huid_neq].
  - split.
    + intros _. split; [exact Huid_in|exact Huid_not_in_deleted].
    + intros _. right. reflexivity.
  - split.
    + intros H.
      destruct H as [H|H].
      * destruct H as [Huid_used0 Huid_not_in0].
        split; [done|].
        intros Huid_in_deleted0.
        apply Huid_not_in0.
        rewrite elem_of_union.
        right. exact Huid_in_deleted0.
      * exfalso. apply Huid_neq. exact H.
    + intros H.
      destruct H as [Huid_used0 Huid_not_in_deleted0].
      left. split; [done|].
      intros Hcontra.
      rewrite elem_of_union in Hcontra.
      destruct Hcontra as [Huid_eq0|Huid_in_deleted0].
      * rewrite elem_of_singleton in Huid_eq0.
        apply Huid_neq. exact Huid_eq0.
      * exact (Huid_not_in_deleted0 Huid_in_deleted0).
Qed.

Lemma tombed_uid_update_eq_used_uid_sub
  (abs_state : gmap KKey.t KObjectV.t) (used_uid tombed_uid : gset types.UID.t)
  key old_kobj new_kobj :
  tombed_uid = used_uid ∖ map_to_set (C:=gset types.UID.t)
    (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj)) abs_state →
  abs_state !! key = Some old_kobj →
  ObjectMetaV.UID' (KObjectV.objectmeta new_kobj) =
    ObjectMetaV.UID' (KObjectV.objectmeta old_kobj) →
  tombed_uid = used_uid ∖ map_to_set (C:=gset types.UID.t)
    (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj))
    (<[key := new_kobj]> abs_state).
Proof.
  intros Htombed Hlookup_abs Huid_eq.
  set (uid := ObjectMetaV.UID' (KObjectV.objectmeta old_kobj)).
  set (uids := λ m : gmap KKey.t KObjectV.t,
    map_to_set (C:=gset types.UID.t)
      (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj))
      m).
  assert (uids abs_state = {[uid]} ∪ uids (delete key abs_state)) as Hmap_to_set_old.
  { rewrite /uids.
    rewrite <- (insert_delete_id abs_state key old_kobj Hlookup_abs) at 1.
    assert (delete key abs_state !! key = None) as Hlookup_delete.
    { apply lookup_delete_eq. }
    rewrite (map_to_set_insert_L
      (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj))
      (delete key abs_state) key old_kobj Hlookup_delete).
    reflexivity.
  }
  assert (uids (<[key := new_kobj]> abs_state) = {[uid]} ∪ uids (delete key abs_state))
    as Hmap_to_set_new.
  { rewrite /uids.
    rewrite <- (insert_delete_eq abs_state key new_kobj).
    assert (delete key abs_state !! key = None) as Hlookup_delete.
    { apply lookup_delete_eq. }
    rewrite (map_to_set_insert_L
      (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj))
      (delete key abs_state) key new_kobj Hlookup_delete).
    rewrite Huid_eq.
    reflexivity.
  }
  rewrite Htombed.
  change (used_uid ∖ uids abs_state = used_uid ∖ uids (<[key := new_kobj]> abs_state)).
  rewrite Hmap_to_set_old Hmap_to_set_new.
  reflexivity.
Qed.

(* TODO: specifies in which case the object is deleted from the state map *)
(* TODO: finish all the shelved goals once wp_if_join is available *)
Lemma wp_State__delete_au γ l key options_c options:
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options 1 ∗
    "%Hvalid_options" ∷ ⌜ DeleteOptionsV.valid options ⌝ ∗
    ( |={⊤,∅}=> ∃ uid kmeta parent_key parent_uid children,
      "%Hkey_in" ∷ ⌜ key ∈ children ⌝ ∗
      "%Hgeneration_no_overflow" ∷ ⌜ 0 ≤ sint.Z kmeta.(ObjectMetaV.Generation') + 1 < 2^63 ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hclose" ∷ ( ∀ err kmeta',
        (* delete succeeds as uid and rv matches *)
        ⌜ delete_preconditions_match kmeta options ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ( (* the object is marked as deleting (DeletionTimestamp is set) but still exists *)
          ⌜kmeta'.(ObjectMetaV.DeletionTimestamp') ≠ None⌝ ∗
          own_meta_frag γ key uid 1 kmeta' ∗
          own_children_frag γ parent_key parent_uid 1 children
          ∨
          (* the object is deleted *)
          own_tombstone_frag γ uid ∗
          own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]})
        )
        ∨
        (* delete fails as the delete preconditions do not match *)
        ⌜ ¬ delete_preconditions_match kmeta options ⌝ ∗
        ⌜ err ≠ interface.nil ⌝ ∗
        own_meta_frag γ key uid 1 kmeta ∗
        own_children_frag γ parent_key parent_uid 1 children
          ={∅,⊤}=∗ ▷ Φ (# err)
      )
    ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "delete" #key #options_c {{ Φ }}.
Proof.
  iIntros (Φ) "(#? & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  wp_method_call. wp_call.
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_DeleteOptions__DeepCopy with "[options Hdeepown_options]"). 1: iFrame.
  iIntros (options_ptr1) "[(%options_c1 & Hoptions_ptr1 & Hdeepown_options1)
    (%options_c' & Hoptions_ptr & Hdeepown_options)]". wp_auto.
  iAssert (DeleteOptionsV.deepown_l options_ptr options 1) with "[Hoptions_ptr Hdeepown_options1]"
    as "Hdeepown_l_options1". 1: iFrame.
  iClear "Hoptions_ptr1". clear options_c1.
  wp_apply (wp_map_get with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq.
  destruct (bool_decide (is_Some (phys_state !! key))) eqn:Hdecide.
  2: {
    apply bool_decide_eq_false in Hdecide.
    assert (phys_state !! key = None) as Hlookup_phys_none.
    { destruct (phys_state !! key) as [i|] eqn:Hlookup_phys; [|done]. exfalso. apply Hdecide. done. }
    assert (abs_state !! key = None) as Hlookup_abs.
    { apply not_elem_of_dom. rewrite <- Hdom_eq. apply not_elem_of_dom. done. }
    iApply fupd_wp.
    iMod "Hau" as (uid kmeta parent_key parent_uid children) "H". iNamed "H".
    iPoseProof (kview.own_meta_exists with "Hinv_Hown_abs Hown_meta_frag")
      as "(%obj & %Hlookup_abs' & %Hmeta_eq & %Huid_in)".
    assert (abs_state !! key ≠ None) as Hlookup_abs''.
    { intros Hnone. rewrite Hlookup_abs' in Hnone. done. }
    done.
  }
  assert (∃ i, phys_state !! key = Some i) as [i Hlookup_phys].
  { apply bool_decide_eq_true in Hdecide. done. }
  clear Hdecide.
  assert (∃ kobj, abs_state !! key = Some kobj) as [kobj Hlookup_abs].
  { apply elem_of_dom. rewrite <- Hdom_eq. apply elem_of_dom. eexists. done. }
  iDestruct (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs
    with "Hinv_Hphys_abs_rep") as "[Hdeepown_i Hother_rep]". rewrite Hlookup_phys. wp_auto.
  wp_apply (wp_deepCopy with "[$Hdeepown_i]"). iIntros (i1) "(Hdeepown_i1 & Hdeepown_i)". wp_auto.
  iDestruct "Hdeepown_i1" as (l1) "[%Hvalid_interface Hdeepown_l1]".
  wp_apply wp_Accessor. 1: iPureIntro; done. rewrite bool_decide_true //. wp_auto.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l1") as "(Hdeepown_t_l1 & Hdeepown_m_l1 & Hdeepown_other_l1)".
  wp_alloc err as "Herr". wp_auto.
  wp_apply (wp_validateDeleteOptions with "[$Hdeepown_l_options1]"). 1: done.
  iIntros "Hdeepown_l_options1". wp_auto.
  rewrite bool_decide_true //. wp_auto.
  wp_apply (wp_validateDeletePreconditions with "[$Hdeepown_m_l1 $Hdeepown_l_options1]"). 1: done.
  iIntros (err0) "(%H & Hdeepown_m_l1 & Hdeepown_l_options1)". wp_auto.
  destruct H as [[Hdelete_preconditions_match ->]|[Hdelete_preconditions_not_match Herr0]].
  2: {
    rewrite bool_decide_false //. wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (uid kmeta parent_key parent_uid children) "H". iNamed "H".
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag") as "(<- & %Huid_in)". 1: done.
    iMod ("Hclose" $! err0 (KObjectV.objectmeta kobj) with "[Hown_meta_frag Hown_children_frag]") as "HΦ".
    { iRight. iFrame. iPureIntro. split; done. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)%I)
      with "[Hdeepown_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs). iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply "HΦ".
  }
  rewrite bool_decide_true //. wp_auto.
  wp_apply (wp_checkGracefulDelete with "[Hdeepown_t_l1 Hdeepown_m_l1 Hdeepown_other_l1 $Hdeepown_l_options1]").
  { iSplit; first done. iApply KObjectV.deepown_l_restore. iFrame. }
  iIntros (graceful pendingGraceful options1) "(Hdeepown_l1 & Hdeepown_l_options1 & %Hif_pendinggraceful & %Hgraceful_eq
    & %Hpendinggraceful_eq & %Hoptions_eq)". wp_auto.
  rewrite bool_decide_true //. wp_auto.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l1") as "(Hdeepown_t_l1 & Hdeepown_m_l1 & Hdeepown_other_l1)".
  destruct (bool_decide (valid_finalizers (KObjectV.objectmeta kobj).(ObjectMetaV.Finalizers'))) as [|]
    eqn:Hvalid_kmeta_finalizers.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (uid kmeta parent_key parent_uid children) "H". iNamed "H".
    iPoseProof (kview.own_meta_valid with "Hown_meta_frag") as "%H".
    destruct H as (_ & _ & _ & Hvalid_kmeta).
    unfold ObjectMetaV.valid in Hvalid_kmeta.
    destruct Hvalid_kmeta as
      (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hvalid_finalizers & _).
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag") as "%H". 1: done.
    destruct H as (Hkmeta_eq & _).
    rewrite <- Hkmeta_eq in Hvalid_finalizers.
    apply bool_decide_eq_false in Hvalid_kmeta_finalizers.
    exfalso. apply Hvalid_kmeta_finalizers. done.
  }
  apply bool_decide_eq_true in Hvalid_kmeta_finalizers.
  destruct pendingGraceful as [|]; wp_auto.
  { assert (ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta kobj) ≠ None) as Hdt_not_none.
    { apply Hif_pendinggraceful. done. }
    iApply fupd_wp.
    iMod "Hau" as (uid kmeta parent_key parent_uid children) "H". iNamed "H".
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag") as "(<- & %Huid_in)". 1: done.
    iMod ("Hclose" $! interface.nil (KObjectV.objectmeta kobj) with "[Hown_meta_frag Hown_children_frag]") as "HΦ".
    { iLeft. iFrame. iFrame "%". iSplit. 1: done. iLeft. iFrame. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)%I)
      with "[Hdeepown_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs). iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply "HΦ".
  }
  wp_apply (wp_deletionFinalizersForGarbageCollection with "[$Hdeepown_m_l1 $Hdeepown_l_options1]").
  { iFrame "%". done. }
  iIntros (should_update_finalizers new_finalizers_sl new_finalizers) "(%Hshould_update_finalizers_eq &
    %Hnew_finalizers_eq & %Hvalid_new_finalizers & %Hnew_finalizers_none & Hnew_finalizers_some & Hdeepown_m_l1 &
    Hdeepown_l_options1)". wp_auto.
  destruct should_update_finalizers as [|]; wp_auto.
  2: shelve.
  iDestruct "Hdeepown_m_l1" as "(%mc & Hmc_ptr & Hdeepown_m)".
  wp_apply (wp_SetFinalizers with "[$Hmc_ptr]") as "Hmc_ptr".
  destruct graceful as [|]; wp_auto.
  2: shelve.
  iDestruct "Hdeepown_l_options1" as "(%options_c1 & Hoptions_ptr & Hdeepown_options1)".
  iNamed "Hdeepown_options1". subst options1.
  wp_auto. destruct (delete_new_grace_period_seconds kobj options) as [gps|].
  2: shelve.
  iDestruct "Hdeepown_graceperiodseconds_some" as (cgps) "[Hgps_ptr ->]".
  assert (bool_decide (v1.DeleteOptions.GracePeriodSeconds' options_c1 = null) = false) as ->.
  { apply bool_decide_false; intros Hcontra.
    apply (proj1 Hdeepown_graceperiodseconds_none) in Hcontra. done. }
  wp_auto.
  (* 4, 5, 6:
    assert (bool_decide (v1.DeleteOptions.GracePeriodSeconds' options_c1 = null) = true) as ->
      by (apply bool_decide_true;
          apply (proj2 Hdeepown_graceperiodseconds_none); done); wp_auto. *)
  
  wp_apply (wp_GetFinalizers with "[$Hmc_ptr]") as "Hmc_ptr".
  destruct (bool_decide (slice.len_f new_finalizers_sl = W64 0)) as [|]; wp_auto.
  2: shelve.
  destruct (bool_decide (gps = W64 0)) as [|]; wp_auto.
  { wp_apply (wp_map_delete with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (uid kmeta parent_key parent_uid children) "H". iNamed "H".
    iPoseProof (kview.own_auth_valid2 with "Hinv_Hown_abs") as "%H". 1: done.
    destruct H as (_ & _ & _ & _ & Hunique_id).
    iPoseProof (kview.own_meta_valid with "Hown_meta_frag") as "%H".
    destruct H as (_ & _ & -> & _).
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag") as "(<- & %Huid_in)". 1: done.
    iMod (kview.delete_kobj_vs with "[$Hinv_Hown_abs] [$Hown_meta_frag]") as "Hinv_Hown_abs".
    iMod (cview.delete_child_vs2 key with "[$Hinv_Hown_children] [$Hown_children_frag]")
      as "(Hinv_Hown_children & Hown_children_frag)". 1: done.
    iMod (mono_gset.insert_vs types.UID.t (KObjectV.objectmeta kobj).(ObjectMetaV.UID')
      with "[$Hinv_Hown_tombstone]") as "(Hinv_Hown_tombstone & Hown_tombstone_frag)".
    iMod ("Hclose" $! interface.nil (KObjectV.objectmeta kobj) with "[Hown_children_frag Hown_tombstone_frag]") as "HΦ".
    { iLeft. iFrame "%". iSplit. 1: done. iRight. iFrame. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)%I)
      with "[Hdeepown_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs). iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". iModIntro. iSplitL.
      { iDestruct (big_sepM2_delete _ phys_state abs_state key _ _
          Hlookup_phys Hlookup_abs with "Hinv_Hphys_abs_rep") as "[_ H]". done.
      }
      iPureIntro. split_and!. all: try done.
      apply tombed_uid_delete_eq_used_uid_sub; done.
    }
    iApply "HΦ".
  }
  wp_apply (wp_GetDeletionGracePeriodSeconds with "[$Hmc_ptr]") as "Hmc_ptr".
  destruct (bool_decide (v1.ObjectMeta.DeletionGracePeriodSeconds' mc = null)) as [|]; wp_auto.
  2: shelve.
  wp_apply (wp_SetDeletionGracePeriodSeconds with "[$Hmc_ptr]") as "Hmc_ptr".
  wp_apply (wp_GetDeletionTimestamp with "[$Hmc_ptr]") as "Hmc_ptr".
  destruct (bool_decide (v1.ObjectMeta.DeletionTimestamp' mc = null)) as [|]; wp_auto.
  2: shelve.
  wp_apply (wp_deletionTimestampForDelete). iIntros (timel timec timev) "[Htimel Hdeepown_time]". wp_auto.
  wp_apply (wp_SetDeletionTimestamp with "[$Hmc_ptr]") as "Hmc_ptr".
  wp_apply (wp_GetGeneration with "[$Hmc_ptr]") as "Hmc_ptr".
  destruct (bool_decide ((sint.Z (v1.ObjectMeta.Generation' mc) > sint.Z (W64 0))%Z)) as [|]; wp_auto.
  2: shelve.
  wp_apply (wp_GetGeneration with "[$Hmc_ptr]") as "Hmc_ptr".
  wp_apply (wp_SetGeneration with "[$Hmc_ptr]") as "Hmc_ptr".
  set new_kmetac := mc <| v1.ObjectMeta.Finalizers' := new_finalizers_sl |>
    <| v1.ObjectMeta.DeletionGracePeriodSeconds' := gracePeriod_ptr |>
    <| v1.ObjectMeta.DeletionTimestamp' := timel |>
    <| v1.ObjectMeta.Generation' := word.add (v1.ObjectMeta.Generation' mc) (W64 1) |>.
  set new_kmeta := (KObjectV.objectmeta kobj) <| ObjectMetaV.Finalizers' := new_finalizers |>
    <| ObjectMetaV.DeletionGracePeriodSeconds' := Some gps |>
    <| ObjectMetaV.DeletionTimestamp' := Some timev |>
    <| ObjectMetaV.Generation' := word.add (ObjectMetaV.Generation' (KObjectV.objectmeta kobj)) (W64 1) |>.
  iAssert (ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l1 kobj) new_kmeta 1)
    with "[Hmc_ptr Hdeepown_m gracePeriod Htimel Hdeepown_time Hnew_finalizers_some]" as "Hdeepown_m_l1".
  { iAssert (⌜ timel ≠ null ⌝%I) as "%Hnow_ptr_not_null".
    { iDestruct (typed_pointsto_not_null with "Htimel") as %H; [done|]. done. }
    iAssert (⌜ gracePeriod_ptr ≠ null ⌝%I) as "%HgracePeriod_ptr_not_null".
    { iDestruct (typed_pointsto_not_null with "gracePeriod") as %H; [done|]. done. }
    iExists new_kmetac. iNamed "Hdeepown_m". iFrame. iFrame "%". unfold new_kmetac, new_kmeta.
    rewrite Hdeepown_generation. iSplit; [done|].
    iPureIntro. split_and!. all: done.
  }
  iAssert (KObjectV.deepown_i i1 (KObjectV.update_objectmeta kobj new_kmeta) 1)
    with "[Hdeepown_t_l1 Hdeepown_m_l1 Hdeepown_other_l1]" as "Hdeepown_i1".
  { iPoseProof (KObjectV.deepown_l_merge with "[$Hdeepown_t_l1 $Hdeepown_m_l1 $Hdeepown_other_l1]") as "H".
    iFrame. destruct kobj. all: done. }
  wp_apply (wp_objDeepEqual with "[$Hdeepown_i1 $Hdeepown_i]").
  iIntros (v) "(Hdeepown_i1 & Hdeepown_i & %Hv)".
  destruct v as [|] eqn:Heq; wp_auto.
  { assert (KObjectV.update_objectmeta kobj new_kmeta = kobj) as Hkobj_eq.
    { apply Hv. done. }
    iApply fupd_wp.
    iMod "Hau" as (uid kmeta parent_key parent_uid children) "H". iNamed "H".
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag") as "(<- & %Huid_in)". 1: done.
    iMod ("Hclose" $! interface.nil (KObjectV.objectmeta kobj) with "[Hown_meta_frag Hown_children_frag]") as "HΦ".
    { iLeft. iFrame. iFrame "%". iSplit. 1: done. iLeft. iFrame. iPureIntro. intros Hcontra.
      assert (ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta kobj) = Some timev) as H.
      { rewrite <-Hkobj_eq. destruct kobj; done. }
      rewrite H in Hcontra. done.
    }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)%I)
      with "[Hdeepown_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs). iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply "HΦ".
  }
  wp_apply (wp_State__generateNewRVAndUpdate with "[$Hinv_Hstate_used_rv_addr $Hinv_Hown_used_rv]").
  iIntros (generated_rv) "(%Hgenerated_rv_is_not_used & Hinv_Hstate_used_rv_addr & Hinv_Hown_used_rv)". wp_auto.
  iPoseProof (KObjectV.deepown_i_yields_deepown_l i1 l1 with "[$Hdeepown_i1]") as "Hdeepown_l1".
  { iPureIntro. destruct kobj; done. }
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l1") as "(Hdeepown_t_l1 & Hdeepown_m_l1 & Hdeepown_other_l1)".
  assert (KObjectV.objectmeta_ptr l1 kobj = KObjectV.objectmeta_ptr l1 (KObjectV.update_objectmeta kobj new_kmeta)) as ->.
  { destruct kobj; done. }
  wp_apply (wp_SetResourceVersion_deepown with "[$Hdeepown_m_l1]") as "Hdeepown_m_l1".
  wp_apply (wp_map_insert with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge with "[$Hdeepown_t_l1 $Hdeepown_m_l1 $Hdeepown_other_l1]") as "Hdeepown_l1".
  set new_kmeta1 := new_kmeta <| ObjectMetaV.ResourceVersion' := generated_rv |>.
  assert (KObjectV.update_objectmeta (KObjectV.update_objectmeta kobj new_kmeta)
    (KObjectV.objectmeta (KObjectV.update_objectmeta kobj new_kmeta) <| ObjectMetaV.ResourceVersion' := generated_rv |>)
    = KObjectV.update_objectmeta kobj new_kmeta1  ) as ->.
  { destruct kobj; done. }
  iAssert (KObjectV.deepown_i i1 (KObjectV.update_objectmeta kobj new_kmeta1) 1) with "[Hdeepown_l1]" as "Hdeepown_i1".
  { iFrame. iPureIntro. destruct kobj. all: done. }
  set new_kobj := KObjectV.update_objectmeta kobj new_kmeta1.
  iApply fupd_wp.
  iMod "Hau" as (uid kmeta parent_key parent_uid children) "H". iNamed "H".
  iPoseProof (kview.own_auth_valid2 key kobj with "Hinv_Hown_abs") as "%H". 1: done.
  destruct H as (-> & Hvalid_kobj & Huid_in & Hno_speculative_parent_reference & _).
  iPoseProof (kview.own_meta_valid with "Hown_meta_frag") as "%H".
  destruct H as (_ & _ & -> & _).
  iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag") as "%H". 1: done.
  destruct H as (Hkmeta_eq & _).
  rewrite <-Hkmeta_eq. rewrite <-Hkmeta_eq in Hgeneration_no_overflow.
  iMod (kview.update_meta_kobj_vs kobj new_kobj with "[$Hinv_Hown_abs] [$Hown_meta_frag]")
    as "(Hinv_Hown_abs & Hown_meta_frag)".
  { split_and!. 1, 2: destruct kobj; done.
    destruct Hvalid_kobj as (Hvalid_tm & Hvalid_m & Hvalid_spec & Hvalid_status).
    split_and!. all: unfold new_kobj.
    - destruct kobj; done.
    - assert (ObjectMetaV.valid new_kmeta1) as Hvalid_m1.
      { unfold ObjectMetaV.valid in Hvalid_m.
        decompose [and] Hvalid_m.
        split_and!. all: try done.
        unfold valid_generation, new_kmeta1, new_kmeta. simpl.
        clear -Hgeneration_no_overflow.
        word.
      }
      destruct kobj; done.
    - destruct kobj; done.
    - destruct kobj; done.
  }
  { destruct kobj; done. }
  { done. }
  { destruct kobj; done. }
  { destruct kobj; done. }
  iMod (cview.simple_update_vs (KObjectV.key kobj) kobj new_kobj with "[$Hinv_Hown_children]") as "Hinv_Hown_children".
  { done. }
  { destruct kobj; done. }
  { destruct kobj; done. }
  iMod ("Hclose" $! interface.nil (KObjectV.objectmeta new_kobj) with "[Hown_meta_frag Hown_children_frag]") as "HΦ".
  { iLeft. iFrame. iFrame "%". iSplit. 1: done. iLeft. iFrame. iPureIntro.
    destruct kobj; done.
  }
  iModIntro.
  iAssert (([∗ map] i; obj ∈ <[KObjectV.key kobj:=i1]> phys_state; <[KObjectV.key kobj:=new_kobj]> abs_state,
    KObjectV.deepown_i i obj 1)%I) with "[Hdeepown_i1 Hother_rep]" as "Hinv_Hphys_abs_rep".
  { rewrite big_sepM2_insert_delete. iFrame. }
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H".
    iFrame "#". iFrame. iPureIntro. split_and!.
    all: try done.
    eapply tombed_uid_update_eq_used_uid_sub; [done|done|].
    destruct kobj; done.
  }
  iApply "HΦ".
Admitted.

Lemma wp_State__delete γ l key options_c options uid kmeta parent_key parent_uid children :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options 1 ∗
      "%Hvalid_options" ∷ ⌜ DeleteOptionsV.valid options ⌝ ∗
      "%Hkey_in" ∷ ⌜ key ∈ children ⌝ ∗
      "%Hgeneration_no_overflow" ∷ ⌜ 0 ≤ sint.Z kmeta.(ObjectMetaV.Generation') + 1 < 2^63 ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "delete" #key #options_c
  {{{ err kmeta', RET #err;
      ( ⌜ delete_preconditions_match kmeta options ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ( ⌜ kmeta'.(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
          own_meta_frag γ key uid 1 kmeta' ∗
          own_children_frag γ parent_key parent_uid 1 children
          ∨
          own_tombstone_frag γ uid ∗
          own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]})
        )
      ∨
        ⌜ ¬ delete_preconditions_match kmeta options ⌝ ∗
        ⌜ err ≠ interface.nil ⌝ ∗
        own_meta_frag γ key uid 1 kmeta ∗
        own_children_frag γ parent_key parent_uid 1 children
      )
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__delete_au.
  iFrame "#". iFrame "%". iFrame.
  iApply fupd_mask_intro; [set_solver|iIntros "Hmask"].
  iIntros (err kmeta') "Hpost".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! err kmeta' with "Hpost").
Qed.

Lemma wp_State__delete_success γ l key options_c options uid kmeta parent_key parent_uid children :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options 1 ∗
      "%Hvalid_options" ∷ ⌜ DeleteOptionsV.valid options ⌝ ∗
      "%Hkey_in" ∷ ⌜ key ∈ children ⌝ ∗
      "%Hgeneration_no_overflow" ∷ ⌜ 0 ≤ sint.Z kmeta.(ObjectMetaV.Generation') + 1 < 2^63 ⌝ ∗
      "%Hdelete_preconditions" ∷ ⌜ delete_preconditions_match kmeta options ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "delete" #key #options_c
  {{{ kmeta', RET #interface.nil;
      ( ⌜ kmeta'.(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
        own_meta_frag γ key uid 1 kmeta' ∗
        own_children_frag γ parent_key parent_uid 1 children
        ∨
        own_tombstone_frag γ uid ∗
        own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]})
      )
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_apply (wp_State__delete with "[$Hdeepown_options $Hown_meta_frag $Hown_children_frag]").
  { iFrame "#". iFrame "%". }
  iIntros (err kmeta') "Hpost".
  iDestruct "Hpost" as "[Hsuccess|Hfailure]".
  - iDestruct "Hsuccess" as "(%_ & %Herr & Hpost)".
    subst err.
    iApply ("HΦ" $! kmeta' with "Hpost").
  - iDestruct "Hfailure" as "(%Hnot_delete_preconditions & _)".
    exfalso. apply Hnot_delete_preconditions. done.
Qed.

End proof.
