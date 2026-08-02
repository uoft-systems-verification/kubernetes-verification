From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_delete.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(* TODO: specifies in which case the object is deleted from the state map *)
Lemma wp_State__delete_au γ l key options_c options:
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options 1 ∗
    "%Hvalid_options" ∷ ⌜ DeleteOptionsV.valid options ⌝ ∗
    ( |={⊤,∅}=> ∃ uid kmeta parent_key parent_uid children,
      "%Hkey_in" ∷ ⌜ key ∈ children ⌝ ∗
      "%Hdelete_preconditions_uid" ∷ ⌜ delete_preconditions_match_uid options uid ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hclose" ∷ (
        if decide (delete_options_preconditions_resource_version_none options) then
          ∀ kmeta',
            delete_success_post γ key uid parent_key parent_uid children kmeta'
              ={∅,⊤}=∗ ▷ Φ #interface.nil
        else
          ∀ err kmeta',
            ( ( ⌜ err = interface.nil ⌝ ∗
                delete_success_post γ key uid parent_key parent_uid children kmeta') ∨
              ( ⌜ err ≠ interface.nil ⌝ ∗
                ⌜ conflict_error err ⌝ ∗
                own_meta_frag γ key uid 1 kmeta ∗
                own_children_frag γ parent_key parent_uid 1 children)
            )
              ={∅,⊤}=∗ ▷ Φ #err
      )%I
    ) -∗ WP l @! (go.PointerType apimodel.State) @! "delete" #key #options_c {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  wp_method_call. rewrite /apimodel.State__deleteⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_DeleteOptions__DeepCopy with "[options Hdeepown_options]"). 1: iFrame.
  iIntros (options_ptr1) "[Hdeepown_l_options1 Hdeepown_l_options]".
  iDestruct "Hdeepown_l_options1" as (options_c1) "[Hoptions_ptr1 Hdeepown_options1]".
  iDestruct "Hdeepown_l_options" as (options_c0) "[Hoptions_ptr Hdeepown_options]".
  wp_auto.
  iAssert (DeleteOptionsV.deepown_l options_ptr options 1) with "[Hoptions_ptr Hdeepown_options1]"
    as "Hdeepown_l_options1".
  { iExists options_c1. iFrame. }
  iClear "Hdeepown_options". clear options_c0 options_c1.
  wp_apply (wp_map_lookup2 apimodel.KKey (go.InterfaceType []) with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
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
      as "(%obj & %Hlookup_abs' & %Huid_obj & %Hmeta_eq & %Huid_in)".
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
  destruct i as [i|].
  2: { iExFalso. iExact "Hdeepown_i". }
  wp_apply (wp_deepCopy i kobj with "[Hdeepown_i]").
  { iFrame "#". iExact "Hdeepown_i". }
  iIntros (i1) "(Hdeepown_i1 & Hdeepown_i)". wp_auto.
  iDestruct "Hdeepown_i1" as (l1) "[%Hvalid_interface Hdeepown_l1]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l1") as
    "(%Hl1_not_null & Hdeepown_t_l1 & Hdeepown_m_l1 & Hdeepown_s_l1 & Hdeepown_st_l1)".
  wp_alloc err as "Herr". wp_auto.
  wp_apply (wp_validateDeleteOptions with "[$Hdeepown_l_options1]"). 1: done.
  iIntros "Hdeepown_l_options1". wp_auto.
  wp_apply (wp_validateDeletePreconditions with "[$Hdeepown_m_l1 $Hdeepown_l_options1]"). 1: done.
  iIntros (err0) "(%Hpreconditions & Hdeepown_m_l1 & Hdeepown_l_options1)". wp_auto.
  destruct Hpreconditions as [[Hdelete_preconditions_match ->]|
    [Hdelete_preconditions_not_match [Herr0 Hconflict_err0]]].
  2: {
    destruct err0 as [err0|].
    2: { exfalso. apply Herr0. done. }
    wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (uid kmeta parent_key parent_uid children) "H". iNamed "H".
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    destruct (decide (delete_options_preconditions_resource_version_none options)) as [Hrv_none|Hrv_some].
    { exfalso. apply Hdelete_preconditions_not_match.
      eapply delete_preconditions_match_of_uid_rv_none; done. }
    iMod ("Hclose" $! (interface.ok err0) (KObjectV.objectmeta kobj) with "[Hown_meta_frag Hown_children_frag]") as "HΦ".
    { iRight. iSplit; first done. iSplit; first done. iFrame. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I)
      with "[Hdeepown_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs). iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply "HΦ".
  }
  wp_auto.
  wp_apply (wp_checkGracefulDelete with "[Hdeepown_t_l1 Hdeepown_m_l1 Hdeepown_s_l1 Hdeepown_st_l1 $Hdeepown_l_options1]").
  { iSplit; first done. iApply (KObjectV.deepown_l_restore _ _ _ Hl1_not_null). iFrame. }
  iIntros (graceful pendingGraceful options1) "(Hdeepown_l1 & Hdeepown_l_options1 & %Hif_pendinggraceful & %Hgraceful_eq
    & %Hpendinggraceful_eq & %Hoptions_eq)". wp_auto.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l1") as
    "(%Hl1_not_null1 & Hdeepown_t_l1 & Hdeepown_m_l1 & Hdeepown_s_l1 & Hdeepown_st_l1)".
  destruct (bool_decide (valid_finalizers (KObjectV.objectmeta kobj).(ObjectMetaV.Finalizers'))) as [|]
    eqn:Hvalid_kmeta_finalizers.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (uid kmeta parent_key parent_uid children) "H". iNamed "H".
    iPoseProof (kview.own_meta_valid with "Hown_meta_frag") as "%Hmeta_valid_full".
    destruct Hmeta_valid_full as (_ & _ & _ & Hvalid_kmeta).
    pose proof (ObjectMetaV.valid_finalizers_of_valid _ Hvalid_kmeta) as Hvalid_finalizers.
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag") as "%Hmeta_exists".
    1: done.
    destruct Hmeta_exists as (_ & Hmeta_eq & _).
    rewrite <-(ObjectMetaV.equiv_except_resource_version_finalizers _ _ Hmeta_eq) in Hvalid_finalizers.
    apply bool_decide_eq_false in Hvalid_kmeta_finalizers.
    exfalso. apply Hvalid_kmeta_finalizers. done.
  }
  apply bool_decide_eq_true in Hvalid_kmeta_finalizers.
  destruct pendingGraceful as [|]; wp_auto.
  { assert (ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta kobj) ≠ None) as Hdt_not_none.
    { apply Hif_pendinggraceful. done. }
    iApply fupd_wp.
    iMod "Hau" as (uid kmeta parent_key parent_uid children) "H". iNamed "H".
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (own_meta_frag_equiv_except_resource_version Hmeta_eq with "Hown_meta_frag")
      as "Hown_meta_frag".
    iAssert (|={∅,⊤}=> ▷ Φ #interface.nil)%I
      with "[Hclose Hown_meta_frag Hown_children_frag]" as "HΦ_fupd".
    { destruct (decide (delete_options_preconditions_resource_version_none options)) as [_|_].
      - iApply ("Hclose" $! (KObjectV.objectmeta kobj)). iLeft. iFrame. iPureIntro. done.
      - iApply ("Hclose" $! interface.nil (KObjectV.objectmeta kobj)).
        iLeft. iSplit; first done. iLeft. iFrame. iPureIntro. done.
    }
    iMod "HΦ_fupd" as "HΦ".
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I)
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
  iDestruct "Hdeepown_m_l1" as "(%mc0 & Hmc_ptr & Hdeepown_m)".
  wp_if_join (λ v, ⌜ v = execute_val ⌝ ∗
    ∃ current_kmeta mc,
    "metadata" ∷ metadata_ptr ↦
      interface.mk_ok (go.PointerType v1.ObjectMeta) #(KObjectV.objectmeta_ptr l1 kobj) ∗
    "newFinalizers" ∷ newFinalizers_ptr ↦ new_finalizers_sl ∗
    "Hmc_ptr" ∷ KObjectV.objectmeta_ptr l1 kobj ↦ mc ∗
    "Hdeepown_m" ∷ ObjectMetaV.deepown mc current_kmeta 1 ∗
    "%Hcurrent_kmeta_eq" ∷ ⌜ current_kmeta =
      (KObjectV.objectmeta kobj) <| ObjectMetaV.Finalizers' :=
        current_kmeta.(ObjectMetaV.Finalizers') |> ⌝ ∗
    "%Hvalid_current_finalizers" ∷ ⌜ valid_finalizers current_kmeta.(ObjectMetaV.Finalizers') ⌝)%I
    with "[metadata newFinalizers Hmc_ptr Hdeepown_m Hnew_finalizers_some]".
  { wp_apply (wp_SetFinalizers with "[$Hmc_ptr]") as "Hmc_ptr".
    iSplit; first done.
    iExists ((KObjectV.objectmeta kobj) <| ObjectMetaV.Finalizers' := new_finalizers |>),
      (mc0 <| v1.ObjectMeta.Finalizers' := new_finalizers_sl |>).
    iFrame "metadata newFinalizers Hmc_ptr".
    iSplitL "Hdeepown_m Hnew_finalizers_some".
    - iNamed "Hdeepown_m". iFrame. iFrame "%".
    - iPureIntro. split; done.
  }
  { iSplit; first done.
    iExists (KObjectV.objectmeta kobj), mc0.
    iFrame. iPureIntro. split; first by destruct (KObjectV.objectmeta kobj); done.
    done.
  }
  iIntros (?) "H". iDestruct "H" as "(-> & H)". iNamed "H". wp_auto.
  iDestruct "Hdeepown_l_options1" as "(%options_c1 & Hoptions_ptr & Hdeepown_options1)".
  iNamed "Hdeepown_options1". subst options1.
  wp_if_join (λ v, ∃ (graceful_val do_graceful : bool),
    "->" ∷ ⌜ v = #do_graceful ⌝ ∗
    "graceful" ∷ graceful_ptr ↦ graceful_val ∗
    "Hoptions_ptr" ∷ options_ptr ↦ options_c1 ∗
    "gracePeriod" ∷ gracePeriod_ptr ↦ W64 0 ∗
    "Hdo_graceful" ∷ (if do_graceful then
      ∃ (gps : w64), "Hgps_ptr" ∷ v1.DeleteOptions.GracePeriodSeconds' options_c1 ↦ gps
    else True))%I
    with "[graceful Hoptions_ptr gracePeriod Hdeepown_graceperiodseconds_some]".
  { destruct (delete_new_grace_period_seconds kobj options) as [gps|] eqn:Hgps.
    - iDestruct "Hdeepown_graceperiodseconds_some" as (cgps) "[Hgps_ptr ->]".
      assert (bool_decide (v1.DeleteOptions.GracePeriodSeconds' options_c1 = null) = false) as ->.
      { apply bool_decide_false; intros Hcontra.
        apply (proj1 Hdeepown_graceperiodseconds_none) in Hcontra. done. }
      iExists true, true. iSplit; first done.
      iFrame "graceful Hoptions_ptr gracePeriod". iExists gps. iFrame.
    - assert (bool_decide (v1.DeleteOptions.GracePeriodSeconds' options_c1 = null) = true) as ->.
      { apply bool_decide_true. apply (proj2 Hdeepown_graceperiodseconds_none). done. }
      iExists true, false. iSplit; first done. iFrame "graceful Hoptions_ptr gracePeriod".
  }
  { iExists false, false. iSplit; first done. iFrame "graceful Hoptions_ptr gracePeriod". }
  iIntros (?) "H". iNamed "H".
  wp_if_join (λ v, "->" ∷ ⌜ v = execute_val ⌝ ∗
    ∃ gps graceful_val,
    "graceful" ∷ graceful_ptr ↦ graceful_val ∗
    "gracePeriod" ∷ gracePeriod_ptr ↦ gps)%I
    with "[graceful Hoptions_ptr gracePeriod Hdo_graceful]".
  { iDestruct "Hdo_graceful" as (gps) "Hgps_ptr".
    wp_auto. iSplit; first done. iExists gps, graceful_val. iFrame.
  }
  { iSplit; first done. iExists (W64 0), graceful_val. iFrame. }
  iIntros (?) "H". iDestruct "H" as "(-> & %gps & %graceful_val1 & H)". iNamed "H". wp_auto.
  wp_apply (wp_GetFinalizers with "[$Hmc_ptr]") as "Hmc_ptr".
  wp_if_join (λ v, ∃ (should_delete : bool),
    "->" ∷ ⌜ v = #should_delete ⌝ ∗
    "Hmc_ptr" ∷ KObjectV.objectmeta_ptr l1 kobj ↦ mc ∗
    "graceful" ∷ graceful_ptr ↦ graceful_val1 ∗
    "gracePeriod" ∷ gracePeriod_ptr ↦ gps)%I
    with "[Hmc_ptr graceful gracePeriod]".
  { destruct (bool_decide (gps = W64 0)) as [|].
    - iExists true. iSplit; first done. iFrame.
    - iExists false. iSplit; first done. iFrame.
  }
  { iExists false. iSplit; first done. iFrame. }
  iIntros (?) "H". iNamed "H".
  destruct should_delete; wp_auto.
  { wp_apply (wp_map_delete _ _ key apimodel.KKey (go.InterfaceType []) with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (uid kmeta parent_key parent_uid children) "H". iNamed "H".
    iPoseProof (kview.own_auth_valid2 with "Hinv_Hown_abs")
      as "%Hauth_valid_delete". 1: done.
    destruct Hauth_valid_delete as (_ & _ & _ & _ & Hunique_id).
    iPoseProof (kview.own_meta_valid with "Hown_meta_frag") as "%Hmeta_valid_delete".
    destruct Hmeta_valid_delete as (_ & _ & -> & _).
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iMod (kview.delete_kobj_vs with "[$Hinv_Hown_abs] [$Hown_meta_frag]") as "Hinv_Hown_abs".
    iMod (cview.delete_child_vs2 key with "[$Hinv_Hown_children] [$Hown_children_frag]")
      as "(Hinv_Hown_children & Hown_children_frag)". 1: done.
    iMod (tombstone.insert_vs (KObjectV.objectmeta kobj).(ObjectMetaV.UID')
      with "[$Hinv_Hown_tombstone]") as "(Hinv_Hown_tombstone & Hown_tombstone_frag)".
    rewrite Huid_obj.
    iAssert (|={∅,⊤}=> ▷ Φ #interface.nil)%I
      with "[Hclose Hown_children_frag Hown_tombstone_frag]" as "HΦ_fupd".
    { destruct (decide (delete_options_preconditions_resource_version_none options)) as [_|_].
      - iApply ("Hclose" $! (KObjectV.objectmeta kobj)). iRight. iFrame.
      - iApply ("Hclose" $! interface.nil (KObjectV.objectmeta kobj)).
        iLeft. iSplit; first done. iRight. iFrame.
    }
    iMod "HΦ_fupd" as "HΦ".
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I)
      with "[Hdeepown_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs). iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". iModIntro. iSplitL.
      { iDestruct (big_sepM2_delete _ phys_state abs_state key _ _
          Hlookup_phys Hlookup_abs with "Hinv_Hphys_abs_rep") as "[_ H]". done.
      }
      iPureIntro. split_and!. all: try done.
      - rewrite <-Huid_obj.
        eapply tombed_uid_delete_eq_used_uid_sub; [done|done| |done].
        rewrite Huid_obj. exact Huid_in.
      - rewrite dom_delete_L.
        Timeout 10 set_solver.
    }
    iApply "HΦ".
  }
  iEval (rewrite /ObjectMetaV.deepown) in "Hdeepown_m".
  iNamedPrefix "Hdeepown_m" "Hmeta_".
  wp_apply (wp_GetDeletionGracePeriodSeconds with "[$Hmc_ptr]") as "Hmc_ptr".
  wp_if_join (λ v, ∃ (should_set_grace_period : bool),
    "->" ∷ ⌜ v = #should_set_grace_period ⌝ ∗
    "Hmc_ptr" ∷ KObjectV.objectmeta_ptr l1 kobj ↦ mc ∗
    "graceful" ∷ graceful_ptr ↦ graceful_val1 ∗
    "gracePeriod" ∷ gracePeriod_ptr ↦ gps ∗
    "Hcurrent_dgps" ∷ (if should_set_grace_period then True
      else v1.ObjectMeta.DeletionGracePeriodSeconds' mc ↦ gps))%I
    with "[Hmc_ptr graceful gracePeriod currentGracePeriod Hmeta_Hdeepown_deletiongraceperiodseconds_some]".
  { iExists true. iSplit; first done. iFrame. }
  { destruct current_kmeta.(ObjectMetaV.DeletionGracePeriodSeconds') as [old_gps|] eqn:Hcurrent_dgps.
    - iDestruct "Hmeta_Hdeepown_deletiongraceperiodseconds_some" as (old_cgps) "[Hold_cgps ->]".
      destruct (bool_decide (old_gps = gps)) as [|] eqn:Hold_gps_eq.
      + apply bool_decide_eq_true in Hold_gps_eq. subst old_gps.
        wp_auto.
        iExists false. iSplit.
        { iPureIntro. rewrite bool_decide_true; done. }
        iFrame.
      + wp_auto. iExists true. iSplit.
        { iPureIntro. rewrite Hold_gps_eq. done. }
        iFrame.
    - exfalso.
      match goal with
      | H : v1.ObjectMeta.DeletionGracePeriodSeconds' mc ≠ null |- _ =>
          apply H; apply (proj2 Hmeta_Hdeepown_deletiongraceperiodseconds_none); done
      end.
  }
  iIntros (?) "H". iNamed "H". wp_auto.
  wp_if_join (λ v, "->" ∷ ⌜ v = execute_val ⌝ ∗
    ∃ dgps_ptr,
      "metadata" ∷ metadata_ptr ↦
        interface.mk_ok (go.PointerType v1.ObjectMeta) #(KObjectV.objectmeta_ptr l1 kobj) ∗
      "Hmc_ptr" ∷ KObjectV.objectmeta_ptr l1 kobj ↦
        (mc <| v1.ObjectMeta.DeletionGracePeriodSeconds' := dgps_ptr |>) ∗
      "graceful" ∷ graceful_ptr ↦ graceful_val1 ∗
      "gracePeriod" ∷ gracePeriod_ptr ↦ gps ∗
      "Hdgps" ∷ (⌜ dgps_ptr = gracePeriod_ptr ⌝ ∨ dgps_ptr ↦ gps))%I
    with "[metadata Hmc_ptr graceful gracePeriod Hcurrent_dgps]".
  {
    wp_apply (wp_SetDeletionGracePeriodSeconds with "[$Hmc_ptr]") as "Hmc_ptr".
    iSplit; first done. iExists gracePeriod_ptr. iFrame. iLeft. done.
  }
  { iSplit; first done.
    iExists (v1.ObjectMeta.DeletionGracePeriodSeconds' mc).
    replace (mc <| v1.ObjectMeta.DeletionGracePeriodSeconds' :=
      v1.ObjectMeta.DeletionGracePeriodSeconds' mc |>) with mc.
    2: { destruct mc; done. }
    iFrame.
  }
  iIntros (?) "H". iDestruct "H" as "(-> & %dgps_ptr & H)". iNamed "H".
  set mc_dgps := mc <| v1.ObjectMeta.DeletionGracePeriodSeconds' := dgps_ptr |>.
  iEval (change (mc <| v1.ObjectMeta.DeletionGracePeriodSeconds' := dgps_ptr |>) with mc_dgps) in "Hmc_ptr".
  wp_auto.
  wp_apply (wp_GetDeletionTimestamp (KObjectV.objectmeta_ptr l1 kobj) mc_dgps (DfracOwn 1) with "[$Hmc_ptr]") as "Hmc_ptr".
  change (v1.ObjectMeta.DeletionTimestamp' mc_dgps) with (v1.ObjectMeta.DeletionTimestamp' mc).
  wp_if_join (λ v, "->" ∷ ⌜ v = execute_val ⌝ ∗
    ∃ dt_ptr dt_c dt_v gen,
      "metadata" ∷ metadata_ptr ↦
        interface.mk_ok (go.PointerType v1.ObjectMeta) #(KObjectV.objectmeta_ptr l1 kobj) ∗
      "gracePeriod" ∷ gracePeriod_ptr ↦ gps ∗
      "Hmc_ptr" ∷ KObjectV.objectmeta_ptr l1 kobj ↦
        (mc_dgps <| v1.ObjectMeta.DeletionTimestamp' := dt_ptr |>
          <| v1.ObjectMeta.Generation' := gen |>) ∗
      "Hdt_ptr" ∷ dt_ptr ↦ dt_c ∗
      "Hdeepown_time" ∷ TimeV.deepown dt_c dt_v 1)%I
    with "[metadata Hmc_ptr graceful gracePeriod Hmeta_Hdeepown_deletiontimestamp_some]".
  { wp_apply (wp_deletionTimestampForDelete). iIntros (timel timec timev) "[Htimel Hdeepown_time]". wp_auto.
    wp_apply (wp_SetDeletionTimestamp with "[$Hmc_ptr]") as "Hmc_ptr".
    set mc_dt := mc_dgps <| v1.ObjectMeta.DeletionTimestamp' := timel |>.
    iEval (change (mc_dgps <| v1.ObjectMeta.DeletionTimestamp' := timel |>) with mc_dt) in "Hmc_ptr".
    wp_apply (wp_GetGeneration (KObjectV.objectmeta_ptr l1 kobj) mc_dt (DfracOwn 1) with "[$Hmc_ptr]") as "Hmc_ptr".
    change (v1.ObjectMeta.Generation' mc_dt) with (v1.ObjectMeta.Generation' mc).
    wp_if_join (λ v, "->" ∷ ⌜ v = execute_val ⌝ ∗
      ∃ gen,
        "metadata" ∷ metadata_ptr ↦
          interface.mk_ok (go.PointerType v1.ObjectMeta) #(KObjectV.objectmeta_ptr l1 kobj) ∗
        "Hmc_ptr" ∷ KObjectV.objectmeta_ptr l1 kobj ↦
        (mc_dt <| v1.ObjectMeta.Generation' := gen |>) )%I
      with "[metadata Hmc_ptr]".
    { wp_bind ((KObjectV.objectmeta_ptr l1 kobj) @! (go.PointerType v1.ObjectMeta) @! "GetGeneration" #())%E.
      wp_apply (wp_GetGeneration (KObjectV.objectmeta_ptr l1 kobj) mc_dt (DfracOwn 1) with "[$Hmc_ptr]") as "Hmc_ptr".
      change (v1.ObjectMeta.Generation' mc_dt) with (v1.ObjectMeta.Generation' mc).
      wp_apply (wp_SetGeneration with "[$Hmc_ptr]") as "Hmc_ptr".
      iSplit; first done. iExists (word.add (v1.ObjectMeta.Generation' mc) (W64 1)). iFrame.
    }
    { iSplit; first done. iExists (v1.ObjectMeta.Generation' mc).
      replace (mc_dt <| v1.ObjectMeta.Generation' := v1.ObjectMeta.Generation' mc |>)
        with mc_dt by (unfold mc_dt, mc_dgps; destruct mc; done).
      iFrame.
    }
    iIntros (?) "H". iDestruct "H" as "(-> & %gen & H)". iNamed "H".
    iSplit; first done. iExists timel, timec, timev, gen. iFrame.
  }
  { destruct current_kmeta.(ObjectMetaV.DeletionTimestamp') as [old_timev|] eqn:Hcurrent_dt.
    - iDestruct "Hmeta_Hdeepown_deletiontimestamp_some" as (old_timec) "[Hdt_ptr Hdeepown_time]".
      iSplit; first done.
      iExists (v1.ObjectMeta.DeletionTimestamp' mc), old_timec, old_timev, (v1.ObjectMeta.Generation' mc).
      replace (mc_dgps <| v1.ObjectMeta.DeletionTimestamp' := v1.ObjectMeta.DeletionTimestamp' mc |>
        <| v1.ObjectMeta.Generation' := v1.ObjectMeta.Generation' mc |>) with mc_dgps
        by (unfold mc_dgps; destruct mc; done).
      iFrame.
    - exfalso.
      match goal with
      | H : v1.ObjectMeta.DeletionTimestamp' mc ≠ null |- _ =>
          apply H; apply (proj2 Hmeta_Hdeepown_deletiontimestamp_none); done
      end.
  }
  iIntros (?) "H". iDestruct "H" as "(-> & %dt_ptr & %dt_c & %dt_v & %gen & H)". iNamed "H".
  set new_kmetac := mc <| v1.ObjectMeta.DeletionGracePeriodSeconds' := dgps_ptr |>
    <| v1.ObjectMeta.DeletionTimestamp' := dt_ptr |>
    <| v1.ObjectMeta.Generation' := gen |>.
  set new_kmeta := current_kmeta <| ObjectMetaV.DeletionGracePeriodSeconds' := Some gps |>
    <| ObjectMetaV.DeletionTimestamp' := Some dt_v |>
    <| ObjectMetaV.Generation' := gen |>.
  iCombineNamed "Hmeta_Hdeepown_*" as "Hmeta_deepown".
  iAssert (ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l1 kobj) new_kmeta 1)
    with "[Hmc_ptr Hdgps gracePeriod Hdt_ptr Hdeepown_time Hmeta_deepown]" as "Hdeepown_m_l1".
  { iNamed "Hmeta_deepown".
    iAssert (⌜ dt_ptr ≠ null ⌝%I) as "%Hnow_ptr_not_null".
    { iDestruct (typed_pointsto_not_null with "Hdt_ptr") as %Hdt_ptr_not_null. done. }
    iDestruct "Hdgps" as "[%Hdgps_eq|Hnew_dgps]".
    - subst dgps_ptr. iRename "gracePeriod" into "Hnew_dgps".
      iAssert (⌜ gracePeriod_ptr ≠ null ⌝%I) as "%Hdgps_ptr_not_null".
      { iDestruct (typed_pointsto_not_null with "Hnew_dgps") as %Hdgps_not_null. done. }
      iExists new_kmetac.
      unfold new_kmetac, new_kmeta.
      iFrame. iFrame "%". iSplit; [done|].
      iPureIntro. split_and!. all: done.
    - iClear "gracePeriod".
      iAssert (⌜ dgps_ptr ≠ null ⌝%I) as "%Hdgps_ptr_not_null".
      { iDestruct (typed_pointsto_not_null with "Hnew_dgps") as %Hdgps_not_null. done. }
      iExists new_kmetac.
      unfold new_kmetac, new_kmeta.
      iFrame. iFrame "%". iSplit; [done|].
      iPureIntro. split_and!. all: done.
  }
  iAssert (KObjectV.deepown_i i1 (KObjectV.update_objectmeta kobj new_kmeta) 1)
    with "[Hdeepown_t_l1 Hdeepown_m_l1 Hdeepown_s_l1 Hdeepown_st_l1]" as "Hdeepown_i1".
  { iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null1 with "[$Hdeepown_t_l1 $Hdeepown_m_l1 $Hdeepown_s_l1 $Hdeepown_st_l1]") as "Hdeepown_l1_new".
    iFrame. destruct kobj. all: done. }
  wp_auto.
  wp_apply (wp_storageObjectDeepEqual with "[$Hdeepown_i1 $Hdeepown_i]").
  iIntros (v) "(Hdeepown_i1 & Hdeepown_i & %Hv)".
  destruct v as [|] eqn:Heq; wp_auto.
  { assert (storage_object_normalize (KObjectV.update_objectmeta kobj new_kmeta) =
      storage_object_normalize kobj) as Hstorage_eq.
    { apply Hv. done. }
    iApply fupd_wp.
    iMod "Hau" as (uid kmeta parent_key parent_uid children) "H". iNamed "H".
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (own_meta_frag_equiv_except_resource_version Hmeta_eq with "Hown_meta_frag")
      as "Hown_meta_frag".
    iAssert (|={∅,⊤}=> ▷ Φ #interface.nil)%I
      with "[Hclose Hown_meta_frag Hown_children_frag]" as "HΦ_fupd".
    { destruct (decide (delete_options_preconditions_resource_version_none options)) as [_|_].
      - iApply ("Hclose" $! (KObjectV.objectmeta kobj)).
        iLeft. iFrame. iPureIntro. intros Hcontra.
        assert (ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta kobj) = Some dt_v) as Hdeletion_timestamp_eq.
        { pose proof (storage_object_normalize_update_objectmeta_deletionTimestamp _ _ Hstorage_eq) as Hdt.
          unfold new_kmeta in Hdt. simpl in Hdt. symmetry. exact Hdt. }
        rewrite Hdeletion_timestamp_eq in Hcontra. done.
      - iApply ("Hclose" $! interface.nil (KObjectV.objectmeta kobj)).
        iLeft. iSplit; first done. iLeft. iFrame. iPureIntro. intros Hcontra.
        assert (ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta kobj) = Some dt_v) as Hdeletion_timestamp_eq.
        { pose proof (storage_object_normalize_update_objectmeta_deletionTimestamp _ _ Hstorage_eq) as Hdt.
          unfold new_kmeta in Hdt. simpl in Hdt. symmetry. exact Hdt. }
        rewrite Hdeletion_timestamp_eq in Hcontra. done.
    }
    iMod "HΦ_fupd" as "HΦ".
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I)
      with "[Hdeepown_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs). iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply "HΦ".
  }
  wp_apply (wp_State__generateNewRVAndUpdate with "[$Hinv_Hstate_used_rv_addr $Hinv_Hown_used_rv]").
  iIntros (generated_rv) "(%Hgenerated_rv_is_not_used & %Hgenerated_rv_valid & Hinv_Hstate_used_rv_addr & Hinv_Hown_used_rv)".
  wp_auto.
  iPoseProof (KObjectV.deepown_i_yields_deepown_l i1 l1 with "[$Hdeepown_i1]") as "Hdeepown_l1".
  { iPureIntro. destruct kobj; done. }
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l1") as
    "(%Hl1_not_null2 & Hdeepown_t_l1 & Hdeepown_m_l1 & Hdeepown_s_l1 & Hdeepown_st_l1)".
  assert (KObjectV.objectmeta_ptr l1 kobj = KObjectV.objectmeta_ptr l1 (KObjectV.update_objectmeta kobj new_kmeta)) as ->.
  { destruct kobj; done. }
  wp_apply (wp_SetResourceVersion_deepown with "[$Hdeepown_m_l1]") as "Hdeepown_m_l1".
  wp_apply (wp_map_insert apimodel.KKey with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null2 with "[$Hdeepown_t_l1 $Hdeepown_m_l1 $Hdeepown_s_l1 $Hdeepown_st_l1]") as "Hdeepown_l1".
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
  iPoseProof (kview.own_auth_valid2 key kobj with
    "Hinv_Hown_abs") as "%Hauth_valid_update". 1: done.
  destruct Hauth_valid_update as
    (-> & Hvalid_kobj & Huid_in &
      Hno_speculative_parent_reference & _).
  iPoseProof (kview.own_meta_valid with "Hown_meta_frag") as "%Hmeta_valid_update".
  destruct Hmeta_valid_update as (_ & _ & -> & _).
  iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag") as "%Hmeta_exists_update". 1: done.
  destruct Hmeta_exists_update as (Huid_obj & Hmeta_eq & _).
  iMod (kview.update_meta_kobj_vs kobj new_kobj with "[$Hinv_Hown_abs] [$Hown_meta_frag]")
    as "(Hinv_Hown_abs & Hown_meta_frag)".
  { split_and!.
    - unfold new_kobj, new_kmeta1, new_kmeta.
      rewrite /KObjectV.key KObjectV.kind_update_objectmeta objectmeta_update_objectmeta.
      rewrite Hcurrent_kmeta_eq. destruct kobj; done.
    - unfold new_kobj, new_kmeta1, new_kmeta. rewrite Hcurrent_kmeta_eq.
      destruct kobj; simpl in *; symmetry; exact Huid_obj.
    - destruct Hvalid_kobj as
        (Hvalid_tm & _ & Hvalid_m & Hvalid_spec & Hvalid_status).
      split_and!. all: unfold new_kobj.
      + destruct kobj; done.
      + destruct kobj; simpl; exact Hgenerated_rv_valid.
      + assert (ObjectMetaV.valid (KObjectV.kind kobj) new_kmeta1)
          as Hvalid_m1.
        { unfold ObjectMetaV.valid in Hvalid_m.
          decompose [and] Hvalid_m.
          unfold new_kmeta1, new_kmeta. rewrite Hcurrent_kmeta_eq.
          split_and!. all: try done.
        }
        destruct kobj; done.
      + destruct kobj; done.
      + destruct kobj; done.
  }
  { unfold new_kobj, new_kmeta1, new_kmeta.
    rewrite objectmeta_update_objectmeta Hcurrent_kmeta_eq.
    unfold no_speculative_parent_reference in *.
    intros kind name uid0 Hparent.
    rewrite /meta_parent_ref_is /meta_parent_ref in Hparent |- *.
    destruct kobj; simpl in *.
    all: eapply Hno_speculative_parent_reference; exact Hparent.
  }
  { done. }
  { destruct kobj; done. }
  { destruct kobj; done. }
  iMod (cview.simple_update_vs (KObjectV.key kobj) kobj new_kobj with "[$Hinv_Hown_children]") as "Hinv_Hown_children".
  { done. }
  { unfold new_kobj, new_kmeta1, new_kmeta, obj_parent_ref.
    rewrite objectmeta_update_objectmeta Hcurrent_kmeta_eq.
    rewrite /meta_parent_ref. destruct kobj; done.
  }
  { unfold new_kobj, new_kmeta1, new_kmeta.
    rewrite objectmeta_update_objectmeta Hcurrent_kmeta_eq.
    destruct kobj; done.
  }
  iAssert (|={∅,⊤}=> ▷ Φ #interface.nil)%I
    with "[Hclose Hown_meta_frag Hown_children_frag]" as "HΦ_fupd".
  { destruct (decide (delete_options_preconditions_resource_version_none options)) as [_|_].
    - iApply ("Hclose" $! (KObjectV.objectmeta new_kobj)).
      iLeft. iFrame. iPureIntro. destruct kobj; done.
    - iApply ("Hclose" $! interface.nil (KObjectV.objectmeta new_kobj)).
      iLeft. iSplit; first done. iLeft. iFrame. iPureIntro. destruct kobj; done.
  }
  iMod "HΦ_fupd" as "HΦ".
  iModIntro.
  iAssert (([∗ map] i; obj ∈ <[KObjectV.key kobj:=interface.ok i1]> phys_state; <[KObjectV.key kobj:=new_kobj]> abs_state,
    match i with
    | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
    | interface.nil => False%I
    end)%I) with "[Hdeepown_i1 Hother_rep]" as "Hinv_Hphys_abs_rep".
  { rewrite big_sepM2_insert_delete. iFrame. }
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H".
    iFrame "#". iFrame. iPureIntro. split_and!.
    all: try done.
    - eapply tombed_uid_update_eq_used_uid_sub; [done|done|].
      unfold new_kobj, new_kmeta1, new_kmeta.
      rewrite objectmeta_update_objectmeta Hcurrent_kmeta_eq.
      destruct kobj; done.
    - rewrite dom_insert_L.
      assert (KObjectV.key kobj ∈ dom abs_state) as Hkey_in_abs.
      { apply elem_of_dom. eexists. exact Hlookup_abs. }
      Timeout 10 set_solver.
  }
  iApply "HΦ".
  Unshelve. all: try apply _. all: done.
Qed.

Lemma wp_State__delete γ l key options_c options uid kmeta parent_key parent_uid children :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options 1 ∗
      "%Hvalid_options" ∷ ⌜ DeleteOptionsV.valid options ⌝ ∗
      "%Hdelete_preconditions_rv_none" ∷
        ⌜ delete_options_preconditions_resource_version_none options ⌝ ∗
      "%Hkey_in" ∷ ⌜ key ∈ children ⌝ ∗
      "%Hdelete_preconditions" ∷ ⌜ delete_preconditions_match options kmeta ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "delete" #key #options_c
  {{{ kmeta', RET #interface.nil;
      ( "%Hdeletion_timestamp" ∷ ⌜ kmeta'.(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
        "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta' ∗
        "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
        ∨
        "Hown_tombstone_frag" ∷ own_tombstone_frag γ uid ∗
        "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]})
      )
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iPoseProof (kview.own_meta_valid with "Hown_meta_frag") as "%Hmeta_valid".
  destruct Hmeta_valid as (_ & _ & Huid_eq & _).
  pose proof (delete_preconditions_match_uid_of_match options uid kmeta Huid_eq
    Hdelete_preconditions) as Hdelete_preconditions_uid.
  iApply wp_State__delete_au.
  iFrame "#". iFrame "%". iFrame.
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  destruct (decide (delete_options_preconditions_resource_version_none options)) as [_|Hrv_some].
  2: { exfalso. apply Hrv_some. done. }
  iIntros (kmeta') "Hpost".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! kmeta' with "Hpost").
Qed.

Lemma wp_State__PodDelete γ l key namespace name options_c options uid kmeta parent_key parent_uid children :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options 1 ∗
      "%Hvalid_options" ∷ ⌜ DeleteOptionsV.valid options ⌝ ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "Pod"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "%Hkey_in" ∷ ⌜ key ∈ children ⌝ ∗
      "%Hdelete_preconditions" ∷ ⌜ delete_preconditions_match options kmeta ⌝ ∗
      "%Hdelete_preconditions_rv_none" ∷
        ⌜ delete_options_preconditions_resource_version_none options ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "PodDelete" #namespace #name #options_c
  {{{ kmeta', RET #interface.nil;
      ( "%Hdeletion_timestamp" ∷ ⌜ kmeta'.(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
        "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta' ∗
        "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
        ∨
        "Hown_tombstone_frag" ∷ own_tombstone_frag γ uid ∗
        "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]})
      )
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H". subst key.
  wp_method_call. rewrite /apimodel.State__PodDeleteⁱᵐᵖˡ. wp_call. wp_auto.
  wp_apply (wp_State__delete γ l
    {| KKey.Kind' := "Pod"%go; KKey.Namespace' := namespace; KKey.Name' := name |}
    options_c options uid kmeta parent_key parent_uid children
    with "[$Hinit $Hisk $Hdeepown_options $Hown_meta_frag $Hown_children_frag]").
  { iFrame "%". }
  iIntros (kmeta') "Hpost".
  wp_auto.
  iApply ("HΦ" with "Hpost").
Qed.

End proof.
