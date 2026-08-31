From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update_release.
From New.proof.kubernetes_model Require Import common_delete.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(** The terminating release path supplies no strong kview fragment. It can
    therefore distinguish only the absent/reused/same-UID cases, and a stale
    same-UID request is allowed to fail validation. *)
Lemma wp_State__update_release_terminating_au γ l kind namespace i kobj :
  ∀ Φ,
  is_pkg_init apimodel ∗
  is_kubernetes γ l ∗
  "%Hnew_parent" ∷ ⌜ obj_parent_ref kobj = None ⌝ ∗
  "%Hterminating" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
  "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
  "Hau" ∷ (|={⊤, ∅}=> ∃ old_meta old_spec,
    "#Hown_deletion_observed_frag" ∷ own_deletion_observed_frag γ (KObjectV.key kobj)
      (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ∗
    "%Hvalid_update" ∷ ⌜ KObjectV.valid_update kind namespace old_meta old_spec kobj ⌝ ∗
    "Hclose" ∷ ((∀ i' kobj',
      ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
      KObjectV.deepown_i i' kobj' 1
        ={∅, ⊤}=∗ ▷ Φ (#(interface.ok i'), #interface.nil)%V) ∧
     (∀ (ret err : interface.t),
      ⌜ err ≠ interface.nil ⌝
        ={∅, ⊤}=∗ ▷ Φ (#ret, #err)%V))
  ) -∗ WP l @! (go.PointerType apimodel.State) @! "update" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & H)". iNamed "H". iNamed "Hkinv".
  destruct (Classical_Prop.classic (
      KObjectV.valid_create kind namespace kobj ∧
      (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go ∧
      valid_typemeta (KObjectV.kind kobj) (KObjectV.typemeta kobj) ∧
      (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ∧
      valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion') ∧
      namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace')))
    as [Hvalid_update_input|Hinvalid_update_input].
  2: {
    iApply fupd_wp.
    iMod "Hau" as (old_meta old_spec) "H". iNamed "H".
    exfalso. apply Hinvalid_update_input.
    revert Hvalid_update.
    destruct old_spec, kobj; rewrite /KObjectV.valid_update /=;
      rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
        ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
        ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
        /KObjectV.valid_create /=;
      try contradiction; tauto.
  }
  destruct Hvalid_update_input as
    (Hvalid & Hname_nonempty & Hvalid_typemeta & Huid_nonempty & Hrv_valid &
      Hns_matches).
  assert (kind = KObjectV.kind kobj) as Hkind_matches.
  { destruct kobj; rewrite /KObjectV.valid_create /= in Hvalid;
      rewrite ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create in Hvalid;
      tauto. }
  wp_method_call. rewrite /apimodel.State__updateⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|].
  iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_".
  rewrite exception_do_unseal /exception_do_def. wp_auto.
  wp_apply (wp_deepCopy i kobj with "[Hdeepown_i]").
  { iFrame "#". iExact "Hdeepown_i". }
  iIntros (i1) "[Hdeepown_i1 Hdeepown_i]". wp_auto.
  iDestruct "Hdeepown_i1" as (l1) "[%Hvalid_interface Hdeepown_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null & Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  wp_apply (wp_EnsureObjectNamespaceMatchesRequestNamespace with "[$Hdeepown_m_l]").
  { iPureIntro. split; [done|]. right. done. }
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetName_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_map_lookup2 apimodel.KKey (go.InterfaceType []) with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
  iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq.
  set key := {|
    KKey.Kind' := kind;
    KKey.Name' := ObjectMetaV.Name' (KObjectV.objectmeta kobj);
    KKey.Namespace' := namespace
  |}.
  assert (key = KObjectV.key kobj) as Hkey_new.
  { unfold key. rewrite Hkind_matches Hns_matches. destruct kobj; done. }
  destruct (bool_decide (is_Some (phys_state !! key))) eqn:Hdecide.
  2: {
    apply bool_decide_eq_false in Hdecide.
    assert (phys_state !! key = None) as Hlookup_phys.
    { destruct (phys_state !! key) as [i'|] eqn:Hlookup_phys; [|done].
      exfalso. apply Hdecide. done. }
    rewrite /is_Some Hlookup_phys. wp_auto.
    wp_apply (wp_NewNotFound
      {| schema.GroupResource.Group' := ""%go;
         schema.GroupResource.Resource' := key.(KKey.Kind') |} key.(KKey.Name')).
    iIntros (err_l) "%Hnot_found". wp_auto.
    set err := interface.mk_ok (go.PointerType api_errors.StatusError) #err_l.
    pose proof (not_found_error_not_nil err Hnot_found) as Herr_ne.
    pose proof (not_found_error_not_conflict err Hnot_found) as Hnot_conflict.
    iApply fupd_wp.
    iMod "Hau" as (witness_meta witness_spec)
      "(#Hdeletion_observed & %Hvalid_update_witness & [_ Hclose])".
    iMod ("Hclose" $! interface.nil err with "[]") as "HΦ".
    { iPureIntro. exact Herr_ne. }
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ". }
  apply bool_decide_eq_true in Hdecide.
  destruct Hdecide as [old_i Hlookup_phys].
  assert (∃ old_kobj, abs_state !! key = Some old_kobj) as [old_kobj Hlookup_abs].
  { apply elem_of_dom. rewrite <-Hdom_eq. apply elem_of_dom. eexists. done. }
  iDestruct (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs
    with "Hinv_Hphys_abs_rep") as "(Hdeepown_old_i & Hother_rep)".
  destruct old_i as [old_i|]. 2: { iExFalso. iExact "Hdeepown_old_i". }
  rewrite Hlookup_phys. wp_auto.
  wp_apply (wp_deepCopy old_i old_kobj with "[Hdeepown_old_i]").
  { iFrame "#". iExact "Hdeepown_old_i". }
  iIntros (old_i1) "[Hdeepown_old_i1 Hdeepown_old_i]". wp_auto.
  iDestruct "Hdeepown_old_i1" as (old_l1) "[%Hvalid_interface_old Hdeepown_old_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_old_l") as
    "(%Hold_l1_not_null & Hdeepown_t_old_l & Hdeepown_m_old_l & Hdeepown_s_old_l & Hdeepown_st_old_l)".
  wp_apply (wp_GetUID_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct. 1: { exfalso. done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_GetUID_deepown_kobject old_i1 old_l1 old_kobj with
    "[$Hdeepown_m_old_l]"). 1: done.
  iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  2: {
    wp_apply (wp_GetUID_deepown_kobject old_i1 old_l1 old_kobj with
      "[$Hdeepown_m_old_l]"). 1: done.
    iIntros "Hdeepown_m_old_l". wp_auto.
    wp_apply wp_newUpdateUIDConflictError.
    iIntros (err) "%Herr_conflict".
    pose proof (conflict_error_not_nil err Herr_conflict) as Herr_ne.
    iApply fupd_wp.
    iMod "Hau" as (witness_meta witness_spec)
      "(#Hdeletion_observed & %Hvalid_update_witness & [_ Hclose])".
    iMod ("Hclose" $! interface.nil err with "[]") as "HΦ".
    { iPureIntro. exact Herr_ne. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I) with "[Hdeepown_old_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs). iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ". }
  wp_apply (wp_GetResourceVersion_deepown_kobject i1 l1 kobj with
    "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown_kobject old_i1 old_l1 old_kobj with
    "[$Hdeepown_m_old_l]"). 1: done.
  iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  { exfalso. eapply valid_resource_version_non_empty; done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply wp_parseResourceVersion.
  { iPureIntro. exact Hrv_valid. }
  iIntros (ret) "_". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown_kobject i1 l1 kobj with
    "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  2: {
    wp_apply wp_newUpdateResourceVersionConflictError.
    iIntros (err) "%Herr_conflict".
    pose proof (conflict_error_not_nil err Herr_conflict) as Herr_ne.
    wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (witness_meta witness_spec)
      "(#Hdeletion_observed & %Hvalid_update_witness & [_ Hclose])".
    iMod ("Hclose" $! interface.nil err with "[]") as "HΦ".
    { iPureIntro. exact Herr_ne. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I) with "[Hdeepown_old_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs). iFrame. }
    iCombineNamed "Hinv_*" as "H".
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ". }
  assert ((KObjectV.objectmeta kobj <|
    ObjectMetaV.Namespace' := ObjectMetaV.Namespace' (KObjectV.objectmeta kobj) |>) =
    KObjectV.objectmeta kobj) as -> by (destruct (KObjectV.objectmeta kobj); done).
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hold_l1_not_null with
    "[$Hdeepown_t_old_l $Hdeepown_m_old_l $Hdeepown_s_old_l $Hdeepown_st_old_l]") as "Hdeepown_old_l".
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hl1_not_null with
    "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]") as "Hdeepown_l".
  iPoseProof (kview.own_auth_valid2 key old_kobj with "Hinv_Hown_abs") as "%Hauth_old". 1: done.
  destruct Hauth_old as
    (Hkey_old & Hvalid_old_kobj & Huid_old_in & Hno_speculative_parent_reference_old & Huid_unique_old).
  iPoseProof (kview.own_auth_extra_valid_forall with "Hinv_Hown_abs")
    as "%Habs_extra_valid".
  assert (KObjectV.extra_valid old_kobj) as Hextra_valid_old.
  { exact (Habs_extra_valid key old_kobj Hlookup_abs). }
  assert (KObjectV.key old_kobj = KObjectV.key kobj) as Hkey_old_new by (rewrite <-Hkey_old; exact Hkey_new).
  assert (update_prepared_for_helper
      (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') old_kobj kobj kobj) as Hprepared.
  { rewrite /update_prepared_for_helper. split_and!.
    - right. done.
    - right. exact e0.
    - exact Hkey_old_new.
    - rewrite <-e0.
      destruct kobj as [[tm meta spec status]|[tm meta spec status]|
        [tm meta spec status]|[tm meta spec status]]; destruct meta; done. }
  destruct ((KObjectV.objectmeta old_kobj).(ObjectMetaV.DeletionTimestamp'))
    as [old_deletion_timestamp|] eqn:Hold_deletion_timestamp.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (witness_meta witness_spec) "H". iNamed "H".
    iPoseProof (deletion_observation.auth_frag_valid with
      "Hinv_Hown_deletion_observations Hown_deletion_observed_frag") as "%Hobserved".
    destruct Hobserved as (_ & Hobserved).
    pose proof (Hobserved old_kobj Hlookup_abs (eq_sym e)) as Hstored_terminating.
    rewrite Hold_deletion_timestamp in Hstored_terminating. done.
  }
  assert ((KObjectV.objectmeta old_kobj).(ObjectMetaV.DeletionTimestamp') ≠ None) as Hold_terminating.
  { rewrite Hold_deletion_timestamp. done. }
  assert (KObjectV.same_kind old_kobj kobj) as Hsame_kind_old_input.
  { destruct old_kobj, kobj; simpl in Hkey_old_new |- *; try done;
      unfold KObjectV.key in Hkey_old_new; simpl in Hkey_old_new; congruence. }
  wp_apply (wp_applyValidationAndDefaultingOnUpdate_general with "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (err) "Hvalidation".
  iDestruct "Hvalidation" as
    "[(%Herr_nil & Hvalidation) | (%Herr_ne & %Herr_not_conflict & Hvalidation)]".
  2: {
    iDestruct "Hvalidation" as
      (failed_kobj) "(Hdeepown_l & Hdeepown_old_l & %Hvalid_interface_failed)".
    wp_auto.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I) with "[Hdeepown_old_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs). iFrame. }
    iCombineNamed "Hinv_*" as "H".
    change (err ≠ interface.nil) in Herr_ne.
    destruct err as [err_ok|]; [|done]. wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (witness_meta witness_spec)
      "(#Hdeletion_observed & %Hvalid_update_witness & [_ Hclose])".
    iMod ("Hclose" $! interface.nil (interface.ok err_ok) with "[]") as "HΦ".
    { iPureIntro. exact Herr_ne. }
    iModIntro.
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ". }
  subst err.
  iDestruct "Hvalidation" as (updated_kobj)
    "(Hdeepown_l & Hdeepown_old_l & %Hvalid_interface_updated & %Hhelper_updated)".
  pose proof Hhelper_updated as
    (Hstatus_eq & _ & Hhelper_result_updated & Hhelper_result_valid &
      Hhelper_result_extra_valid).
  assert (update_objects_equiv_except_resource_version updated_kobj updated_kobj)
    as Hequiv_updated_refl.
  { rewrite /update_objects_equiv_except_resource_version
      /ObjectMetaV.equiv_except_resource_version.
    destruct updated_kobj; done. }
  pose proof (Hhelper_result_updated kobj updated_kobj Hprepared Hequiv_updated_refl)
    as Hupdated_kobj.
  assert (KObjectV.same_kind kobj updated_kobj) as Hsame_kind_updated.
  { destruct kobj, updated_kobj; simpl in Hupdated_kobj |- *; try contradiction; done. }
  pose proof (Hhelper_result_valid Hvalid_old_kobj Hvalid_typemeta)
    as Hvalid_updated_kobj.
  pose proof (Hhelper_result_extra_valid Hextra_valid_old) as Hextra_valid_updated_kobj.
  wp_auto.
  wp_apply (wp_shouldDeleteDuringUpdate_general with "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (should_delete) "(Hdeepown_l & Hdeepown_old_l & %Hshould_delete)".
  destruct should_delete; wp_auto.
  {
    wp_apply (wp_map_delete _ _ key apimodel.KKey (go.InterfaceType []) with "[$Hinv_Hown_phys]").
    iIntros "Hinv_Hown_phys". wp_auto.
    iMod (kview.delete_terminating_kobj_vs Hlookup_abs Hold_terminating with "Hinv_Hown_abs")
      as "Hinv_Hown_abs".
    iMod (cview.delete_orphan_vs key old_kobj with "Hinv_Hown_children") as "Hinv_Hown_children".
    { exact Hlookup_abs. }
    { unfold living_obj_parent_ref. destruct ((KObjectV.objectmeta old_kobj).(ObjectMetaV.DeletionTimestamp')); done. }
    iMod (terminating_children.delete_vs γ.(γ_terminating_children) abs_state key with
      "Hinv_Hown_terminating_children") as "Hinv_Hown_terminating_children".
    iMod (deletion_observation.delete_vs key with "Hinv_Hown_deletion_observations")
      as "Hinv_Hown_deletion_observations".
    iAssert (([∗ map] i; obj ∈ delete key phys_state; delete key abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I) with "[Hother_rep]" as "Hinv_Hphys_abs_rep".
    { iFrame. }
    iAssert (KObjectV.deepown_i i1 updated_kobj 1) with "[Hdeepown_l]" as "Hdeepown_i1".
    { iExists l1. iFrame. iPureIntro. exact Hvalid_interface_updated. }
    iApply fupd_wp.
    iMod "Hau" as (witness_meta witness_spec)
      "(#Hdeletion_observed & %Hvalid_update_witness & [Hclose _])".
    iMod ("Hclose" $! i1 updated_kobj with "[$Hdeepown_i1]") as "HΦ".
    { iPureIntro. exact Hsame_kind_updated. }
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ". }
  wp_apply (wp_storageObjectDeepEqual with "[$Hdeepown_l $Hdeepown_old_l]").
  { iPureIntro. split_and!; done. }
  iIntros (same) "(Hdeepown_i1 & Hdeepown_old_i1 & %Hsame)".
  wp_if_destruct.
  {
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I) with "[Hdeepown_old_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs). iFrame. }
    iApply fupd_wp.
    iMod "Hau" as (witness_meta witness_spec)
      "(#Hdeletion_observed & %Hvalid_update_witness & [Hclose _])".
    iMod ("Hclose" $! old_i1 old_kobj with "[$Hdeepown_old_i1]") as "HΦ".
    { iPureIntro. destruct kobj, updated_kobj, old_kobj; simpl in *; try done;
      unfold storage_object_normalize in Hsame; simpl in Hsame; congruence. }
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ". }
  wp_apply (wp_State__generateNewRVAndUpdate with "[$Hinv_Hstate_used_rv_addr $Hinv_Hown_used_rv]").
  iIntros (rv) "(%Hlookup_phys_used_rv & %Hvalid_rv & Hinv_Hstate_used_rv_addr & Hinv_Hown_used_rv)". wp_auto.
  iPoseProof (KObjectV.deepown_i_yields_deepown_l with "[$Hdeepown_i1]") as "Hdeepown_l". 1: done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null1 & Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  wp_apply (wp_SetResourceVersion_deepown_kobject i1 l1 updated_kobj with
    "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_map_insert apimodel.KKey with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null1 with
    "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]") as "Hdeepown_l".
  set new_kmeta := KObjectV.objectmeta updated_kobj <| ObjectMetaV.ResourceVersion' := rv |>.
  set new_kobj := KObjectV.update_objectmeta updated_kobj new_kmeta.
  wp_apply (wp_deepCopy i1 new_kobj with "[Hdeepown_l]").
  { iFrame. iPureIntro. unfold new_kobj, new_kmeta. destruct updated_kobj; done. }
  iIntros (i1') "[Hdeepown_i1' Hdeepown_i1]". wp_auto.
  assert (update_objects_equiv_except_resource_version updated_kobj new_kobj)
    as Hequiv_updated_new.
  { unfold new_kobj, new_kmeta, update_objects_equiv_except_resource_version.
    destruct updated_kobj; simpl; split_and!; try done.
    all: rewrite /ObjectMetaV.equiv_except_resource_version
      /ObjectMetaV.without_resource_version; destruct ObjectMeta'; done. }
  pose proof (Hhelper_result_updated kobj new_kobj Hprepared Hequiv_updated_new)
    as Hupdated_new.
  assert (KObjectV.same_kind kobj new_kobj ∧
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.Name') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ∧
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.Namespace') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ∧
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.UID') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ∧
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp'))
    as (Hsame_kind_new & Hname_new & Hnamespace_stored_new & Huid_new &
      Hdeletion_timestamp_new).
  { destruct kobj, new_kobj;
      rewrite /KObjectV.updated /PodV.updated /ReplicaSetV.updated
        /PersistentVolumeClaimV.updated /StatefulSetV.updated /= in Hupdated_new |- *;
      try contradiction; rewrite /ObjectMetaV.updated in Hupdated_new |- *; tauto. }
  assert (KObjectV.valid new_kobj) as Hvalid_new.
  { unfold new_kobj, new_kmeta.
    pose proof Hvalid_updated_kobj as
      (Hupdated_valid_typemeta & _ & Hupdated_valid_meta & Hupdated_valid_spec &
        Hupdated_valid_status).
    split_and!.
    - rewrite KObjectV.kind_update_objectmeta KObjectV.typemeta_update_objectmeta.
      exact Hupdated_valid_typemeta.
    - rewrite objectmeta_update_objectmeta. exact Hvalid_rv.
    - rewrite KObjectV.kind_update_objectmeta objectmeta_update_objectmeta.
      destruct (KObjectV.objectmeta updated_kobj); simpl in *; done.
    - rewrite KObjectV.spec_update_objectmeta. exact Hupdated_valid_spec.
    - rewrite KObjectV.status_update_objectmeta. exact Hupdated_valid_status. }
  assert (kview.valid_k_uid_obj key (ObjectMetaV.UID' (KObjectV.objectmeta old_kobj)) new_kobj)
    as Hvalid_kuid_new.
  { unfold kview.valid_k_uid_obj. split.
    - rewrite Hkey_old /KObjectV.key.
      rewrite Hname_new Hnamespace_stored_new.
      destruct kobj, new_kobj; simpl in Hsame_kind_new |- *; try done.
    - split.
      + rewrite <-e. symmetry. exact Huid_new.
      + split.
        * exact Hvalid_new.
        * unfold new_kobj.
          apply KObjectV.extra_valid_update_objectmeta.
          exact Hextra_valid_updated_kobj. }
  assert ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp') ≠ None) as Hnew_terminating.
  { rewrite Hdeletion_timestamp_new. exact Hterminating. }
  assert (obj_parent_ref new_kobj = None) as Hnew_parent_none.
  { rewrite (kobject_updated_parent_ref _ _ Hupdated_new) Hnew_parent. done. }
  iMod (kview.update_terminating_kobj_vs Hvalid_kuid_new Hnew_terminating with "Hinv_Hown_abs")
    as "Hinv_Hown_abs".
  { unfold no_speculative_parent_reference. intros kind' name' uid' Hparent.
    unfold meta_parent_ref_is in Hparent. unfold obj_parent_ref in Hnew_parent_none.
    rewrite Hnew_parent_none in Hparent. done. }
  { exact Hlookup_abs. }
  { reflexivity. }
  { exact Hold_terminating. }
  iMod (cview.simple_update_vs key old_kobj new_kobj with "Hinv_Hown_children") as "Hinv_Hown_children".
  { exact Hlookup_abs. }
  { unfold living_obj_parent_ref.
    destruct ((KObjectV.objectmeta old_kobj).(ObjectMetaV.DeletionTimestamp')) eqn:Hold_dt; [|exfalso; done].
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp')) eqn:Hnew_dt; [|exfalso; done]. done. }
  { rewrite <-e. symmetry. exact Huid_new. }
  iMod (terminating_children.update_remove_parent_vs γ.(γ_terminating_children) abs_state key old_kobj new_kobj
    with "Hinv_Hown_terminating_children") as "Hinv_Hown_terminating_children".
  { exact Hlookup_abs. }
  { unfold terminating_children.terminating_obj_parent_ref.
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp')) eqn:Hnew_dt;
      [exact Hnew_parent_none|exfalso; done]. }
  iMod (deletion_observation.update_vs key old_kobj new_kobj with "Hinv_Hown_deletion_observations")
    as "Hinv_Hown_deletion_observations".
  { exact Hlookup_abs. }
  { rewrite <-e. symmetry. exact Huid_new. }
  { intros _. exact Hnew_terminating. }
  iAssert (([∗ map] i; obj ∈ <[key:=interface.ok i1]> phys_state; <[key:=new_kobj]> abs_state,
    match i with
    | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
    | interface.nil => False%I
    end)%I) with "[Hdeepown_i1 Hother_rep]" as "Hinv_Hphys_abs_rep".
  { rewrite big_sepM2_insert_delete. iFrame. }
  iApply fupd_wp.
  iMod "Hau" as (witness_meta witness_spec)
    "(#Hdeletion_observed & %Hvalid_update_witness & [Hclose _])".
  iMod ("Hclose" $! i1' new_kobj with "[$Hdeepown_i1']") as "HΦ".
  { iPureIntro. exact Hsame_kind_new. }
  iModIntro.
  iCombineNamed "Hinv_*" as "H".
  rewrite return_val_unseal /return_val_def. wp_auto.
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#". done. }
  iExact "HΦ".
Unshelve. all: try tc_solve. all: try apply _. all: try exact sem. all: try done.
Qed.

Lemma wp_State__update_release_terminating γ l kind namespace i kobj :
  {{{ "#Hpkg" ∷ is_pkg_init apimodel ∗
      "#Hkinv" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid_create kind namespace kobj ⌝ ∗
      "%Hname_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go ⌝ ∗
      "%Hvalid_typemeta" ∷ ⌜ valid_typemeta (KObjectV.kind kobj) (KObjectV.typemeta kobj) ⌝ ∗
      "%Huid_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
      "%Hrv_valid" ∷ ⌜ valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion') ⌝ ∗
      "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
      "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
      "%Hnew_parent" ∷ ⌜ obj_parent_ref kobj = None ⌝ ∗
      "%Hterminating" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "#Hown_deletion_observed_frag" ∷ own_deletion_observed_frag γ (KObjectV.key kobj)
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID')
  }}}
    l @! (go.PointerType apimodel.State) @! "update" #kind #namespace #(interface.ok i)
  {{{ (ret err : interface.t), RET (#ret, #err);
      (∃ i' kobj',
        ⌜ ret = interface.ok i' ∧ err = interface.nil ∧ KObjectV.same_kind kobj kobj' ⌝ ∗
        KObjectV.deepown_i i' kobj' 1) ∨
      ⌜ err ≠ interface.nil ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & H) HΦ". iNamed "H".
  assert (ObjectMetaV.valid_update
      (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj)) as Hvalid_meta_update.
  { rewrite /ObjectMetaV.valid_update. split.
    - left. rewrite /ObjectMetaV.valid_simple_update. done.
    - destruct kobj as [pod|rs|pvc|sts]; simpl in Hvalid, Hname_nonempty |- *;
        rewrite ?/PodV.valid_create ?/ReplicaSetV.valid_create
          ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create in Hvalid;
        destruct Hvalid as (_ & _ & _ & _ & Hvalid_meta & _);
        rewrite /ObjectMetaV.valid_create in Hvalid_meta;
        tauto. }
  assert (ObjectSpecV.valid_update
      (KObjectV.spec kobj) (KObjectV.spec kobj)) as Hvalid_spec_update.
  { destruct kobj as [pod|rs|pvc|sts]; simpl in Hvalid |- *;
      rewrite ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create in Hvalid;
      destruct Hvalid as (_ & _ & _ & _ & _ & Hvalid_spec).
    - apply PodSpecV.valid_update_refl. exact Hvalid_spec.
    - apply ReplicaSetSpecV.valid_update_refl. exact Hvalid_spec.
    - apply PersistentVolumeClaimSpecV.valid_update_refl. exact Hvalid_spec.
    - apply StatefulSetSpecV.valid_update_refl. exact Hvalid_spec. }
  assert (KObjectV.valid_update kind namespace
      (KObjectV.objectmeta kobj) (KObjectV.spec kobj) kobj) as Hvalid_update.
  { destruct kobj as [pod|rs|pvc|sts]; simpl in *;
      rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
        ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update;
      split_and!; assumption. }
  iApply wp_State__update_release_terminating_au.
  iFrame "#". iFrame "%". iFrame "Hdeepown_i".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iSplit.
  - iIntros (i' kobj') "(%Hsame_kind & Hdeepown_i)".
    iMod "Hmask" as "_". iModIntro. iNext.
    iApply ("HΦ" $! (interface.ok i') interface.nil). iLeft.
    iExists i', kobj'. iFrame. done.
  - iIntros (ret err) "%Herror".
    iMod "Hmask" as "_". iModIntro. iNext.
    iApply ("HΦ" $! ret err). iRight. done.
Qed.


End proof.
