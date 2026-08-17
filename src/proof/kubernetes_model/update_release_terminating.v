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
  "%Hvalid" ∷ ⌜ KObjectV.valid_named_create kind namespace kobj ⌝ ∗
  "%Huid_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
  "%Hrv_valid" ∷ ⌜ valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion') ⌝ ∗
  "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
  "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
  "%Hnew_parent" ∷ ⌜ obj_parent_ref kobj = None ⌝ ∗
  "%Hterminating" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
  "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
  "#Hown_deletion_observed_frag" ∷ own_deletion_observed_frag γ (KObjectV.key kobj)
    (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ∗
  "Hau" ∷ (|={⊤,∅}=>
    ((∀ i' kobj',
      "%Hsame_kind" ∷ ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1
        ={∅,⊤}=∗ ▷ Φ (#(interface.ok i'), #interface.nil)%V) ∧
     (∀ (ret err : interface.t),
      "%Herror" ∷ ⌜ conflict_error err ∨ (err ≠ interface.nil ∧ ¬ conflict_error err) ⌝
        ={∅,⊤}=∗ ▷ Φ (#ret, #err)%V))
  ) -∗ WP l @! (go.PointerType apimodel.State) @! "update" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & H)". iNamed "H". iNamed "Hkinv".
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
  wp_apply (wp_GetName_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  assert (ObjectMetaV.Name' (KObjectV.objectmeta kobj) ≠ ""%go) as Hname_not_empty.
  { destruct Hvalid as (_ & _ & Hmeta & _).
    unfold ObjectMetaV.valid_named_create in Hmeta. tauto. }
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
    iApply fupd_wp. iMod "Hau" as "[_ Hclose]".
    iMod ("Hclose" $! interface.nil err with "[]") as "HΦ".
    { iPureIntro. right. done. }
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
  wp_apply (wp_GetUID_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct. 1: { exfalso. done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_GetUID_deepown with "[$Hdeepown_m_old_l]").
  iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  2: {
    wp_apply (wp_GetUID_deepown with "[$Hdeepown_m_old_l]").
    iIntros "Hdeepown_m_old_l". wp_auto.
    wp_apply wp_newUpdateUIDConflictError.
    iIntros (err) "%Herr_conflict".
    pose proof (conflict_error_not_nil err Herr_conflict) as Herr_ne.
    iApply fupd_wp. iMod "Hau" as "[_ Hclose]".
    iMod ("Hclose" $! interface.nil err with "[]") as "HΦ".
    { iPureIntro. left. done. }
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
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]").
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_old_l]").
  iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  { exfalso. eapply valid_resource_version_non_empty; done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply wp_parseResourceVersion.
  { iPureIntro. exact Hrv_valid. }
  iIntros (ret) "_". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]").
  iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  2: {
    wp_apply wp_newUpdateResourceVersionConflictError.
    iIntros (err) "%Herr_conflict".
    pose proof (conflict_error_not_nil err Herr_conflict) as Herr_ne.
    wp_auto.
    iApply fupd_wp. iMod "Hau" as "[_ Hclose]".
    iMod ("Hclose" $! interface.nil err with "[]") as "HΦ".
    { iPureIntro. left. done. }
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
  assert (KObjectV.key old_kobj = KObjectV.key kobj) as Hkey_old_new by (rewrite <-Hkey_old; exact Hkey_new).
  iPoseProof (deletion_observation.auth_frag_valid with
    "Hinv_Hown_deletion_observations Hown_deletion_observed_frag") as "%Hobserved".
  destruct Hobserved as (Huid_used & Hobserved).
  assert ((KObjectV.objectmeta old_kobj).(ObjectMetaV.DeletionTimestamp') ≠ None) as Hold_terminating.
  { eapply Hobserved; [exact Hlookup_abs|]. symmetry. exact e. }
  wp_apply (wp_applyValidationAndDefaultingOnUpdate_general with "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (err) "Hvalidation".
  iDestruct "Hvalidation" as
    "[(%Herr_nil & Hvalidation) | (%Herr_ne & %Herr_not_conflict & Hdeepown_l & Hdeepown_old_l)]".
  2: {
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
    iApply fupd_wp. iMod "Hau" as "[_ Hclose]".
    iMod ("Hclose" $! interface.nil (interface.ok err_ok) with "[]") as "HΦ".
    { iPureIntro. right. done. }
    iModIntro.
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ". }
  subst err.
  iDestruct "Hvalidation" as (updated_kobj)
    "(Hdeepown_l & Hdeepown_old_l & %Hvalid_interface_updated & %Hvalid_updated_kobj & %Hsame_key &
      %Htypemeta_eq & %Hupdated_meta & %Hupdated_spec & %Hspec_eq_if_unchanged & %Hstatus_eq)".
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
    iApply fupd_wp. iMod "Hau" as "[Hclose _]".
    iMod ("Hclose" $! i1 updated_kobj with "[$Hdeepown_i1]") as "HΦ".
    { iPureIntro. destruct kobj, updated_kobj; simpl in *; done. }
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
    iApply fupd_wp. iMod "Hau" as "[Hclose _]".
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
  assert (KObjectV.objectmeta_ptr l1 kobj = KObjectV.objectmeta_ptr l1 updated_kobj) as ->.
  { destruct kobj, updated_kobj; simpl in *; simplify_eq; done. }
  wp_apply (wp_SetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_map_insert apimodel.KKey with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null1 with
    "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]") as "Hdeepown_l".
  set new_kmeta := KObjectV.objectmeta updated_kobj <| ObjectMetaV.ResourceVersion' := rv |>.
  set new_kobj := KObjectV.update_objectmeta updated_kobj new_kmeta.
  wp_apply (wp_deepCopy i1 new_kobj with "[Hdeepown_l]").
  { iFrame. iPureIntro. unfold new_kobj, new_kmeta. destruct updated_kobj; done. }
  iIntros (i1') "[Hdeepown_i1' Hdeepown_i1]". wp_auto.
  assert (kview.valid_k_uid_obj key (ObjectMetaV.UID' (KObjectV.objectmeta old_kobj)) new_kobj)
    as Hvalid_kuid_new.
  { unfold kview.valid_k_uid_obj. split.
    - unfold new_kobj, new_kmeta. rewrite key_update_objectmeta_set_resource_version. rewrite <-Hsame_key. exact Hkey_old.
    - split.
      + unfold new_kobj, new_kmeta. rewrite objectmeta_update_objectmeta.
        rewrite <-e. symmetry. eapply objectmeta_updated_set_resource_version_uid. done.
      + unfold new_kobj, new_kmeta. eapply valid_update_objectmeta_set_resource_version; done. }
  assert ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp') ≠ None) as Hnew_terminating.
  { unfold new_kobj, new_kmeta. rewrite objectmeta_update_objectmeta.
    rewrite (objectmeta_updated_set_resource_version_deletion_timestamp _ _ _ Hupdated_meta). exact Hterminating. }
  assert (obj_parent_ref new_kobj = None) as Hnew_parent_none.
  { unfold new_kobj, new_kmeta, obj_parent_ref. rewrite objectmeta_update_objectmeta.
    rewrite /ObjectMetaV.updated in Hupdated_meta.
    rewrite /obj_parent_ref /meta_parent_ref in Hnew_parent |- *.
    destruct (KObjectV.objectmeta kobj), (KObjectV.objectmeta updated_kobj); simpl in *.
    decompose [and] Hupdated_meta. subst. done. }
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
  { unfold new_kobj, new_kmeta. rewrite objectmeta_update_objectmeta. symmetry.
    rewrite (objectmeta_updated_set_resource_version_uid _ _ _ Hupdated_meta). exact e. }
  iMod (terminating_children.update_remove_parent_vs γ.(γ_terminating_children) abs_state key old_kobj new_kobj
    with "Hinv_Hown_terminating_children") as "Hinv_Hown_terminating_children".
  { exact Hlookup_abs. }
  { unfold terminating_children.terminating_obj_parent_ref.
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp')) eqn:Hnew_dt;
      [exact Hnew_parent_none|exfalso; done]. }
  iMod (deletion_observation.update_vs key old_kobj new_kobj with "Hinv_Hown_deletion_observations")
    as "Hinv_Hown_deletion_observations".
  { exact Hlookup_abs. }
  { unfold new_kobj, new_kmeta. rewrite objectmeta_update_objectmeta. symmetry.
    rewrite (objectmeta_updated_set_resource_version_uid _ _ _ Hupdated_meta). exact e. }
  { intros _. exact Hnew_terminating. }
  iAssert (([∗ map] i; obj ∈ <[key:=interface.ok i1]> phys_state; <[key:=new_kobj]> abs_state,
    match i with
    | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
    | interface.nil => False%I
    end)%I) with "[Hdeepown_i1 Hother_rep]" as "Hinv_Hphys_abs_rep".
  { rewrite big_sepM2_insert_delete. iFrame. }
  iApply fupd_wp. iMod "Hau" as "[Hclose _]".
  iMod ("Hclose" $! i1' new_kobj with "[$Hdeepown_i1']") as "HΦ".
  { iPureIntro. unfold new_kobj. destruct kobj, updated_kobj; simpl in *; done. }
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
      "%Hvalid" ∷ ⌜ KObjectV.valid_named_create kind namespace kobj ⌝ ∗
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
      ⌜ conflict_error err ∨ (err ≠ interface.nil ∧ ¬ conflict_error err) ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & H) HΦ". iNamed "H".
  iApply wp_State__update_release_terminating_au.
  iFrame "#". iFrame "%". iFrame.
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask". iSplit.
  - iIntros (i' kobj') "(%Hsame_kind & Hdeepown_i)".
    iMod "Hmask" as "_". iModIntro. iNext.
    iApply ("HΦ" $! (interface.ok i') interface.nil). iLeft.
    iExists i', kobj'. iFrame. done.
  - iIntros (ret err) "%Herror".
    iMod "Hmask" as "_". iModIntro. iNext.
    iApply ("HΦ" $! ret err). iRight. done.
Qed.


End proof.
