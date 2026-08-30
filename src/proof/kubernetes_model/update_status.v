From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_update.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__update_status_au γ l kind namespace i kobj :
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    (|={⊤, ∅}=> ∃ key uid kmeta kstatus,
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid 1 kstatus ∗
      "%Hvalid_status_update" ∷ ⌜ KObjectV.valid_status_update kind namespace kmeta kstatus kobj ⌝ ∗
      "%Hvalid_simple_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta (KObjectV.objectmeta kobj) ⌝ ∗
      "Hclose" ∷ (
        (∀ i' old_spec kobj',
          ( ⌜ KObjectV.valid kobj' ⌝ ∗
            ⌜ KObjectV.status_updated old_spec kobj kobj' ⌝ ∗
            KObjectV.deepown_i i' kobj' 1 ∗
            own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
            own_status_frag γ key uid 1 (KObjectV.status kobj'))
            ={∅,⊤}=∗ ▷ Φ (#(interface.ok i'), #interface.nil)%V) ∧
        (∀ err,
          ( ⌜ conflict_error err ⌝ ∗
            own_meta_frag γ key uid 1 kmeta ∗
            own_status_frag γ key uid 1 kstatus)
            ={∅,⊤}=∗ ▷ Φ (#interface.nil, #err)%V)
      )%I
    ) -∗ WP l @! (go.PointerType apimodel.State) @! "updateStatus" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  destruct (Classical_Prop.classic (
      kind = KObjectV.kind kobj ∧
      (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go ∧
      (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ∧
      namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ∧
      valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion') ∧
      valid_typemeta (KObjectV.kind kobj) (KObjectV.typemeta kobj) ∧
      valid_labels (KObjectV.objectmeta kobj).(ObjectMetaV.Labels') ∧
      valid_annotations (KObjectV.objectmeta kobj).(ObjectMetaV.Annotations') ∧
      valid_owner_references (KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences') ∧
      valid_finalizers (KObjectV.objectmeta kobj).(ObjectMetaV.Finalizers') ∧
      valid_managed_fields (KObjectV.objectmeta kobj).(ObjectMetaV.ManagedFields')))
    as [Hvalid_status_update_input|Hinvalid_status_update_input].
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key uid kmeta kstatus) "H". iNamed "H".
    exfalso. apply Hinvalid_status_update_input.
    destruct kstatus, kobj; rewrite /KObjectV.valid_status_update /= in Hvalid_status_update;
      rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
        ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
        /ObjectMetaV.valid_update in Hvalid_status_update;
      try contradiction; tauto.
  }
  destruct Hvalid_status_update_input as
    (Hkind_matches & Hname_nonempty & Huid_nonempty & Hns_matches & Hrv_valid &
      Hvalid_typemeta & Hlabels & Hannotations & Howners &
      Hfinalizers & Hmanaged_fields).
  wp_method_call. rewrite /apimodel.State__updateStatusⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_deepCopy i kobj with "[Hdeepown_i]").
  { iFrame "#". iExact "Hdeepown_i". }
  iIntros (i1) "[Hdeepown_i1 Hdeepown_i]". wp_auto.
  iDestruct "Hdeepown_i1" as (l1) "[%Hvalid_interface Hdeepown_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null & Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  wp_apply (wp_EnsureObjectNamespaceMatchesRequestNamespace with "[$Hdeepown_m_l]").
  { iPureIntro. split. 1: done. right. done. }
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetName_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
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
  assert (namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace')) as Hnamespace_new.
  { done. }
  destruct (bool_decide (is_Some (phys_state !! key))) eqn:Hdecide.
  2: {
    apply bool_decide_eq_false in Hdecide.
    assert (phys_state !! key = None) as Hlookup_phys_none.
    { destruct (phys_state !! key) as [i'|] eqn:Hlookup_phys; [|done].
      exfalso. apply Hdecide. done. }
    assert (abs_state !! key = None) as Hlookup_abs.
    { apply not_elem_of_dom. rewrite <- Hdom_eq.
      apply not_elem_of_dom. done. }
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
    iPoseProof (own_status_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_status_update with
      "Hinv_Hown_abs Hown_meta_frag Hown_status_frag") as
      "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. symmetry. exact Hkey_new. }
    iPoseProof (kview.own_meta_exists with "Hinv_Hown_abs Hown_meta_frag")
      as "(%obj & %Hlookup_abs' & %Huid_obj & %Hmeta_eq & %Huid_in)".
    assert (abs_state !! key ≠ None) as Hlookup_abs''.
    { intros Hnone. rewrite Hlookup_abs' in Hnone. done. }
    exfalso.
    done.
  }
  assert (∃ old_i, phys_state !! key = Some old_i) as [old_i Hlookup_phys].
  { apply bool_decide_eq_true in Hdecide. done. }
  assert (∃ old_kobj, abs_state !! key = Some old_kobj) as [old_kobj Hlookup_abs].
  { apply elem_of_dom. rewrite <- Hdom_eq. apply elem_of_dom. eexists. done. }
  iDestruct (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs with "Hinv_Hphys_abs_rep")
    as "(Hdeepown_old_i & Hother_rep)".
  destruct old_i as [old_i|].
  2: { iExFalso. iExact "Hdeepown_old_i". }
  rewrite Hlookup_phys. wp_auto.
  wp_apply (wp_deepCopy old_i old_kobj with "[Hdeepown_old_i]").
  { iFrame "#". iExact "Hdeepown_old_i". }
  iIntros (old_i1) "[Hdeepown_old_i1 Hdeepown_old_i]". wp_auto.
  iDestruct "Hdeepown_old_i1" as (old_l1) "[%Hvalid_interface_old Hdeepown_old_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_old_l") as
    "(%Hold_l1_not_null & Hdeepown_t_old_l & Hdeepown_m_old_l & Hdeepown_s_old_l & Hdeepown_st_old_l)".
  wp_apply (wp_GetUID_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  1: { exfalso. done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_GetUID_deepown with "[$Hdeepown_m_old_l]"). iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
    iPoseProof (own_status_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_status_update with
      "Hinv_Hown_abs Hown_meta_frag Hown_status_frag") as
      "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (kview.own_meta_living Hlookup_abs with
      "Hinv_Hown_abs Hown_meta_frag") as "%Hold_living".
    exfalso.
    rewrite Huid_eq in Huid_obj. symmetry in Huid_obj. done.
  }
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_old_l]"). iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  { exfalso. eapply valid_resource_version_non_empty; done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply wp_parseResourceVersion.
  { iPureIntro. exact Hrv_valid. }
  iIntros (ret) "_". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  2: {
    wp_apply wp_newUpdateResourceVersionConflictError.
    iIntros (err) "%Herr_conflict".
    pose proof (conflict_error_not_nil err Herr_conflict) as Herr_not_nil.
    wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
    iPoseProof (own_status_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_status_update with
      "Hinv_Hown_abs Hown_meta_frag Hown_status_frag") as
      "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iDestruct "Hclose" as "[_ Hclose_err]".
    iMod ("Hclose_err" $! err with "[Hown_meta_frag Hown_status_frag]") as "HΦ".
    { iSplit; first done. iFrame. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I)
      with "[Hdeepown_old_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs).
      iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ".
  }
  set P := ObjectMetaV.valid_simple_update (KObjectV.objectmeta old_kobj) (KObjectV.objectmeta kobj) ∧
    ObjectStatusV.valid_update (KObjectV.status old_kobj) (KObjectV.status kobj).
  destruct (bool_decide(P)) eqn:Hdecide'.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
    iPoseProof (own_status_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_status_update with
      "Hinv_Hown_abs Hown_meta_frag Hown_status_frag") as
      "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
    assert (ObjectMetaV.valid_update kmeta (KObjectV.objectmeta kobj) ∧
        ObjectStatusV.valid_update kstatus (KObjectV.status kobj)) as
      (Hvalid_meta_update & Hvalid_status_update_parts).
    { destruct kstatus, kobj; rewrite /KObjectV.valid_status_update /= in Hvalid_status_update;
        rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
          ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
          in Hvalid_status_update;
        try contradiction; tauto. }
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (kview.own_meta_living Hlookup_abs with
      "Hinv_Hown_abs Hown_meta_frag") as "%Hold_living".
    iPoseProof (kview.own_status_exists with "Hinv_Hown_abs Hown_status_frag") as "%Hstatus_found".
    assert (KObjectV.status old_kobj = kstatus) as Hstatus_eq.
    { eapply Hstatus_found; done. }
    apply bool_decide_eq_false in Hdecide'.
    exfalso. apply Hdecide'. unfold P.
    split.
    - rewrite /ObjectMetaV.valid_simple_update in Hvalid_simple_update |- *.
      rewrite /ObjectMetaV.equiv_except_resource_version /ObjectMetaV.without_resource_version in Hmeta_eq.
      destruct (KObjectV.objectmeta old_kobj), kmeta, (KObjectV.objectmeta kobj); simpl in *.
      inversion Hmeta_eq; subst. tauto.
    - rewrite Hstatus_eq. exact Hvalid_status_update_parts.
  }
  apply bool_decide_eq_true in Hdecide'.
  unfold P in Hdecide'. destruct Hdecide' as [Hvalid_meta_old Hvalid_status_old].
  assert ((KObjectV.objectmeta kobj <| ObjectMetaV.Namespace' := ObjectMetaV.Namespace' (KObjectV.objectmeta kobj) |>)
    = (KObjectV.objectmeta kobj)) as ->.
  { destruct (KObjectV.objectmeta kobj). done. }
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hold_l1_not_null with "[$Hdeepown_t_old_l $Hdeepown_m_old_l $Hdeepown_s_old_l $Hdeepown_st_old_l]")
    as "Hdeepown_old_l".
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hl1_not_null with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]")
    as "Hdeepown_l".
  iPoseProof (kview.own_auth_valid2 key old_kobj with
    "Hinv_Hown_abs") as "%Hauth_old".
  1: done.
  destruct Hauth_old as (Hkey_old & Hvalid_old_kobj & Huid_old_in &
    Hno_speculative_parent_reference_old & Huid_unique_old).
  iPoseProof (kview.own_auth_extra_valid_forall with "Hinv_Hown_abs")
    as "%Habs_extra_valid".
  assert (KObjectV.extra_valid old_kobj) as Hextra_valid_old.
  { exact (Habs_extra_valid key old_kobj Hlookup_abs). }
  assert (KObjectV.key old_kobj = KObjectV.key kobj) as Hkey_old_new.
  { rewrite <-Hkey_old. exact Hkey_new. }
  assert (ObjectMetaV.valid_update (KObjectV.objectmeta old_kobj)
      (KObjectV.objectmeta kobj)) as Hvalid_meta_update_actual.
  { rewrite /ObjectMetaV.valid_update. split; first (left; exact Hvalid_meta_old).
    split_and!; done. }
  assert (KObjectV.valid_status_update
      (KObjectV.kind kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace')
      (KObjectV.objectmeta old_kobj) (KObjectV.status old_kobj) kobj)
    as Hvalid_status_update_actual.
  { destruct old_kobj, kobj; rewrite /KObjectV.valid_status_update /=;
      rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
        ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
        /ObjectMetaV.valid_update;
      simpl in Hvalid_meta_update_actual, Hvalid_status_old;
      try contradiction; tauto. }
  assert (update_prepared_for_helper
      (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') old_kobj kobj kobj) as Hprepared.
  { rewrite /update_prepared_for_helper. split_and!.
    - right. done.
    - right. exact e0.
    - exact Hkey_old_new.
    - rewrite <-e0.
      destruct kobj as [[tm meta spec status]|[tm meta spec status]|
        [tm meta spec status]|[tm meta spec status]]; destruct meta; done. }
  wp_apply (wp_applyValidationAndDefaultingOnStatusUpdate_ok _ _ _ _ _ _ _
    (KObjectV.kind kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') kobj
    with "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (updated_kobj)
    "(Hdeepown_l & Hdeepown_old_l & %Hvalid_interface_updated & %Hhelper_updated)". wp_auto.
  pose proof Hhelper_updated as (Hhelper_result_status_updated & _).
  assert (update_objects_equiv_except_resource_version updated_kobj updated_kobj)
    as Hequiv_updated_refl.
  { rewrite /update_objects_equiv_except_resource_version
      /ObjectMetaV.equiv_except_resource_version.
    destruct updated_kobj; done. }
  pose proof (Hhelper_result_status_updated (KObjectV.kind kobj) kobj updated_kobj
    Hvalid_old_kobj Hvalid_status_update_actual Hprepared
    Hequiv_updated_refl) as Hstatus_updated_kobj.
  pose proof (applyValidationAndDefaultingOnStatusUpdate_updated_implies_valid
    (KObjectV.kind kobj) (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') old_kobj kobj kobj updated_kobj
    Hvalid_old_kobj Hvalid_status_update_actual Hprepared Hhelper_updated)
    as Hvalid_updated_kobj.
  assert (KObjectV.same_kind kobj updated_kobj ∧
      KObjectV.spec updated_kobj = KObjectV.spec old_kobj ∧
      ObjectStatusV.updated (KObjectV.status kobj) (KObjectV.status updated_kobj) ∧
      (KObjectV.objectmeta updated_kobj).(ObjectMetaV.Name') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ∧
      (KObjectV.objectmeta updated_kobj).(ObjectMetaV.Namespace') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ∧
      (KObjectV.objectmeta updated_kobj).(ObjectMetaV.UID') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ∧
      (KObjectV.objectmeta updated_kobj).(ObjectMetaV.DeletionTimestamp') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp'))
    as (Hsame_kind & Hspec_eq & Hupdated_status & Hname_updated & Hnamespace_updated &
      Huid_updated & Hdeletion_timestamp_updated).
  { destruct (KObjectV.spec old_kobj), kobj, updated_kobj;
      rewrite /KObjectV.status_updated /PodV.status_updated /ReplicaSetV.status_updated
        /PersistentVolumeClaimV.status_updated /StatefulSetV.status_updated /=
        in Hstatus_updated_kobj |- *; try contradiction.
    all: split_and!; try done.
    all: try (f_equal; tauto).
    all: rewrite /ObjectMetaV.updated in Hstatus_updated_kobj; tauto. }
  assert ((KObjectV.objectmeta kobj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta old_kobj).(ObjectMetaV.UID') ∧
      (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') =
        (KObjectV.objectmeta old_kobj).(ObjectMetaV.DeletionTimestamp') ∧
      (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') =
        (KObjectV.objectmeta old_kobj).(ObjectMetaV.Namespace') ∧
      meta_parent_ref (KObjectV.objectmeta old_kobj) =
        meta_parent_ref (KObjectV.objectmeta kobj))
    as (Hinput_uid_old & Hinput_deletion_timestamp_old & Hinput_namespace_old &
      Hinput_parent_ref_old).
  { rewrite /ObjectMetaV.valid_simple_update /meta_parent_ref in Hvalid_meta_old |- *.
    remember (KObjectV.objectmeta old_kobj) as old_meta.
    remember (KObjectV.objectmeta kobj) as input_meta.
    destruct old_meta, input_meta; simpl in *.
    decompose [and] Hvalid_meta_old. subst. done. }
  assert (KObjectV.key old_kobj = KObjectV.key updated_kobj) as Hsame_key.
  { rewrite Hkey_old_new /KObjectV.key.
    rewrite Hname_updated Hnamespace_updated.
    destruct kobj, updated_kobj; simpl in Hsame_kind |- *; try done. }
  assert ((KObjectV.objectmeta updated_kobj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta old_kobj).(ObjectMetaV.UID')) as Huid_updated_old.
  { rewrite Huid_updated. exact Hinput_uid_old. }
  assert ((KObjectV.objectmeta old_kobj).(ObjectMetaV.DeletionTimestamp') =
      (KObjectV.objectmeta updated_kobj).(ObjectMetaV.DeletionTimestamp'))
    as Hdeletion_timestamp_old_updated.
  { rewrite Hdeletion_timestamp_updated. symmetry. exact Hinput_deletion_timestamp_old. }
  assert (obj_parent_ref old_kobj = obj_parent_ref updated_kobj)
    as Hparent_ref_old_updated.
  { rewrite (kobject_status_updated_parent_ref _ _ _ Hstatus_updated_kobj).
    exact Hinput_parent_ref_old. }
  assert ((KObjectV.objectmeta old_kobj).(ObjectMetaV.Namespace') =
      (KObjectV.objectmeta updated_kobj).(ObjectMetaV.Namespace'))
    as Hnamespace_old_updated.
  { rewrite Hnamespace_updated. symmetry. exact Hinput_namespace_old. }
  set P' := ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta old_kobj) = None.
  destruct (bool_decide(P')) eqn:Hdecide''.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
    iPoseProof (own_status_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_status_update with
      "Hinv_Hown_abs Hown_meta_frag Hown_status_frag") as
      "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. symmetry. exact Hkey_new. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    apply bool_decide_eq_false in Hdecide''.
    exfalso. apply Hdecide''. unfold P'.
    rewrite (ObjectMetaV.equiv_except_resource_version_deletion_timestamp _ _ Hmeta_eq).
    exact Hno_deletion_timestamp.
  }
  apply bool_decide_eq_true in Hdecide''. unfold P' in Hdecide''.
  wp_apply (wp_shouldDeleteDuringUpdate_false with "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros "(Hdeepown_l & Hdeepown_old_l)". wp_auto.
  wp_apply (wp_storageObjectDeepEqual with "[$Hdeepown_l $Hdeepown_old_l]").
  { iPureIntro. split_and!. all: done. }
  iIntros (v) "(Hdeepown_i1 & Hdeepown_old_i1 & %Hifv)".
  wp_if_destruct.
  {
    assert (storage_object_normalize updated_kobj = storage_object_normalize old_kobj) as Hstorage_eq.
    { apply Hifv. done. }
    pose proof
      (storage_object_normalize_eq_implies_update_objects_equiv_except_resource_version
        updated_kobj old_kobj Hvalid_updated_kobj Hvalid_old_kobj Hstorage_eq)
      as Hequiv_updated_old.
    pose proof (Hhelper_result_status_updated (KObjectV.kind kobj) kobj old_kobj
      Hvalid_old_kobj Hvalid_status_update_actual Hprepared Hequiv_updated_old)
      as Hstatus_updated_old.
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
    iPoseProof (own_status_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_status_update with
      "Hinv_Hown_abs Hown_meta_frag Hown_status_frag") as
      "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. symmetry. exact Hkey_new. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    assert (kview.mk_meta_frag key uid 1 (KObjectV.objectmeta old_kobj) =
        kview.mk_meta_frag key uid 1 kmeta) as Hfrag_eq.
    { rewrite /kview.mk_meta_frag /ObjectMetaV.equiv_except_resource_version
        in Hmeta_eq |- *.
      rewrite Hmeta_eq. done. }
    iAssert (own_meta_frag γ key uid 1 (KObjectV.objectmeta old_kobj))
      with "[Hown_meta_frag]" as "Hown_meta_frag".
    { rewrite /own_meta_frag /kview.own_meta_frag Hfrag_eq. iExact "Hown_meta_frag". }
    iPoseProof (kview.own_status_exists with "Hinv_Hown_abs Hown_status_frag") as "%Hstatus_found".
    assert (KObjectV.status old_kobj = kstatus) as Hstatus_eq.
    { eapply Hstatus_found; done. }
    iDestruct "Hclose" as "[Hclose_success _]".
    iMod ("Hclose_success" $! old_i1 (KObjectV.spec old_kobj) old_kobj with
      "[Hdeepown_old_i1 Hown_meta_frag Hown_status_frag]") as "HΦ".
	    { iSplit; first (iPureIntro; exact Hvalid_old_kobj).
      iSplit; first (iPureIntro; exact Hstatus_updated_old).
      iFrame "Hdeepown_old_i1 Hown_meta_frag".
      rewrite Hstatus_eq. iFrame. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I)
      with "[Hdeepown_old_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs).
      iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ".
  }
  wp_apply (wp_State__generateNewRVAndUpdate with "[$Hinv_Hstate_used_rv_addr $Hinv_Hown_used_rv]").
  iIntros (rv) "(%Hlookup_phys_used_rv & %Hvalid_rv & Hinv_Hstate_used_rv_addr & Hinv_Hown_used_rv)". wp_auto.
  iPoseProof (KObjectV.deepown_i_yields_deepown_l with "[$Hdeepown_i1]") as "Hdeepown_l". 1: done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null1 & Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  assert (KObjectV.objectmeta_ptr l1 kobj = KObjectV.objectmeta_ptr l1 updated_kobj) as ->.
  { destruct kobj, updated_kobj; simpl in *; simplify_eq; done. }
  wp_apply (wp_SetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_map_insert apimodel.KKey with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null1 with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]")
    as "Hdeepown_l".
  set new_kmeta := (KObjectV.objectmeta updated_kobj <| ObjectMetaV.ResourceVersion' := rv |>).
  set new_kobj := KObjectV.update_objectmeta updated_kobj new_kmeta.
  wp_apply (wp_deepCopy i1 new_kobj with "[Hdeepown_l]").
  { iFrame. iPureIntro. unfold new_kobj, new_kmeta. destruct updated_kobj; done. }
  iIntros (i1') "[Hdeepown_i1' Hdeepown_i1]". wp_auto.
  iApply fupd_wp.
  iMod "Hau" as (key0 uid kmeta kstatus) "H". iNamed "H".
  iPoseProof (own_status_update_frag_identity _ _ _ _ _ _ _ _ _ _ Hvalid_status_update with
    "Hinv_Hown_abs Hown_meta_frag Hown_status_frag") as
    "(%Hkey_eq & %Huid_eq & %Hno_deletion_timestamp)".
  assert (key0 = key) as ->.
  { rewrite Hkey_eq. symmetry. exact Hkey_new. }
  assert (update_objects_equiv_except_resource_version updated_kobj new_kobj)
    as Hequiv_updated_new.
  { unfold new_kobj, new_kmeta, update_objects_equiv_except_resource_version.
    destruct updated_kobj; simpl; split_and!; try done.
    all: rewrite /ObjectMetaV.equiv_except_resource_version
      /ObjectMetaV.without_resource_version; destruct ObjectMeta'; done. }
  pose proof (Hhelper_result_status_updated (KObjectV.kind kobj) kobj new_kobj
    Hvalid_old_kobj Hvalid_status_update_actual Hprepared Hequiv_updated_new)
    as Hstatus_updated_new.
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
  { destruct (KObjectV.spec old_kobj), kobj, new_kobj;
      rewrite /KObjectV.status_updated /PodV.status_updated /ReplicaSetV.status_updated
        /PersistentVolumeClaimV.status_updated /StatefulSetV.status_updated /=
        in Hstatus_updated_new |- *;
      try contradiction; rewrite /ObjectMetaV.updated in Hstatus_updated_new |- *; tauto. }
  assert ((KObjectV.objectmeta new_kobj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta old_kobj).(ObjectMetaV.UID')) as Huid_new_old.
  { rewrite Huid_new. exact Hinput_uid_old. }
  assert ((KObjectV.objectmeta old_kobj).(ObjectMetaV.DeletionTimestamp') =
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp'))
    as Hdeletion_timestamp_old_new.
  { rewrite Hdeletion_timestamp_new. symmetry. exact Hinput_deletion_timestamp_old. }
  assert (obj_parent_ref old_kobj = obj_parent_ref new_kobj) as Hparent_ref_old_new.
  { rewrite (kobject_status_updated_parent_ref _ _ _ Hstatus_updated_new).
    exact Hinput_parent_ref_old. }
  assert ((KObjectV.objectmeta old_kobj).(ObjectMetaV.Namespace') =
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.Namespace')) as Hnamespace_old_new.
  { rewrite Hnamespace_stored_new. symmetry. exact Hinput_namespace_old. }
  assert (kview.valid_k_uid_obj key uid new_kobj) as Hvalid_kuid_new.
  { unfold kview.valid_k_uid_obj.
    split.
    - rewrite Hkey_new /KObjectV.key.
      rewrite Hname_new Hnamespace_stored_new.
      destruct kobj, new_kobj; simpl in Hsame_kind_new |- *; try done.
    - unfold new_kobj, new_kmeta.
      split.
      + rewrite objectmeta_update_objectmeta Huid_eq. symmetry.
        exact Huid_updated.
      + split.
        * pose proof Hvalid_updated_kobj as
            (Hupdated_valid_typemeta & _ & Hupdated_valid_meta & Hupdated_valid_spec &
              Hupdated_valid_status).
          split_and!.
          -- rewrite KObjectV.kind_update_objectmeta KObjectV.typemeta_update_objectmeta.
             exact Hupdated_valid_typemeta.
          -- rewrite objectmeta_update_objectmeta. exact Hvalid_rv.
          -- rewrite KObjectV.kind_update_objectmeta objectmeta_update_objectmeta.
             destruct (KObjectV.objectmeta updated_kobj); simpl in *; done.
          -- rewrite KObjectV.spec_update_objectmeta. exact Hupdated_valid_spec.
          -- rewrite KObjectV.status_update_objectmeta. exact Hupdated_valid_status.
        * apply KObjectV.extra_valid_update_objectmeta.
          rewrite /KObjectV.extra_valid Hspec_eq.
          exact Hextra_valid_old.
  }
  iMod (kview.update_status_kobj_vs old_kobj new_kobj with
    "[$Hinv_Hown_abs] [$Hown_meta_frag] [$Hown_status_frag]")
    as "(Hinv_Hown_abs & Hown_meta_frag & Hown_status_frag)".
  { exact Hvalid_kuid_new. }
  { rewrite -Hdeletion_timestamp_old_new. exact Hdecide''. }
  { intros kind' name' uid' Hparent.
    eapply Hno_speculative_parent_reference_old.
    unfold meta_parent_ref_is in Hparent |- *.
    unfold obj_parent_ref in Hparent_ref_old_new.
    rewrite Hparent_ref_old_new Hnamespace_old_new. exact Hparent. }
  { exact Hlookup_abs. }
  { unfold new_kobj. rewrite KObjectV.spec_update_objectmeta.
    symmetry. exact Hspec_eq. }
  iMod (cview.simple_update_vs key old_kobj new_kobj with "[$Hinv_Hown_children]")
    as "Hinv_Hown_children".
  { done. }
  {
    unfold living_obj_parent_ref, obj_parent_ref.
    rewrite Hdeletion_timestamp_old_new.
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp'));
      [done|].
    exact Hparent_ref_old_new. }
  { symmetry. exact Huid_new_old. }
  iMod (terminating_children.update_same_parent_vs
    γ.(γ_terminating_children) abs_state key old_kobj new_kobj with
    "Hinv_Hown_terminating_children") as
    "Hinv_Hown_terminating_children".
  { exact Hlookup_abs. }
  { unfold terminating_children.terminating_obj_parent_ref, obj_parent_ref.
    rewrite Hdeletion_timestamp_old_new.
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp'));
      [|done].
    exact Hparent_ref_old_new. }
  iMod (deletion_observation.update_vs key old_kobj new_kobj with
    "Hinv_Hown_deletion_observations") as
    "Hinv_Hown_deletion_observations".
  { exact Hlookup_abs. }
  { symmetry. exact Huid_new_old. }
  { intros Hold_terminating.
    rewrite -Hdeletion_timestamp_old_new. exact Hold_terminating. }
  assert (KObjectV.valid new_kobj) as Hvalid_new_kobj.
  { destruct Hvalid_kuid_new as (_ & _ & Hvalid_new_kobj & _). done. }
  iDestruct "Hclose" as "[Hclose_success _]".
  iMod ("Hclose_success" $! i1' (KObjectV.spec old_kobj) new_kobj with
    "[Hdeepown_i1' Hown_meta_frag Hown_status_frag]") as "HΦ".
  { iSplit; first done.
    iSplit; first (iPureIntro; exact Hstatus_updated_new).
    iFrame. }
  iModIntro.
  iAssert (([∗ map] i; obj ∈ <[key:=interface.ok i1]> phys_state; <[key:=new_kobj]> abs_state,
    match i with
    | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
    | interface.nil => False%I
    end)%I) with "[Hdeepown_i1 Hother_rep]" as "Hinv_Hphys_abs_rep".
  { rewrite big_sepM2_insert_delete. iFrame. }
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H".
    iFrame "#". iFrame. iNext. iFrame. iPureIntro. split_and!.
    all: try done.
  }
  iExact "HΦ".
Unshelve.
all: try apply _.
all: try done.
Qed.

Lemma wp_State__update_status γ l kind namespace i kobj key uid kmeta kstatus :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid_status_update" ∷
        ⌜ KObjectV.valid_status_update kind namespace kmeta kstatus kobj ⌝ ∗
      "%Hvalid_simple_update" ∷
        ⌜ ObjectMetaV.valid_simple_update kmeta (KObjectV.objectmeta kobj) ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid 1 kstatus
  }}}
    l @! (go.PointerType apimodel.State) @! "updateStatus" #kind #namespace #(interface.ok i)
  {{{ ret err i' kobj', RET (ret, #err);
      (⌜ err = interface.nil ⌝ ∗
        ⌜ ret = #(interface.ok i') ⌝ ∗
        ⌜ KObjectV.valid kobj' ⌝ ∗
        ∃ old_spec,
        ⌜ KObjectV.status_updated old_spec kobj kobj' ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
        own_status_frag γ key uid 1 (KObjectV.status kobj')) ∨
      (⌜ err ≠ interface.nil ⌝ ∗
        ⌜ ret = #interface.nil ⌝ ∗
        own_meta_frag γ key uid 1 kmeta ∗
        own_status_frag γ key uid 1 kstatus)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__update_status_au.
  iFrame "#". iFrame.
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iFrame.
  iSplit; first done.
  iSplit; first done.
  iSplit.
  - iIntros (i' old_spec kobj') "Hpost".
    iMod "Hmask" as "_".
    iModIntro. iNext.
    iApply ("HΦ" $! #(interface.ok i') interface.nil i' kobj').
    iLeft. iSplit; first done.
    iSplit; first done.
    iDestruct "Hpost" as "($ & Hpost)".
    iExists old_spec. iExact "Hpost".
  - iIntros (err) "Hpost".
    iDestruct "Hpost" as "(%Hconflict & Hown_meta_frag & Hown_status_frag)".
    pose proof (conflict_error_not_nil err Hconflict) as Herr_ne.
    iMod "Hmask" as "_".
    iModIntro. iNext.
    iApply ("HΦ" $! #interface.nil err i kobj).
    iRight. iSplit; first done.
    iSplit; first done.
    iFrame.
Qed.

End proof.
