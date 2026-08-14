From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_update.
From New.proof.kubernetes_model Require Import common_delete.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(* Atomic update contract for releasing an object from its controller parent.
   The request changes only metadata: its spec is exactly the value currently
   stored. Ordinary update preserves status, so status ownership can remain
   framed around this contract. The parent relation and [own_children_frag]
   are updated atomically with the object. *)
Lemma wp_State__update_release_au γ l kind namespace i kobj parent_key parent_uid dq :
  ∀ Φ,
  is_pkg_init apimodel ∗
  is_kubernetes γ l ∗
  "%Hvalid" ∷ ⌜ KObjectV.valid_named_create kind namespace kobj ⌝ ∗
  "%Huid_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
  "%Hrv_valid" ∷ ⌜ valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion') ⌝ ∗
  "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
  "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
  "%Hnew_parent" ∷ ⌜ obj_parent_ref kobj = None ⌝ ∗
  "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
  ( |={⊤,∅}=> ∃ key uid old_meta old_spec children,
    "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 old_meta ∗
    "Hown_spec_frag" ∷ own_spec_frag γ key uid dq old_spec ∗
    "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
    "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
    "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
    "%Hold_parent" ∷ ⌜ meta_parent_ref old_meta = Some (parent_key, parent_uid) ⌝ ∗
    "%Hchild" ∷ ⌜ key ∈ children ⌝ ∗
    "%Howner_references_only" ∷
      (* The request differs from the stored metadata only in owner
         references. ResourceVersion is omitted because metadata fragments
         abstract over that server-managed field. *)
      ⌜ ObjectMetaV.equiv_except_resource_version
          (old_meta <| ObjectMetaV.OwnerReferences' := (KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences') |>)
          (KObjectV.objectmeta kobj) ⌝ ∗
    "%Hspec_eq" ∷ ⌜ KObjectV.spec kobj = old_spec ⌝ ∗
    "Hclose" ∷ (
      (∀ i' kobj',
        ( "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
          "%Hsame_kind" ∷ ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
          "%Hmeta_updated" ∷ ⌜ ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
          "%Hspec_unchanged" ∷ ⌜ KObjectV.spec kobj' = old_spec ⌝ ∗
          "%Hparent_released" ∷ ⌜ obj_parent_ref kobj' = None ⌝ ∗
          "%Hkey_eq'" ∷ ⌜ KObjectV.key kobj' = key ⌝ ∗
          "%Huid_eq'" ∷ ⌜ (KObjectV.objectmeta kobj').(ObjectMetaV.UID') = uid ⌝ ∗ 
          "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
          "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]}))
        ={∅,⊤}=∗ ▷ Φ (#(interface.ok i'), #interface.nil)%V) ∧
      (∀ err,
        ( "%Hconflict" ∷ ⌜ conflict_error err ⌝ ∗
          "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 old_meta ∗
          "Hown_spec_frag" ∷ own_spec_frag γ key uid dq old_spec ∗
          "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children)
        ={∅,⊤}=∗ ▷ Φ (#interface.nil, #err)%V)
    )%I
  ) -∗ WP l @! (go.PointerType apimodel.State) @! "update" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
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
  wp_apply (wp_GetName_deepown with "[$Hdeepown_m_l]").
  iIntros "Hdeepown_m_l". wp_auto.
  assert (ObjectMetaV.Name' (KObjectV.objectmeta kobj) ≠ ""%go)
    as Hname_not_empty.
  { pose proof Hvalid as Hvalid_copy.
    destruct Hvalid_copy as (_ & _ & Hmeta & _).
    unfold ObjectMetaV.valid_named_create in Hmeta. tauto. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_map_lookup2 apimodel.KKey (go.InterfaceType [])
    with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
  iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq.
  set key := {|
    KKey.Kind' := kind;
    KKey.Name' := ObjectMetaV.Name' (KObjectV.objectmeta kobj);
    KKey.Namespace' := namespace
  |}.
  assert (key = KObjectV.key kobj) as Hkey_new.
  { unfold key. rewrite Hkind_matches Hns_matches. destruct kobj; done. }
  assert (namespace =
    (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace')) as Hnamespace_new.
  { done. }
  destruct (bool_decide (is_Some (phys_state !! key))) eqn:Hdecide.
  2: {
    apply bool_decide_eq_false in Hdecide.
    assert (phys_state !! key = None) as Hlookup_phys_none.
    { destruct (phys_state !! key) as [i'|] eqn:Hlookup_phys; [|done].
      exfalso. apply Hdecide. done. }
    assert (abs_state !! key = None) as Hlookup_abs.
    { apply not_elem_of_dom. rewrite <-Hdom_eq.
      apply not_elem_of_dom. done. }
    iApply fupd_wp.
    iMod "Hau" as (key0 uid old_meta old_spec children) "H". iNamed "H".
    assert (key0 = key) as ->.
    { unfold key. rewrite Hkind_matches Hns_matches.
      destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists with
      "Hinv_Hown_abs Hown_meta_frag")
      as "(%obj & %Hlookup_abs' & %Huid_obj & %Hmeta_eq & %Huid_in)".
    assert (abs_state !! key ≠ None) as Hlookup_abs''.
    { intros Hnone. rewrite Hlookup_abs' in Hnone. done. }
    exfalso. done.
  }
  assert (∃ old_i, phys_state !! key = Some old_i)
    as [old_i Hlookup_phys].
  { apply bool_decide_eq_true in Hdecide. done. }
  assert (∃ old_kobj, abs_state !! key = Some old_kobj)
    as [old_kobj Hlookup_abs].
  { apply elem_of_dom. rewrite <-Hdom_eq.
    apply elem_of_dom. eexists. done. }
  iDestruct (big_sepM2_delete _ phys_state abs_state key _ _
    Hlookup_phys Hlookup_abs with "Hinv_Hphys_abs_rep")
    as "(Hdeepown_old_i & Hother_rep)".
  destruct old_i as [old_i|].
  2: { iExFalso. iExact "Hdeepown_old_i". }
  rewrite Hlookup_phys. wp_auto.
  wp_apply (wp_deepCopy old_i old_kobj with "[Hdeepown_old_i]").
  { iFrame "#". iExact "Hdeepown_old_i". }
  iIntros (old_i1) "[Hdeepown_old_i1 Hdeepown_old_i]". wp_auto.
  iDestruct "Hdeepown_old_i1" as
    (old_l1) "[%Hvalid_interface_old Hdeepown_old_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_old_l") as
    "(%Hold_l1_not_null & Hdeepown_t_old_l & Hdeepown_m_old_l &
      Hdeepown_s_old_l & Hdeepown_st_old_l)".
  wp_apply (wp_GetUID_deepown with "[$Hdeepown_m_l]").
  iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  1: { exfalso. done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_GetUID_deepown with "[$Hdeepown_m_old_l]").
  iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid old_meta old_spec children) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists2 with
      "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (kview.own_meta_living Hlookup_abs with
      "Hinv_Hown_abs Hown_meta_frag") as "%Hold_living".
    exfalso. rewrite Huid_eq in Huid_obj. symmetry in Huid_obj. done.
  }
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
    pose proof (conflict_error_not_nil err Herr_conflict)
      as Herr_not_nil.
    wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (key0 uid old_meta old_spec children) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iDestruct "Hclose" as "[_ Hclose_err]".
    iMod ("Hclose_err" $! err with
      "[Hown_meta_frag Hown_spec_frag Hown_children_frag]")
      as "HΦ".
    { iFrame. iPureIntro. exact Herr_conflict. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I) with "[Hdeepown_old_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _
        Hlookup_phys Hlookup_abs). iFrame. }
    iCombineNamed "Hinv_*" as "H".
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l)
      with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ".
  }
  set P :=
    ObjectMetaV.equiv_except_resource_version
      ((KObjectV.objectmeta old_kobj) <|
        ObjectMetaV.OwnerReferences' :=
          (KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences') |>)
      (KObjectV.objectmeta kobj) ∧
    KObjectV.spec old_kobj = KObjectV.spec kobj ∧
    meta_parent_ref (KObjectV.objectmeta old_kobj) =
      Some (parent_key, parent_uid).
  destruct (Classical_Prop.classic P) as [Hdecide'|Hdecide'].
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid old_meta old_spec children) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists2 with
      "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (kview.own_meta_living Hlookup_abs with
      "Hinv_Hown_abs Hown_meta_frag") as "%Hold_living".
    iPoseProof (kview.own_spec_exists with
      "Hinv_Hown_abs Hown_spec_frag") as "%Hspec_found".
    assert (KObjectV.spec old_kobj = old_spec) as Hstored_spec_eq.
    { eapply Hspec_found; done. }
    exfalso. apply Hdecide'. unfold P.
    split_and!.
    - rewrite /ObjectMetaV.equiv_except_resource_version
        /ObjectMetaV.without_resource_version in
        Hmeta_eq Howner_references_only |- *.
      destruct (KObjectV.objectmeta old_kobj), old_meta,
        (KObjectV.objectmeta kobj); simpl in *.
      inversion Hmeta_eq; subst. done.
    - congruence.
    - rewrite /ObjectMetaV.equiv_except_resource_version
        /ObjectMetaV.without_resource_version in Hmeta_eq.
      rewrite /meta_parent_ref in Hold_parent |- *.
      destruct (KObjectV.objectmeta old_kobj), old_meta; simpl in *.
      inversion Hmeta_eq; subst. done.
  }
  unfold P in Hdecide'.
  destruct Hdecide' as
    (Howner_references_only_old & Hspec_old & Hold_parent_old).
  assert ((KObjectV.objectmeta kobj <|
    ObjectMetaV.Namespace' :=
      ObjectMetaV.Namespace' (KObjectV.objectmeta kobj) |>) =
    KObjectV.objectmeta kobj) as ->.
  { destruct (KObjectV.objectmeta kobj). done. }
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hold_l1_not_null with
    "[$Hdeepown_t_old_l $Hdeepown_m_old_l $Hdeepown_s_old_l
      $Hdeepown_st_old_l]") as "Hdeepown_old_l".
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hl1_not_null with
    "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]")
    as "Hdeepown_l".
  iPoseProof (kview.own_auth_valid2 key old_kobj with
    "Hinv_Hown_abs") as "%Hauth_old". 1: done.
  destruct Hauth_old as
    (Hkey_old & Hvalid_old_kobj & Huid_old_in &
      Hno_speculative_parent_reference_old & Huid_unique_old).
  assert (KObjectV.key old_kobj = KObjectV.key kobj) as Hkey_old_new.
  { rewrite <-Hkey_old. exact Hkey_new. }
  wp_apply (wp_applyValidationAndDefaultingOnUpdate with
    "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; try done.
    - right. exact Howner_references_only_old.
    - rewrite <-Hspec_old.
      destruct (KObjectV.spec old_kobj); simpl.
      + apply PodSpecV.valid_update_refl.
      + apply ReplicaSetSpecV.valid_update_refl.
      + apply PersistentVolumeClaimSpecV.valid_update_refl.
      + apply StatefulSetSpecV.valid_update_refl. }
  iIntros (updated_kobj)
    "(Hdeepown_l & Hdeepown_old_l & %Hvalid_interface_updated &
      %Hvalid_updated_kobj & %Hsame_key & %Htypemeta_eq &
      %Hupdated_meta & %Hupdated_spec & %Hspec_eq_if_unchanged &
      %Hstatus_eq)".
  assert (KObjectV.spec updated_kobj = KObjectV.spec old_kobj)
    as Hspec_updated_old.
  { apply Hspec_eq_if_unchanged. symmetry. exact Hspec_old. }
  wp_auto.
  wp_apply (wp_shouldDeleteDuringUpdate_general with
    "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (should_delete)
    "(Hdeepown_l & Hdeepown_old_l & %Hshould_delete)".
  destruct should_delete; wp_auto.
  {
    iApply fupd_wp.
    iMod "Hau" as
      (key0 uid old_meta old_spec children) "H".
    iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. symmetry. exact Hkey_new. }
    iPoseProof (kview.own_meta_living Hlookup_abs with
      "Hinv_Hown_abs Hown_meta_frag") as "%Hold_living".
    exfalso. apply (Hshould_delete eq_refl). exact Hold_living.
  }
  wp_apply (wp_storageObjectDeepEqual with
    "[$Hdeepown_l $Hdeepown_old_l]").
  { iPureIntro. split_and!; done. }
  iIntros (v) "(Hdeepown_i1 & Hdeepown_old_i1 & %Hifv)".
  wp_if_destruct.
  {
    assert (storage_object_normalize updated_kobj =
      storage_object_normalize old_kobj) as Hstorage_eq.
    { apply Hifv. done. }
    assert (meta_parent_ref (KObjectV.objectmeta updated_kobj) =
      meta_parent_ref (KObjectV.objectmeta old_kobj)) as Hparent_storage.
    { assert (KObjectV.objectmeta
          (storage_object_normalize updated_kobj) =
        KObjectV.objectmeta
          (storage_object_normalize old_kobj)) as Hnormalized.
      { rewrite Hstorage_eq. done. }
      rewrite /storage_object_normalize
        !objectmeta_update_objectmeta in Hnormalized.
      rewrite /meta_parent_ref.
      destruct (KObjectV.objectmeta updated_kobj),
        (KObjectV.objectmeta old_kobj); simpl in *.
      inversion Hnormalized. done. }
    assert (meta_parent_ref (KObjectV.objectmeta updated_kobj) = None)
      as Hupdated_parent_none.
    { rewrite /ObjectMetaV.updated in Hupdated_meta.
      rewrite /obj_parent_ref /meta_parent_ref in Hnew_parent |- *.
      destruct (KObjectV.objectmeta kobj),
        (KObjectV.objectmeta updated_kobj); simpl in *.
      decompose [and] Hupdated_meta. subst. done. }
    rewrite Hold_parent_old in Hparent_storage.
    congruence.
  }
  wp_apply (wp_State__generateNewRVAndUpdate with
    "[$Hinv_Hstate_used_rv_addr $Hinv_Hown_used_rv]").
  iIntros (rv)
    "(%Hlookup_phys_used_rv & %Hvalid_rv &
      Hinv_Hstate_used_rv_addr & Hinv_Hown_used_rv)".
  wp_auto.
  iPoseProof (KObjectV.deepown_i_yields_deepown_l with
    "[$Hdeepown_i1]") as "Hdeepown_l". 1: done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null1 & Hdeepown_t_l & Hdeepown_m_l &
      Hdeepown_s_l & Hdeepown_st_l)".
  assert (KObjectV.objectmeta_ptr l1 kobj =
    KObjectV.objectmeta_ptr l1 updated_kobj) as ->.
  { destruct kobj, updated_kobj; simpl in *; simplify_eq; done. }
  wp_apply (wp_SetResourceVersion_deepown with "[$Hdeepown_m_l]").
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_map_insert apimodel.KKey with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null1 with
    "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]")
    as "Hdeepown_l".
  set new_kmeta :=
    (KObjectV.objectmeta updated_kobj <|
      ObjectMetaV.ResourceVersion' := rv |>).
  set new_kobj := KObjectV.update_objectmeta updated_kobj new_kmeta.
  wp_apply (wp_deepCopy i1 new_kobj with "[Hdeepown_l]").
  { iFrame. iPureIntro. unfold new_kobj, new_kmeta.
    destruct updated_kobj; done. }
  iIntros (i1') "[Hdeepown_i1' Hdeepown_i1]". wp_auto.
  iApply fupd_wp.
  iMod "Hau" as (key0 uid old_meta old_spec children) "H". iNamed "H".
  assert (key0 = key) as ->.
  { rewrite Hkey_eq. symmetry. exact Hkey_new. }
  iPoseProof (kview.own_meta_exists2 with
    "Hinv_Hown_abs Hown_meta_frag")
    as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
  iPoseProof (kview.own_meta_living Hlookup_abs with
    "Hinv_Hown_abs Hown_meta_frag") as "%Hold_living".
  iPoseProof (kview.own_spec_exists with
    "Hinv_Hown_abs Hown_spec_frag") as "%Hspec_found".
  assert (KObjectV.spec old_kobj = old_spec) as Hstored_spec_eq.
  { eapply Hspec_found; done. }
  assert (kview.valid_k_uid_obj key uid new_kobj)
    as Hvalid_kuid_new.
  { unfold kview.valid_k_uid_obj.
    split.
    - unfold new_kobj, new_kmeta.
      rewrite key_update_objectmeta_set_resource_version.
      rewrite <-Hsame_key. done.
    - split.
      + unfold new_kobj, new_kmeta.
        rewrite objectmeta_update_objectmeta Huid_eq.
        symmetry. eapply objectmeta_updated_set_resource_version_uid.
        done.
      + unfold new_kobj, new_kmeta.
        eapply valid_update_objectmeta_set_resource_version; done.
  }
  assert (obj_parent_ref new_kobj = None) as Hnew_parent_none.
  { unfold new_kobj, new_kmeta, obj_parent_ref.
    rewrite objectmeta_update_objectmeta.
    rewrite /ObjectMetaV.updated in Hupdated_meta.
    rewrite /obj_parent_ref /meta_parent_ref in Hnew_parent |- *.
    destruct (KObjectV.objectmeta kobj),
      (KObjectV.objectmeta updated_kobj); simpl in *.
    decompose [and] Hupdated_meta. subst. done. }
  iPoseProof (kview.own_meta_living Hlookup_abs with
    "Hinv_Hown_abs Hown_meta_frag") as "%Hold_deletion_timestamp_none".
  assert ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp') =
      None) as Hnew_deletion_timestamp_none.
  { assert (Hold_meta_none : old_meta.(ObjectMetaV.DeletionTimestamp') = None).
    { rewrite <-(ObjectMetaV.equiv_except_resource_version_deletion_timestamp
        _ _ Hmeta_eq). exact Hold_deletion_timestamp_none. }
    assert (Hrequest_none :
        (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') = None).
    { pose proof (ObjectMetaV.equiv_except_resource_version_deletion_timestamp
        _ _ Howner_references_only) as Hdt.
      change (ObjectMetaV.DeletionTimestamp' old_meta =
        ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta kobj)) in Hdt.
      rewrite -Hdt. exact Hold_meta_none. }
    unfold new_kobj, new_kmeta. rewrite objectmeta_update_objectmeta.
    rewrite (objectmeta_updated_set_resource_version_deletion_timestamp
      _ _ _ Hupdated_meta).
    exact Hrequest_none. }
  iMod (kview.update_meta_kobj_vs old_kobj new_kobj with
    "[$Hinv_Hown_abs] [$Hown_meta_frag]")
    as "(Hinv_Hown_abs & Hown_meta_frag)".
  { exact Hvalid_kuid_new. }
  { exact Hnew_deletion_timestamp_none. }
  { unfold no_speculative_parent_reference.
    intros kind' name' uid' Hparent.
    unfold meta_parent_ref_is in Hparent.
    unfold obj_parent_ref in Hnew_parent_none.
    rewrite Hnew_parent_none in Hparent. done. }
  { exact Hlookup_abs. }
  { unfold new_kobj. rewrite KObjectV.spec_update_objectmeta.
    symmetry. exact Hspec_updated_old. }
  { unfold new_kobj. rewrite KObjectV.status_update_objectmeta.
    symmetry. exact Hstatus_eq. }
  iPoseProof (cview.own_auth_frag_lookup key old_kobj Hlookup_abs Hchild with
    "Hinv_Hown_children Hown_children_frag") as "%Hold_living_parent".
  assert (Hold_terminating_parent_none :
      terminating_children.terminating_obj_parent_ref old_kobj = None).
  { unfold terminating_children.terminating_obj_parent_ref.
    rewrite Hold_deletion_timestamp_none. done. }
  assert (Hnew_terminating_parent_none :
      terminating_children.terminating_obj_parent_ref new_kobj = None).
  { unfold terminating_children.terminating_obj_parent_ref.
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp'));
      [exact Hnew_parent_none|done]. }
  iMod (cview.release_child_vs key old_kobj new_kobj with
    "[$Hinv_Hown_children] [$Hown_children_frag]")
    as "(Hinv_Hown_children & Hown_children_frag)".
  { exact Hlookup_abs. }
  { exact Hold_living_parent. }
  { unfold living_obj_parent_ref.
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp'));
      [done|exact Hnew_parent_none]. }
  { unfold new_kobj, new_kmeta.
    rewrite objectmeta_update_objectmeta.
    rewrite Huid_obj Huid_eq.
    symmetry. eapply objectmeta_updated_set_resource_version_uid.
    done. }
  iMod (terminating_children.update_same_parent_vs
    γ.(γ_terminating_children) abs_state key old_kobj new_kobj with
    "Hinv_Hown_terminating_children") as
    "Hinv_Hown_terminating_children".
  { exact Hlookup_abs. }
  { rewrite Hold_terminating_parent_none Hnew_terminating_parent_none. done. }
  iMod (deletion_observation.update_vs key old_kobj new_kobj with
    "Hinv_Hown_deletion_observations") as
    "Hinv_Hown_deletion_observations".
  { exact Hlookup_abs. }
  { unfold new_kobj, new_kmeta. rewrite objectmeta_update_objectmeta.
    rewrite Huid_obj Huid_eq. symmetry.
    eapply objectmeta_updated_set_resource_version_uid. done. }
  { intros Hold_terminating.
    exfalso. apply Hold_terminating. exact Hold_deletion_timestamp_none. }
  assert (KObjectV.same_kind kobj new_kobj) as Hsame_kind_new.
  { unfold new_kobj.
    destruct kobj, updated_kobj; simpl in *; simplify_eq; done. }
  iClear "Hown_meta_frag Hown_spec_frag".
  iDestruct "Hclose" as "[Hclose_success _]".
  iMod ("Hclose_success" $! i1' new_kobj with
    "[Hdeepown_i1' Hown_children_frag]") as "HΦ".
  { iSplit.
    { iPureIntro. unfold new_kobj, new_kmeta.
      eapply valid_update_objectmeta_set_resource_version; done. }
    iSplit; first done.
    iSplit.
    { iPureIntro. unfold new_kobj, new_kmeta.
      rewrite objectmeta_update_objectmeta.
      eapply objectmeta_updated_set_resource_version. done. }
    iSplit.
    { iPureIntro. unfold new_kobj.
      rewrite KObjectV.spec_update_objectmeta.
      rewrite Hspec_updated_old Hstored_spec_eq. done. }
    iSplit; first done.
    iSplit.
    { iPureIntro. unfold new_kobj, new_kmeta.
      rewrite key_update_objectmeta_set_resource_version.
      rewrite <-Hsame_key. rewrite Hkey_old. done. }
    iSplit.
    { iPureIntro. unfold new_kobj, new_kmeta.
      rewrite objectmeta_update_objectmeta Huid_eq.
      eapply objectmeta_updated_set_resource_version_uid. done. }
    iFrame "Hdeepown_i1' Hown_children_frag". }
  iModIntro.
  iAssert (([∗ map] i; obj ∈
      <[key:=interface.ok i1]> phys_state;
      <[key:=new_kobj]> abs_state,
      match i with
    | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
    | interface.nil => False%I
    end)%I) with "[Hdeepown_i1 Hother_rep]" as "Hinv_Hphys_abs_rep".
  { rewrite big_sepM2_insert_delete. iFrame. }
  iCombineNamed "Hinv_*" as "H".
  rewrite return_val_unseal /return_val_def. wp_auto.
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l)
    with "[$Hown_Mutex H]").
  { iNamed "H". iFrame "#". iFrame.
    iPureIntro. split_and!. all: try done.
  }
  iExact "HΦ".
Unshelve. all: try tc_solve. all: try apply _. all: try exact sem.
Qed.

(* TODO: have an AU version of this lemma *)
(** The terminating release path supplies no strong kview fragment. It can
    therefore distinguish only the absent/reused/same-UID cases, and a stale
    same-UID request is allowed to fail validation. *)
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
  wp_start as "H".
  iNamed "H". iNamed "Hkinv".
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
    iCombineNamed "Hinv_*" as "H".
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply ("HΦ" $! interface.nil err). iRight. iPureIntro. right. done. }
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
    iApply ("HΦ" $! interface.nil err). iRight. iPureIntro. left. done. }
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
    iApply ("HΦ" $! interface.nil err). iRight. iPureIntro. left. done. }
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
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply ("HΦ" $! interface.nil (interface.ok err_ok)). iRight. iPureIntro. right. done. }
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
    iCombineNamed "Hinv_*" as "H".
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply ("HΦ" $! (interface.ok i1) interface.nil). iLeft. iExists i1, updated_kobj. iFrame.
    iPureIntro. split_and!; try done.
    destruct kobj, updated_kobj; simpl in *; done. }
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
    iCombineNamed "Hinv_*" as "H".
    rewrite return_val_unseal /return_val_def. wp_auto.
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply ("HΦ" $! (interface.ok old_i1) interface.nil). iLeft. iExists old_i1, old_kobj. iFrame.
    iPureIntro. split_and!; try done.
    destruct kobj, updated_kobj, old_kobj; simpl in *; try done;
      unfold storage_object_normalize in Hsame; simpl in Hsame; congruence. }
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
  iCombineNamed "Hinv_*" as "H".
  rewrite return_val_unseal /return_val_def. wp_auto.
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#". done. }
  iApply ("HΦ" $! (interface.ok i1') interface.nil). iLeft. iExists i1', new_kobj. iFrame.
  iPureIntro. split_and!; try done.
  unfold new_kobj. destruct kobj, updated_kobj; simpl in *; done.
Unshelve. all: try tc_solve. all: try apply _. all: try exact sem. all: try done.
Qed.

End proof.
