From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv common.
From New.proof.k8s_io.apiserver.pkg.registry Require Export rest.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kubernetesModelG Σ}.

Lemma update_own_meta_frag_equiv_except_resource_version {γ k uid dq meta1 meta2} :
  ObjectMetaV.equiv_except_resource_version meta1 meta2 →
  own_meta_frag γ k uid dq meta2 -∗
  own_meta_frag γ k uid dq meta1.
Proof.
  iIntros (Hmeta_eq) "Hown_meta".
  assert (kview.mk_meta_frag k uid dq meta1 = kview.mk_meta_frag k uid dq meta2) as Hfrag_eq.
  { rewrite /kview.mk_meta_frag /ObjectMetaV.equiv_except_resource_version in Hmeta_eq |- *.
    rewrite Hmeta_eq. done. }
  rewrite /own_meta_frag /kview.own_meta_frag Hfrag_eq.
  iExact "Hown_meta".
Qed.

Lemma objectmeta_updated_set_resource_version m m' rv :
  ObjectMetaV.updated m m' →
  ObjectMetaV.updated m (m' <| ObjectMetaV.ResourceVersion' := rv |>).
Proof.
  rewrite /ObjectMetaV.updated.
  destruct m, m'; simpl; intuition congruence.
Qed.

Lemma objectmeta_updated_set_resource_version_uid m m' rv :
  ObjectMetaV.updated m m' →
  ObjectMetaV.UID' (m' <| ObjectMetaV.ResourceVersion' := rv |>) =
    ObjectMetaV.UID' m.
Proof.
  rewrite /ObjectMetaV.updated.
  destruct m, m'; simpl; intuition congruence.
Qed.

Lemma valid_simple_update_updated_set_resource_version_uid m_old m_input m_updated rv :
  ObjectMetaV.valid_simple_update m_old m_input →
  ObjectMetaV.updated m_input m_updated →
  ObjectMetaV.UID' (m_updated <| ObjectMetaV.ResourceVersion' := rv |>) =
    ObjectMetaV.UID' m_old.
Proof.
  rewrite /ObjectMetaV.valid_simple_update /ObjectMetaV.updated.
  destruct m_old, m_input, m_updated; simpl; intuition congruence.
Qed.

Lemma valid_simple_update_updated_set_resource_version_parent_ref m_old m_input m_updated rv :
  ObjectMetaV.valid_simple_update m_old m_input →
  ObjectMetaV.updated m_input m_updated →
  meta_parent_ref m_old =
    meta_parent_ref (m_updated <| ObjectMetaV.ResourceVersion' := rv |>).
Proof.
  rewrite /ObjectMetaV.valid_simple_update /ObjectMetaV.updated /meta_parent_ref.
  destruct m_old, m_input, m_updated; simpl.
  intros Hvalid Hupdated.
  decompose [and] Hvalid. decompose [and] Hupdated. subst.
  done.
Qed.

Lemma valid_simple_update_updated_set_resource_version_no_speculative_parent_reference
    m_old m_input m_updated rv used_uid :
  ObjectMetaV.valid_simple_update m_old m_input →
  ObjectMetaV.updated m_input m_updated →
  no_speculative_parent_reference m_old used_uid →
  no_speculative_parent_reference
    (m_updated <| ObjectMetaV.ResourceVersion' := rv |>) used_uid.
Proof.
  rewrite /ObjectMetaV.valid_simple_update /ObjectMetaV.updated
          /no_speculative_parent_reference /meta_parent_ref_is /meta_parent_ref.
  destruct m_old, m_input, m_updated; simpl.
  intros Hvalid Hupdated Hno_spec kind name uid Hparent.
  decompose [and] Hvalid. decompose [and] Hupdated. subst.
  eapply Hno_spec. done.
Qed.

Lemma key_update_objectmeta_set_resource_version obj rv :
  KObjectV.key
    (KObjectV.update_objectmeta obj
       ((KObjectV.objectmeta obj) <| ObjectMetaV.ResourceVersion' := rv |>)) =
  KObjectV.key obj.
Proof.
  rewrite /KObjectV.key.
  rewrite KObjectV.kind_update_objectmeta objectmeta_update_objectmeta.
  destruct (KObjectV.objectmeta obj); done.
Qed.

Lemma valid_update_objectmeta_set_resource_version obj rv :
  KObjectV.valid obj →
  valid_resource_version rv →
  KObjectV.valid
    (KObjectV.update_objectmeta obj
       ((KObjectV.objectmeta obj) <| ObjectMetaV.ResourceVersion' := rv |>)).
Proof.
  intros (Hvalid_typemeta & _ & Hvalid_meta & Hvalid_spec & Hvalid_status) Hvalid_rv.
  split_and!.
  - rewrite KObjectV.kind_update_objectmeta KObjectV.typemeta_update_objectmeta.
    exact Hvalid_typemeta.
  - rewrite objectmeta_update_objectmeta. done.
  - rewrite objectmeta_update_objectmeta.
    destruct (KObjectV.objectmeta obj); simpl in *; done.
  - rewrite KObjectV.spec_update_objectmeta. done.
  - rewrite KObjectV.status_update_objectmeta. done.
Qed.

Lemma update_tombed_uid_update_eq_used_uid_sub
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

Lemma wp_State__update_au γ l kind namespace i kobj :
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "%Hvalid" ∷ ⌜ KObjectV.valid kobj ⌝ ∗
    "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
    "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    ( |={⊤,∅}=> ∃ key uid kmeta kspec,
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 kspec ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid_meta_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hvalid_spec_update" ∷ ⌜ ObjectSpecV.valid_update kspec (KObjectV.spec kobj) ⌝ ∗
      (* Hno_deletion_timestamp ensures that the update doesn't delete the object *)
      "%Hno_deletion_timestamp" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "Hclose" ∷ (
          ∀ i' err kobj',
            ( ( ⌜ err = interface.nil ⌝ ∗
                ⌜ ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
                ⌜ ObjectSpecV.updated (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
                KObjectV.deepown_i i' kobj' 1 ∗
                own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
                own_spec_frag γ key uid 1 (KObjectV.spec kobj')) ∨
              ( ⌜ err ≠ interface.nil ⌝ ∗
                ⌜ conflict_error err ⌝ ∗
                own_meta_frag γ key uid 1 kmeta ∗
                own_spec_frag γ key uid 1 kspec)
            )
              ={∅,⊤}=∗ ▷ Φ (#i', #err)%V
      )%I
    ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "update" #kind #namespace #i {{ Φ }}.
Proof.
  iIntros (Φ) "(#? & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  wp_method_call. wp_call.
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_deepCopy with "[$Hdeepown_i]"). iIntros (i1) "[Hdeepown_i1 Hdeepown_i]". wp_auto.
  iDestruct "Hdeepown_i1" as (l1) "[%Hvalid_interface Hdeepown_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  rewrite bool_decide_true //. wp_auto.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  wp_apply (wp_EnsureObjectNamespaceMatchesRequestNamespace with "[$Hdeepown_m_l]").
  { iPureIntro. split. 1: done. right. done. }
  iIntros "Hdeepown_m_l". wp_auto.
  rewrite bool_decide_true //. wp_auto.
  wp_apply (wp_GetName_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  assert (ObjectMetaV.Name' (KObjectV.objectmeta kobj) ≠ ""%go) as Hname_not_empty.
  { destruct Hvalid as (_ & _ & Hmeta & _). apply ObjectMetaV.valid_name_nonempty_of_valid. done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_map_get with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
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
    iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
    assert (key0 = key) as ->.
    { unfold key. rewrite Hkind_matches. rewrite Hns_matches. destruct kobj. all: done. }
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
  rewrite Hlookup_phys. wp_auto.
  wp_apply (wp_deepCopy with "[$Hdeepown_old_i]"). iIntros (old_i1) "[Hdeepown_old_i1 Hdeepown_old_i]". wp_auto.
  iDestruct "Hdeepown_old_i1" as (old_l1) "[%Hvalid_interface_old Hdeepown_old_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  rewrite bool_decide_true //. wp_auto.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_old_l") as
    "(Hdeepown_t_old_l & Hdeepown_m_old_l & Hdeepown_s_old_l & Hdeepown_st_old_l)".
  wp_apply (wp_GetUID_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  1: {
    exfalso.
    destruct Hvalid as (_ & _ & Hmeta_valid & _).
    pose proof (ObjectMetaV.valid_uid_of_valid _ Hmeta_valid) as Huid_valid.
    pose proof (valid_uid_non_empty _ Huid_valid) as Huid_nonempty. done.
  }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_GetUID_deepown with "[$Hdeepown_m_old_l]"). iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    exfalso.
    rewrite Huid_eq in Huid_obj. symmetry in Huid_obj. done.
  }
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_old_l]"). iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  {
    exfalso.
    destruct Hvalid as (_ & Hrv_valid & _).
    pose proof (valid_resource_version_non_empty _ Hrv_valid) as Hrv_nonempty. done.
  }
  rewrite bool_decide_false //. wp_auto.
  wp_apply wp_parseResourceVersion.
  { iPureIntro. destruct Hvalid as (_ & Hrv_valid & _). done. }
  iIntros (ret) "_". wp_auto.
  rewrite bool_decide_true //. wp_auto.
  wp_apply (wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  2: {
    wp_apply wp_newUpdateResourceVersionConflictError.
    iIntros (err) "(%Herr_not_nil & %Herr_conflict)". wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iMod ("Hclose" $! interface.nil err kobj with "[Hown_meta_frag Hown_spec_frag]") as "HΦ".
    { iRight. iSplit; first done. iSplit; first done. iFrame. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)%I)
      with "[Hdeepown_old_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs).
      iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply "HΦ".
  }
  set P := ObjectMetaV.valid_simple_update (KObjectV.objectmeta old_kobj) (KObjectV.objectmeta kobj) ∧
    ObjectSpecV.valid_update (KObjectV.spec old_kobj) (KObjectV.spec kobj).
  destruct (bool_decide(P)) eqn:Hdecide'.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. unfold key. destruct kobj. all: done. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (kview.own_spec_exists with "Hinv_Hown_abs Hown_spec_frag") as "%Hspec_found".
    assert (KObjectV.spec old_kobj = kspec) as Hspec_eq.
    { eapply Hspec_found; done. }
    apply bool_decide_eq_false in Hdecide'.
    exfalso. apply Hdecide'. unfold P.
    split.
    - rewrite /ObjectMetaV.valid_simple_update in Hvalid_meta_update |- *.
      rewrite /ObjectMetaV.equiv_except_resource_version /ObjectMetaV.without_resource_version in Hmeta_eq.
      destruct (KObjectV.objectmeta old_kobj), kmeta, (KObjectV.objectmeta kobj); simpl in *.
      inversion Hmeta_eq; subst. tauto.
    - rewrite Hspec_eq. done.
  }
  apply bool_decide_eq_true in Hdecide'.
  unfold P in Hdecide'. destruct Hdecide' as [Hvalid_meta_old Hvalid_spec_old].
  assert ((KObjectV.objectmeta kobj <| ObjectMetaV.Namespace' := ObjectMetaV.Namespace' (KObjectV.objectmeta kobj) |>)
    = (KObjectV.objectmeta kobj)) as ->.
  { destruct (KObjectV.objectmeta kobj). done. }
  iPoseProof (KObjectV.deepown_l_restore with "[$Hdeepown_t_old_l $Hdeepown_m_old_l $Hdeepown_s_old_l $Hdeepown_st_old_l]")
    as "Hdeepown_old_l".
  iPoseProof (KObjectV.deepown_l_restore with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]")
    as "Hdeepown_l".
  iPoseProof (kview.own_auth_valid2 key old_kobj with "Hinv_Hown_abs") as "%Hauth_old".
  1: done.
  destruct Hauth_old as (Hkey_old & Hvalid_old_kobj & Huid_old_in &
    Hno_speculative_parent_reference_old & Huid_unique_old).
  assert (KObjectV.key old_kobj = KObjectV.key kobj) as Hkey_old_new.
  { rewrite <-Hkey_old. exact Hkey_new. }
  wp_apply (wp_applyValidationAndDefaultingOnUpdate with "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (updated_kobj) "(Hdeepown_l & Hdeepown_old_l & %Hvalid_interface_updated & %Hvalid_updated_kobj & %Hsame_key
    & %Htypemeta_eq & %Hupdated_meta & %Hupdated_spec & %Hstatus_eq)". wp_auto.
  rewrite bool_decide_true //. wp_auto.
  set P' := ObjectMetaV.DeletionTimestamp' (KObjectV.objectmeta old_kobj) = None.
  destruct (bool_decide(P')) eqn:Hdecide''.
  2: {
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
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
  wp_apply (wp_shouldDeleteDuringUpdate with "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros "(Hdeepown_l & Hdeepown_old_l)". wp_auto.
  wp_apply (wp_storageObjectDeepEqual with "[$Hdeepown_l $Hdeepown_old_l]").
  { iPureIntro. split_and!. all: done. }
  iIntros (v) "(Hdeepown_i1 & Hdeepown_old_i1 & %Hifv)".
  wp_if_destruct.
  {
    assert (storage_object_normalize updated_kobj = storage_object_normalize old_kobj) as Hstorage_eq.
    { apply Hifv. done. }
    assert (ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta old_kobj))
      as Hupdated_meta_old.
    { eapply storage_object_normalize_objectmeta_updated; done. }
    assert (ObjectSpecV.updated (KObjectV.spec kobj) (KObjectV.spec old_kobj))
      as Hupdated_spec_old.
    { assert (KObjectV.spec updated_kobj = KObjectV.spec old_kobj) as Hspec_updated_old.
      { eapply storage_object_normalize_spec_eq. done. }
      rewrite <-Hspec_updated_old. done. }
    iApply fupd_wp.
    iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
    assert (key0 = key) as ->.
    { rewrite Hkey_eq. symmetry. exact Hkey_new. }
    iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
      as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
    iPoseProof (update_own_meta_frag_equiv_except_resource_version Hmeta_eq with "Hown_meta_frag")
      as "Hown_meta_frag".
    iPoseProof (kview.own_spec_exists with "Hinv_Hown_abs Hown_spec_frag") as "%Hspec_found".
    assert (KObjectV.spec old_kobj = kspec) as Hspec_eq.
    { eapply Hspec_found; done. }
    iMod ("Hclose" $! old_i1 interface.nil old_kobj with
      "[Hdeepown_old_i1 Hown_meta_frag Hown_spec_frag]") as "HΦ".
    { iLeft.
      iSplit; first done.
      iSplit; first done.
      iSplit; first done.
      iFrame "Hdeepown_old_i1 Hown_meta_frag".
      rewrite Hspec_eq. iFrame. }
    iModIntro.
    iAssert (([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)%I)
      with "[Hdeepown_old_i Hother_rep]" as "Hinv_Hphys_abs_rep".
    { rewrite (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs).
      iFrame. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply "HΦ".
  }
  wp_apply (wp_State__generateNewRVAndUpdate with "[$Hinv_Hstate_used_rv_addr $Hinv_Hown_used_rv]").
  iIntros (rv) "(%Hlookup_phys_used_rv & %Hvalid_rv & Hinv_Hstate_used_rv_addr & Hinv_Hown_used_rv)". wp_auto.
  iPoseProof (KObjectV.deepown_i_yields_deepown_l with "[$Hdeepown_i1]") as "Hdeepown_l". 1: done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  assert (KObjectV.objectmeta_ptr l1 kobj = KObjectV.objectmeta_ptr l1 updated_kobj) as ->.
  { destruct kobj, updated_kobj; simpl in *; simplify_eq; done. }
  wp_apply (wp_SetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_map_insert with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]")
    as "Hdeepown_l".
  set new_kmeta := (KObjectV.objectmeta updated_kobj <| ObjectMetaV.ResourceVersion' := rv |>).
  set new_kobj := KObjectV.update_objectmeta updated_kobj new_kmeta.
  wp_apply (wp_deepCopy i1 new_kobj with "[Hdeepown_l]").
  { iFrame. iPureIntro. unfold new_kobj, new_kmeta. destruct updated_kobj; done. }
  iIntros (i1') "[Hdeepown_i1' Hdeepown_i1]". wp_auto.
  iApply fupd_wp.
  iMod "Hau" as (key0 uid kmeta kspec) "H". iNamed "H".
  assert (key0 = key) as ->.
  { rewrite Hkey_eq. symmetry. exact Hkey_new. }
  assert (kview.valid_k_uid_obj key uid new_kobj) as Hvalid_kuid_new.
  { unfold kview.valid_k_uid_obj.
    split_and!.
    - unfold new_kobj, new_kmeta.
      rewrite key_update_objectmeta_set_resource_version.
      rewrite <- Hsame_key. done.
    - unfold new_kobj, new_kmeta.
      rewrite objectmeta_update_objectmeta.
      rewrite Huid_eq.
      symmetry. eapply objectmeta_updated_set_resource_version_uid. done.
    - unfold new_kobj, new_kmeta.
      eapply valid_update_objectmeta_set_resource_version; done.
  }
  iMod (kview.update_kobj_vs old_kobj new_kobj with
    "[$Hinv_Hown_abs] [$Hown_meta_frag] [$Hown_spec_frag]")
    as "(Hinv_Hown_abs & Hown_meta_frag & Hown_spec_frag)".
  { exact Hvalid_kuid_new. }
  { unfold new_kobj, new_kmeta.
    rewrite objectmeta_update_objectmeta.
    eapply valid_simple_update_updated_set_resource_version_no_speculative_parent_reference;
      [exact Hvalid_meta_old|exact Hupdated_meta|exact Hno_speculative_parent_reference_old]. }
  { exact Hlookup_abs. }
  { unfold new_kobj, new_kmeta.
    rewrite KObjectV.status_update_objectmeta. symmetry. done. }
  iMod (cview.simple_update_vs key old_kobj new_kobj with "[$Hinv_Hown_children]")
    as "Hinv_Hown_children".
  { done. }
  { unfold new_kobj, new_kmeta, obj_parent_ref.
    rewrite objectmeta_update_objectmeta.
    eapply valid_simple_update_updated_set_resource_version_parent_ref; done. }
  { unfold new_kobj, new_kmeta.
    rewrite objectmeta_update_objectmeta.
    symmetry. eapply valid_simple_update_updated_set_resource_version_uid; done. }
  iMod ("Hclose" $! i1' interface.nil new_kobj with
    "[Hdeepown_i1' Hown_meta_frag Hown_spec_frag]") as "HΦ".
  { iLeft.
    iSplit; first done.
    iSplit.
    { iPureIntro. unfold new_kobj, new_kmeta.
      rewrite objectmeta_update_objectmeta.
      eapply objectmeta_updated_set_resource_version; done. }
    iSplit.
    { iPureIntro. unfold new_kobj.
      rewrite KObjectV.spec_update_objectmeta. done. }
    iFrame. }
  iModIntro.
  iAssert (([∗ map] i; obj ∈ <[key:=i1]> phys_state; <[key:=new_kobj]> abs_state,
    KObjectV.deepown_i i obj 1)%I) with "[Hdeepown_i1 Hother_rep]" as "Hinv_Hphys_abs_rep".
  { rewrite big_sepM2_insert_delete. iFrame. }
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H".
    iFrame "#". iFrame. iPureIntro. split_and!.
    all: try done.
    eapply update_tombed_uid_update_eq_used_uid_sub; [done|done|].
    unfold new_kobj, new_kmeta.
    rewrite objectmeta_update_objectmeta.
    eapply valid_simple_update_updated_set_resource_version_uid; done.
  }
  iApply "HΦ".
Qed.

Lemma wp_State__update γ l kind namespace i kobj key uid kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid kobj ⌝ ∗
      "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
      "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid_meta_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hvalid_spec_update" ∷ ⌜ ObjectSpecV.valid_update kspec (KObjectV.spec kobj) ⌝ ∗
      "%Hno_deletion_timestamp" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 kspec
  }}}
    l @ (ptrT.id apimodel.State.id) @ "update" #kind #namespace #i
  {{{ i' err kobj', RET (#i', #err);
      (⌜ err = interface.nil ⌝ ∗
        ⌜ ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
        ⌜ ObjectSpecV.updated (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
        own_spec_frag γ key uid 1 (KObjectV.spec kobj')) ∨
      (⌜ err ≠ interface.nil ⌝ ∗
        own_meta_frag γ key uid 1 kmeta ∗
        own_spec_frag γ key uid 1 kspec)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__update_au.
  iFrame "#". iFrame "%". iFrame.
  iApply fupd_mask_intro.
  { Timeout 5 set_solver. }
  iIntros "Hmask".
  iIntros (i' err kobj') "Hpost".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! i' err kobj').
  iDestruct "Hpost" as "[Hpost|Hpost]".
  - iLeft. iExact "Hpost".
  - iRight. iDestruct "Hpost" as "($ & _ & $ & $)".
Qed.

End proof.
