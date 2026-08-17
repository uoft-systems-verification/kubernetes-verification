From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common.
From New.proof.k8s_io.apiserver.pkg.registry Require Export rest.

(* Lightweight infrastructure shared by the independent Update variants. *)

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

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

Lemma objectmeta_updated_set_resource_version_deletion_timestamp m m' rv :
  ObjectMetaV.updated m m' →
  ObjectMetaV.DeletionTimestamp'
      (m' <| ObjectMetaV.ResourceVersion' := rv |>) =
    ObjectMetaV.DeletionTimestamp' m.
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

Lemma valid_simple_update_updated_set_resource_version_deletion_timestamp
    m_old m_input m_updated rv :
  ObjectMetaV.valid_simple_update m_old m_input →
  ObjectMetaV.updated m_input m_updated →
  m_old.(ObjectMetaV.DeletionTimestamp') =
    (m_updated <| ObjectMetaV.ResourceVersion' := rv |>).(
      ObjectMetaV.DeletionTimestamp').
Proof.
  rewrite /ObjectMetaV.valid_simple_update /ObjectMetaV.updated.
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
  intros (Hvalid_typemeta & _ & Hvalid_meta & Hvalid_spec &
    Hvalid_status) Hvalid_rv.
  split_and!.
  - rewrite KObjectV.kind_update_objectmeta KObjectV.typemeta_update_objectmeta.
    exact Hvalid_typemeta.
  - rewrite objectmeta_update_objectmeta. done.
  - rewrite KObjectV.kind_update_objectmeta objectmeta_update_objectmeta.
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

End proof.
