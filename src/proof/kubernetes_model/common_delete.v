From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common.

(* Lightweight infrastructure shared by the Delete variants and updates
   whose success path may remove an object. *)

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

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
    + intros Hcase.
      destruct Hcase as [Hcase|Hcase].
      * destruct Hcase as [Huid_used0 Huid_not_in0].
        split; [done|].
        intros Huid_in_deleted0.
        apply Huid_not_in0.
        rewrite elem_of_union.
        right. exact Huid_in_deleted0.
      * exfalso. apply Huid_neq. exact Hcase.
    + intros Hcase.
      destruct Hcase as [Huid_used0 Huid_not_in_deleted0].
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

Definition delete_options_preconditions_resource_version_none (options : DeleteOptionsV.t) : Prop :=
  match options.(DeleteOptionsV.Preconditions') with
  | None => True
  | Some preconditions => preconditions.(PreconditionsV.ResourceVersion') = None
  end.

#[global] Instance delete_options_preconditions_resource_version_none_dec options :
  Decision (delete_options_preconditions_resource_version_none options).
Proof.
  unfold delete_options_preconditions_resource_version_none.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|].
  - destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|].
    + right. intros Hcontra. inversion Hcontra.
    + left. done.
  - left. done.
Qed.

Lemma own_meta_frag_equiv_except_resource_version {γ k uid dq meta1 meta2} :
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

Lemma delete_preconditions_match_equiv_except_resource_version m1 m2 options :
  ObjectMetaV.equiv_except_resource_version m1 m2 →
  delete_options_preconditions_resource_version_none options →
  delete_preconditions_match options m2 →
  delete_preconditions_match options m1.
Proof.
  intros Hmeta_eq Hrv_none Hmatch.
  rewrite /delete_preconditions_match /delete_options_preconditions_resource_version_none in Hrv_none, Hmatch |- *.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|]; [|done].
  destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|]; [done|].
  destruct preconditions.(PreconditionsV.UID') as [uid|]; [|done].
  simpl in Hmatch |- *.
  rewrite (ObjectMetaV.equiv_except_resource_version_uid _ _ Hmeta_eq).
  exact Hmatch.
Qed.

Definition delete_preconditions_match_uid (options : DeleteOptionsV.t) obj_uid : Prop :=
  match options.(DeleteOptionsV.Preconditions') with
  | None => True
  | Some preconditions =>
      (match preconditions.(PreconditionsV.UID') with
       | Some uid => uid = obj_uid
       | None => True
       end)
  end.

Lemma delete_preconditions_match_uid_of_match options uid kmeta :
  uid = kmeta.(ObjectMetaV.UID') →
  delete_preconditions_match options kmeta →
  delete_preconditions_match_uid options uid.
Proof.
  intros Huid_eq Hmatch.
  rewrite /delete_preconditions_match /delete_preconditions_match_uid in Hmatch |- *.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|]; [|done].
  destruct preconditions.(PreconditionsV.UID') as [precondition_uid|]; [|done].
  destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|]; simpl in Hmatch;
    rewrite Huid_eq; intuition.
Qed.

Lemma delete_preconditions_match_of_uid_rv_none options uid kmeta :
  uid = kmeta.(ObjectMetaV.UID') →
  delete_options_preconditions_resource_version_none options →
  delete_preconditions_match_uid options uid →
  delete_preconditions_match options kmeta.
Proof.
  intros Huid_eq Hrv_none Huid_match.
  rewrite /delete_options_preconditions_resource_version_none in Hrv_none.
  rewrite /delete_preconditions_match /delete_preconditions_match_uid in Huid_match |- *.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|]; [|done].
  destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|]; [done|].
  destruct preconditions.(PreconditionsV.UID') as [precondition_uid|]; simpl in Huid_match |- *.
  - split; [rewrite <-Huid_eq; done|done].
  - split; done.
Qed.

Definition delete_success_post
  (γ : KubernetesGname) (key : KKey.t) (uid : types.UID.t)
  (parent_key : KKey.t) (parent_uid : types.UID.t)
  (children : gset KKey.t) (kmeta' : ObjectMetaV.t) : iProp Σ :=
  ( (* the object is marked as deleting (DeletionTimestamp is set) but still exists *)
    "Hdeletion_timestamp" ∷ ⌜ kmeta'.(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
    "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta' ∗
    "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
    ∨
    (* the object is deleted *)
    "Hown_tombstone_frag" ∷ own_tombstone_frag γ uid ∗
    "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]})
  )%I.


End proof.
