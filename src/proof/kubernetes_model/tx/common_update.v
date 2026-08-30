From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_update.

(* ResourceVersion plumbing shared by the transaction Update variants. *)

Lemma valid_simple_update_set_resource_version m_old m rv :
  ObjectMetaV.valid_simple_update m_old m →
  ObjectMetaV.valid_simple_update
    m_old (m <| ObjectMetaV.ResourceVersion' := rv |>).
Proof.
  rewrite /ObjectMetaV.valid_simple_update.
  destruct m_old, m; simpl; intuition congruence.
Qed.

Lemma objectmeta_valid_create_set_resource_version kind namespace meta rv :
  ObjectMetaV.valid_create kind namespace meta →
  ObjectMetaV.valid_create kind namespace
    (meta <| ObjectMetaV.ResourceVersion' := rv |>).
Proof.
  destruct meta. done.
Qed.

Lemma objectmeta_valid_update_set_resource_version old_meta input_meta rv :
  ObjectMetaV.valid_update old_meta input_meta →
  ObjectMetaV.valid_update old_meta
    (input_meta <| ObjectMetaV.ResourceVersion' := rv |>).
Proof.
  destruct input_meta.
  intros ([Hsimple | Hrelease] & Hlabels & Hannotations & Howners &
    Hfinalizers & Hmanaged_fields).
  - split.
    + left. apply valid_simple_update_set_resource_version. exact Hsimple.
    + split_and!; done.
  - split.
    + right. exact Hrelease.
    + split_and!; done.
Qed.

Lemma kobject_valid_create_set_resource_version request_kind namespace input rv :
  KObjectV.valid_create request_kind namespace input →
  KObjectV.valid_create request_kind namespace
    (KObjectV.update_objectmeta input
      ((KObjectV.objectmeta input) <| ObjectMetaV.ResourceVersion' := rv |>)).
Proof.
  destruct input as [[tm meta spec status]|[tm meta spec status]|
    [tm meta spec status]|[tm meta spec status]]; simpl;
    rewrite ?/PodV.valid_create ?/ReplicaSetV.valid_create
      ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create;
    intros (Hkind & Hns_nonempty & Hns_valid & Htypemeta & Hmeta & Hspec);
    split_and!; try done;
    apply objectmeta_valid_create_set_resource_version; done.
Qed.

Lemma kobject_valid_update_set_resource_version request_kind namespace old_meta old_spec input rv :
  KObjectV.valid_update request_kind namespace old_meta old_spec input →
  valid_resource_version rv →
  KObjectV.valid_update request_kind namespace old_meta old_spec
    (KObjectV.update_objectmeta input
      ((KObjectV.objectmeta input) <| ObjectMetaV.ResourceVersion' := rv |>)).
Proof.
  intros Hvalid Hrv.
  assert (KObjectV.valid_create request_kind namespace input ∧
      (KObjectV.objectmeta input).(ObjectMetaV.Name') ≠ ""%go ∧
      valid_typemeta (KObjectV.kind input) (KObjectV.typemeta input) ∧
      (KObjectV.objectmeta input).(ObjectMetaV.UID') ≠ ""%go ∧
      valid_resource_version (KObjectV.objectmeta input).(ObjectMetaV.ResourceVersion') ∧
      namespace = (KObjectV.objectmeta input).(ObjectMetaV.Namespace') ∧
      ObjectMetaV.valid_update old_meta (KObjectV.objectmeta input) ∧
      ObjectSpecV.valid_update old_spec (KObjectV.spec input)) as
    (Hcreate & Hname & Htypemeta & Huid & _ & Hnamespace & Hmeta & Hspec).
  { revert Hvalid.
    destruct old_spec, input; rewrite /KObjectV.valid_update /=;
      rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
        ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
        ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
        /KObjectV.valid_create /=;
      try contradiction; tauto. }
  pose proof (kobject_valid_create_set_resource_version
    request_kind namespace input rv Hcreate) as Hcreate_rv.
  assert (ObjectMetaV.valid_update old_meta
      ((KObjectV.objectmeta input) <| ObjectMetaV.ResourceVersion' := rv |>)) as Hmeta_rv.
  { apply objectmeta_valid_update_set_resource_version. exact Hmeta. }
  destruct old_spec, input as [[tm meta spec status]|[tm meta spec status]|
      [tm meta spec status]|[tm meta spec status]]; destruct meta; simpl in *;
    rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
      ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
      ?/PodV.valid_create ?/ReplicaSetV.valid_create
      ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
      /KObjectV.valid_create /= in Hcreate_rv |- *;
    try contradiction; tauto.
Qed.

Lemma kobject_valid_status_update_set_resource_version request_kind namespace old_meta old_status input rv :
  KObjectV.valid_status_update request_kind namespace old_meta old_status input →
  valid_resource_version rv →
  KObjectV.valid_status_update request_kind namespace old_meta old_status
    (KObjectV.update_objectmeta input
      ((KObjectV.objectmeta input) <| ObjectMetaV.ResourceVersion' := rv |>)).
Proof.
  intros Hvalid Hrv.
  assert (ObjectMetaV.valid_update old_meta (KObjectV.objectmeta input)) as Hmeta.
  { destruct old_status, input; rewrite /KObjectV.valid_status_update /= in Hvalid;
      rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
        ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
        in Hvalid;
      try contradiction; tauto. }
  pose proof (objectmeta_valid_update_set_resource_version old_meta
    (KObjectV.objectmeta input) rv Hmeta) as Hmeta_rv.
  destruct old_status, input; rewrite /KObjectV.valid_status_update /= in Hvalid |- *;
    rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
      ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
      /ObjectMetaV.valid_update in Hvalid |- *;
    simpl in Hmeta_rv |- *; try contradiction; tauto.
Qed.

Lemma objectmeta_updated_unset_resource_version_input m rv m' :
  ObjectMetaV.updated (m <| ObjectMetaV.ResourceVersion' := rv |>) m' →
  ObjectMetaV.updated m m'.
Proof.
  rewrite /ObjectMetaV.updated.
  destruct m, m'; simpl; intuition congruence.
Qed.

Lemma kobject_updated_unset_resource_version_input input stored rv :
  KObjectV.updated
    (KObjectV.update_objectmeta input
      ((KObjectV.objectmeta input) <| ObjectMetaV.ResourceVersion' := rv |>))
    stored →
  KObjectV.updated input stored.
Proof.
  destruct input, stored; simpl; try done;
    intros (Htypemeta & Hmeta & Hspec); split_and!; try done.
  all: apply objectmeta_updated_unset_resource_version_input in Hmeta; exact Hmeta.
Qed.

Lemma kobject_status_updated_unset_resource_version_input old_spec input stored rv :
  KObjectV.status_updated old_spec
    (KObjectV.update_objectmeta input
      ((KObjectV.objectmeta input) <| ObjectMetaV.ResourceVersion' := rv |>))
    stored →
  KObjectV.status_updated old_spec input stored.
Proof.
  destruct old_spec, input, stored; simpl; try done;
    intros (Htypemeta & Hmeta & Hspec & Hstatus); split_and!; try done.
  all: apply objectmeta_updated_unset_resource_version_input in Hmeta; exact Hmeta.
Qed.
