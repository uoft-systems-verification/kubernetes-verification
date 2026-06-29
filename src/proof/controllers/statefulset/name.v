From New.proof Require Import prelude empty_ffi.
From New.proof.string Require Export prefix_suffix.
From New.proof Require Export pure_objects.

Definition desired_pod_name (sts : StatefulSetV.t) (ordinal : nat) : go_string :=
  sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-"%go ++ decimal_string ordinal.

Definition desired_pod_key (sts : StatefulSetV.t) (ordinal : nat) : KKey.t := {|
  KKey.Kind' := PodV.kind;
  KKey.Namespace' := sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace');
  KKey.Name' := desired_pod_name sts ordinal;
|}.

Definition statefulset_replicas (sts : StatefulSetV.t) : nat :=
  match sts.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') with
  | Some replicas => sint.nat replicas
  | None => 1%nat
  end.

Definition desired_ordinals (sts : StatefulSetV.t) : list nat :=
  seq 0 (statefulset_replicas sts).

Definition pvc_claim_template_names (sts : StatefulSetV.t) : list go_string :=
  (λ claim_template,
    claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name'))
  <$> sts.(StatefulSetV.Spec').(StatefulSetSpecV.VolumeClaimTemplates').

Definition desired_pvc_name sts claim_template_name ordinal : go_string :=
  claim_template_name ++ "-"%go ++
  sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-"%go ++
  decimal_string ordinal.

Definition desired_pvc_key sts claim_template_name ordinal : KKey.t := {|
  KKey.Kind' := PersistentVolumeClaimV.kind;
  KKey.Namespace' := sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace');
  KKey.Name' := desired_pvc_name sts claim_template_name ordinal;
|}.

Definition desired_pvc_key_candidates sts : list KKey.t :=
  concat (
    (λ ordinal,
      (λ claim_template_name, desired_pvc_key sts claim_template_name ordinal)
      <$> pvc_claim_template_names sts)
    <$> desired_ordinals sts
  ).

(* The official StatefulSet controller stores PVC requirements in maps keyed by
   template name, so duplicate claim-template names collapse to one object key. *)
Definition desired_pvc_keys sts : list KKey.t :=
  elements (list_to_set (C:=gset KKey.t) (desired_pvc_key_candidates sts)).

Definition desired_pod_keys (sts : StatefulSetV.t) : list KKey.t :=
  desired_pod_key sts <$> desired_ordinals sts.

Definition pod_key_is_desired (sts : StatefulSetV.t) (key : KKey.t) : Prop :=
  key ∈ desired_pod_keys sts.

#[global] Instance pod_key_is_desired_decision sts key :
    Decision (pod_key_is_desired sts key).
Proof. unfold pod_key_is_desired. apply _. Defined.

Definition pod_has_member_name (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  ∃ ordinal,
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = desired_pod_name sts ordinal.

Definition pod_has_member_key (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  ∃ ordinal, PodV.key pod = desired_pod_key sts ordinal.

Definition member_name_prefix (sts : StatefulSetV.t) : go_string :=
  sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-"%go.

Definition parse_member_name (sts : StatefulSetV.t) (pod : PodV.t) : option nat :=
  match New.proof.string.prefix_suffix.strip_prefix (member_name_prefix sts)
      (pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) with
  | Some suffix => parse_canonical_decimal_string suffix
  | None => None
  end.

Lemma parse_member_name_sound sts pod ordinal :
  parse_member_name sts pod = Some ordinal →
  pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = desired_pod_name sts ordinal.
Proof.
  unfold parse_member_name.
  destruct (New.proof.string.prefix_suffix.strip_prefix (member_name_prefix sts)
    (pod.(PodV.ObjectMeta').(ObjectMetaV.Name'))) as [suffix|] eqn:Hstrip; [|done].
  intros Hparse.
  apply parse_canonical_decimal_string_sound in Hparse.
  apply New.proof.string.prefix_suffix.strip_prefix_correct in Hstrip.
  unfold desired_pod_name, member_name_prefix in *.
  rewrite Hstrip.
  rewrite -Hparse.
  by rewrite List.app_assoc.
Qed.

Lemma parse_member_name_complete sts pod ordinal :
  pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = desired_pod_name sts ordinal →
  parse_member_name sts pod = Some ordinal.
Proof.
  intros Hname.
  unfold parse_member_name.
  rewrite Hname.
  unfold desired_pod_name, member_name_prefix.
  rewrite List.app_assoc.
  rewrite New.proof.string.prefix_suffix.strip_prefix_complete.
  apply parse_canonical_decimal_string_decimal_string.
Qed.

#[global] Instance pod_has_member_name_decision sts pod :
  Decision (pod_has_member_name sts pod).
Proof.
  destruct (parse_member_name sts pod) as [ordinal|] eqn:Hparse.
  - left. exists ordinal. by apply parse_member_name_sound.
  - right. intros [ordinal Hname].
    apply parse_member_name_complete in Hname.
    congruence.
Defined.

Lemma pod_has_member_key_iff sts pod :
  pod_has_member_key sts pod ↔
  pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ∧
  pod_has_member_name sts pod.
Proof.
  split.
  - intros [ordinal Hkey].
    split.
    + apply (f_equal KKey.Namespace') in Hkey. exact Hkey.
    + exists ordinal.
      apply (f_equal KKey.Name') in Hkey. exact Hkey.
  - intros [Hnamespace [ordinal Hname]].
    exists ordinal.
    unfold PodV.key, PodV.meta_key, desired_pod_key.
    simpl. by rewrite Hnamespace Hname.
Qed.

#[global] Instance pod_has_member_key_decision sts pod :
  Decision (pod_has_member_key sts pod).
Proof.
  destruct (decide (
    pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ∧
    pod_has_member_name sts pod)) as [Hmember|Hnot_member].
  - left. by apply pod_has_member_key_iff.
  - right. intros Hmember_key.
    apply Hnot_member. by apply pod_has_member_key_iff.
Defined.

Example pod_has_member_name_accepts_one sts pod :
  pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-1"%go →
  pod_has_member_name sts pod.
Proof.
  intros Hname.
  exists 1%nat.
  unfold desired_pod_name, decimal_string.
  simpl.
  exact Hname.
Qed.

Example pod_has_member_name_rejects_leading_zero sts pod :
  pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-01"%go →
  ¬ pod_has_member_name sts pod.
Proof.
  intros Hname [ordinal Hmember].
  pose proof (parse_member_name_complete sts pod ordinal Hmember) as Hparse.
  unfold parse_member_name, member_name_prefix in Hparse.
  rewrite Hname in Hparse.
  replace (sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-01"%go)
    with ((sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-"%go) ++ "01"%go)
    in Hparse by (rewrite -List.app_assoc; done).
  rewrite New.proof.string.prefix_suffix.strip_prefix_complete in Hparse.
  simpl in Hparse. done.
Qed.
