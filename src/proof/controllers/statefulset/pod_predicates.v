From New.proof Require Export wp_helpers.
From New.proof.string Require Export prefix_suffix.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers Require Export common.
From New.proof.controllers.statefulset Require Import pvc_predicates.

Definition statefulset_replicas (sts : StatefulSetV.t) : nat :=
  match sts.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') with
  | Some replicas => sint.nat replicas
  | None => 1%nat
  end.

Definition desired_ordinals (sts : StatefulSetV.t) : list nat :=
  seq 0 (statefulset_replicas sts).

Definition desired_pod_name (set_name : go_string) (ordinal : nat) : go_string :=
  set_name ++ "-"%go ++ decimal_string ordinal.

Definition desired_pod_key sts ordinal : KKey.t := {|
  KKey.Kind' := PodV.kind;
  KKey.Namespace' := sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace');
  KKey.Name' := desired_pod_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal;
|}.

Definition desired_pod_keys (sts : StatefulSetV.t) : list KKey.t :=
  desired_pod_key sts <$> desired_ordinals sts.

Definition pod_key_is_desired (sts : StatefulSetV.t) (key : KKey.t) : Prop :=
  key ∈ desired_pod_keys sts.

#[global] Instance pod_key_is_desired_decision sts key :
    Decision (pod_key_is_desired sts key).
Proof. unfold pod_key_is_desired. apply _. Defined.

Definition pod_has_member_name (set_name pod_name : go_string) : Prop :=
  ∃ ordinal, pod_name = desired_pod_name set_name ordinal.

Definition pod_has_member_key (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  ∃ ordinal, PodV.key pod = desired_pod_key sts ordinal.

Lemma desired_pod_name_inj set_name ordinal1 ordinal2 :
  desired_pod_name set_name ordinal1 = desired_pod_name set_name ordinal2 →
  ordinal1 = ordinal2.
Proof.
  unfold desired_pod_name.
  intros Hname.
  apply app_inv_head in Hname.
  inversion Hname as [Hdecimal].
  by apply decimal_string_inj in Hdecimal.
Qed.

Lemma desired_pod_name_last_dash_decomp pod_name parent suffix set_name ordinal :
  pod_name = parent ++ [byte_dash] ++ suffix →
  byte_dash ∉ suffix →
  pod_name = desired_pod_name set_name ordinal →
  parent = set_name ∧ suffix = decimal_string ordinal.
Proof.
  intros Hdecomp Hsuffix_no_dash Hdesired.
  rewrite Hdesired in Hdecomp.
  unfold desired_pod_name in Hdecomp.
  change "-"%go with [byte_dash] in Hdecomp.
  eapply app_last_sep_inj in Hdecomp.
  - destruct Hdecomp as [Hparent Hsuffix].
    split; symmetry; done.
  - apply decimal_string_dash_free.
  - by apply dash_free_of_not_elem.
Qed.

Lemma desired_pod_name_has_dash set_name ordinal :
  byte_dash ∈ desired_pod_name set_name ordinal.
Proof.
  unfold desired_pod_name.
  change "-"%go with [byte_dash].
  rewrite elem_of_app. right.
  rewrite elem_of_app. left.
  rewrite elem_of_cons. by left.
Qed.

Definition member_name_prefix (set_name : go_string) : go_string :=
  set_name ++ "-"%go.

Definition parse_member_name (set_name pod_name : go_string) : option nat :=
  match New.proof.string.prefix_suffix.strip_prefix (member_name_prefix set_name)
      pod_name with
  | Some suffix => parse_canonical_decimal_string suffix
  | None => None
  end.

Lemma parse_member_name_sound set_name pod_name ordinal :
  parse_member_name set_name pod_name = Some ordinal →
  pod_name = desired_pod_name set_name ordinal.
Proof.
  unfold parse_member_name.
  destruct (New.proof.string.prefix_suffix.strip_prefix (member_name_prefix set_name)
    pod_name) as [suffix|] eqn:Hstrip; [|done].
  intros Hparse.
  apply parse_canonical_decimal_string_sound in Hparse.
  apply New.proof.string.prefix_suffix.strip_prefix_correct in Hstrip.
  unfold desired_pod_name, member_name_prefix in *.
  rewrite Hstrip.
  rewrite -Hparse.
  by rewrite List.app_assoc.
Qed.

Lemma parse_member_name_complete set_name pod_name ordinal :
  pod_name = desired_pod_name set_name ordinal →
  parse_member_name set_name pod_name = Some ordinal.
Proof.
  intros Hname.
  unfold parse_member_name.
  rewrite Hname.
  unfold desired_pod_name, member_name_prefix.
  rewrite List.app_assoc.
  rewrite New.proof.string.prefix_suffix.strip_prefix_complete.
  apply parse_canonical_decimal_string_decimal_string.
Qed.

#[global] Instance pod_has_member_name_decision set_name pod_name :
  Decision (pod_has_member_name set_name pod_name).
Proof.
  destruct (parse_member_name set_name pod_name) as [ordinal|] eqn:Hparse.
  - left. exists ordinal. by apply parse_member_name_sound.
  - right. intros [ordinal Hname].
    apply parse_member_name_complete in Hname.
    congruence.
Defined.

Definition pod_has_int32_member_name (set_name pod_name : go_string) : Prop :=
  ∃ ordinal : nat,
    (ordinal <= go_int32_max_nat)%nat ∧
    pod_name = desired_pod_name set_name ordinal.

#[global] Instance pod_has_int32_member_name_decision set_name pod_name :
    Decision (pod_has_int32_member_name set_name pod_name).
Proof.
  unfold pod_has_int32_member_name.
  destruct (parse_member_name set_name pod_name) as [ordinal|] eqn:Hparse.
  - destruct (decide (ordinal <= go_int32_max_nat)%nat) as [Hbound|Hoverflow].
    + left. exists ordinal. split; [done|].
      by apply parse_member_name_sound.
    + right. intros (ordinal' & Hbound & Hname).
      apply parse_member_name_complete in Hname.
      rewrite Hparse in Hname.
      simplify_eq/=.
      done.
  - right. intros (ordinal & _ & Hname).
    apply parse_member_name_complete in Hname.
    congruence.
Defined.

(* These are precisely the Pods that pass [filterPodsForStatefulSet] and cause
   [reconcileReplicas] to return when it observes their deletion timestamp. *)
Definition pending_pod sts (pod : PodV.t) : Prop :=
  ¬ is_pod_alive pod ∧
  pod_has_int32_member_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name').

Lemma pod_has_member_key_iff sts pod :
  pod_has_member_key sts pod ↔
  pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ∧
  pod_has_member_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name').
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
    pod_has_member_name
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name'))) as [Hmember|Hnot_member].
  - left. by apply pod_has_member_key_iff.
  - right. intros Hmember_key.
    apply Hnot_member. by apply pod_has_member_key_iff.
Defined.

Definition pod_ordinal_suffix (pod_name : go_string) : option go_string :=
  match list_find (λ b, b = byte_dash) (reverse pod_name) with
  | Some (idx, _) => Some (reverse (take idx (reverse pod_name)))
  | None => None
  end.

Definition parse_pod_ordinal (pod_name : go_string) : option nat :=
  suffix ← pod_ordinal_suffix pod_name;
  parse_decimal_string suffix.

Lemma pod_name_length_le_go_int_max_of_valid_name name :
  valid_name PodV.kind name →
  Z.of_nat (length name) ≤ go_int_max.
Proof.
  unfold valid_name, PodV.kind.
  intros [[Hkind _]|([Hpod|[Hreplicaset|Hpvc]] & Hvalid_name)];
    try discriminate.
  destruct Hvalid_name as [_ Hlength].
  unfold go_int_max. lia.
Qed.

Lemma pod_name_length_le_go_int_max_of_valid pod :
  PodV.valid pod →
  Z.of_nat
    (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max.
Proof.
  intros (_ & _ & Hmeta & _).
  apply pod_name_length_le_go_int_max_of_valid_name.
  by apply ObjectMetaV.valid_name_of_valid.
Qed.

Lemma pod_name_length_le_go_int_max_of_valid_named_create namespace pod :
  PodV.valid_named_create namespace pod →
  Z.of_nat
    (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max.
Proof.
  intros (_ & Hmeta & _).
  apply pod_name_length_le_go_int_max_of_valid_name.
  unfold ObjectMetaV.valid_named_create in Hmeta.
  tauto.
Qed.

Example pod_has_member_name_accepts_one sts pod :
  pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-1"%go →
  pod_has_member_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name').
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
  ¬ pod_has_member_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name').
Proof.
  intros Hname [ordinal Hmember].
  pose proof (parse_member_name_complete
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ordinal Hmember) as Hparse.
  unfold parse_member_name, member_name_prefix in Hparse.
  rewrite Hname in Hparse.
  replace (sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-01"%go)
    with ((sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-"%go) ++
      "01"%go) in Hparse by (rewrite -List.app_assoc; done).
  rewrite New.proof.string.prefix_suffix.strip_prefix_complete in Hparse.
  simpl in Hparse. done.
Qed.

Definition pod_identity_matches (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  match parse_member_name
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name'),
    pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') with
  | Some ordinal, Some labels =>
      (ordinal <= go_int32_max_nat)%nat ∧
      pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
        sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ∧
      labels !! statefulset_pod_name_label =
        Some pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ∧
      labels !! pod_index_label = Some (decimal_string ordinal)
  | _, _ => False
  end.

#[global] Instance pod_identity_matches_decision sts pod :
    Decision (pod_identity_matches sts pod).
Proof.
  unfold pod_identity_matches.
  destruct parse_member_name,
    (pod.(PodV.ObjectMeta').(ObjectMetaV.Labels')); apply _.
Defined.

(* Go map insertion overwrites an earlier volume with the same name, so the
   left fold preserves the last volume from the Pod's volume slice. *)
Definition pod_volumes_map_insert
    (volumes : gmap go_string VolumeV.t) (volume : VolumeV.t) :
    gmap go_string VolumeV.t :=
  <[volume.(VolumeV.Name') := volume]> volumes.

Definition pod_volumes_map_of_list (volumes : list VolumeV.t) :
    gmap go_string VolumeV.t :=
  fold_left pod_volumes_map_insert volumes ∅.

Definition pod_volume_claim_matches
    (volumes : gmap go_string VolumeV.t) (set_name : go_string)
    (ordinal : nat) (claim_template_name : go_string) : Prop :=
  match volumes !! claim_template_name with
  | Some volume =>
      match volume.(VolumeV.VolumeSource').(
        VolumeSourceV.PersistentVolumeClaim') with
      | Some pvc =>
          pvc.(v1.PersistentVolumeClaimVolumeSource.ClaimName') =
            desired_pvc_name set_name claim_template_name ordinal
      | None => False
      end
  | None => False
  end.

#[global] Instance pod_volume_claim_matches_decision volumes set_name ordinal
    claim_template_name :
    Decision (pod_volume_claim_matches volumes set_name ordinal
      claim_template_name).
Proof.
  unfold pod_volume_claim_matches.
  destruct (volumes !! claim_template_name) as [volume|]; [|apply _].
  destruct volume.(VolumeV.VolumeSource').(
    VolumeSourceV.PersistentVolumeClaim'); apply _.
Defined.

Definition pod_storage_matches (set : StatefulSetV.t) (pod : PodV.t) : Prop :=
  match parse_pod_ordinal
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name') with
  | Some ordinal =>
      (ordinal <= go_int32_max_nat)%nat ∧
      Forall
        (pod_volume_claim_matches
          (pod_volumes_map_of_list pod.(PodV.Spec').(PodSpecV.Volumes'))
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal)
        (pvc_claim_template_names set)
  | None => False
  end.

#[global] Instance pod_storage_matches_decision set pod :
    Decision (pod_storage_matches set pod).
Proof.
  unfold pod_storage_matches.
  destruct (parse_pod_ordinal
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name')); apply _.
Defined.

Definition without_statefulset_fields (_ : PodSpecV.t) : PodSpecV.t := {|
  PodSpecV.Volumes' := [];
  PodSpecV.Hostname' := ""%go;
  PodSpecV.Subdomain' := ""%go;
|}.

(* [podSpecMatches] treats Hostname, Subdomain, and the StatefulSet PVC
   volumes as immutable creation-time state. The remaining PodSpec fields must
   still agree with the Pod template after those generated fields are erased. *)
Definition pod_immutable_matches (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  pod.(PodV.Spec').(PodSpecV.Hostname') =
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ∧
  pod.(PodV.Spec').(PodSpecV.Subdomain') =
    sts.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') ∧
  pod_storage_matches sts pod ∧
  without_statefulset_fields pod.(PodV.Spec') =
    without_statefulset_fields
      sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template').(PodTemplateSpecV.Spec').

#[global] Instance pod_immutable_matches_decision sts pod :
    Decision (pod_immutable_matches sts pod).
Proof.
  unfold pod_immutable_matches, without_statefulset_fields.
  destruct (decide
    (pod.(PodV.Spec').(PodSpecV.Hostname') =
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name'))) as [Hhostname|Hhostname].
  2: { right. intros (H & _). contradiction. }
  destruct (decide
    (pod.(PodV.Spec').(PodSpecV.Subdomain') =
      sts.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName')))
    as [Hsubdomain|Hsubdomain].
  2: { right. intros (_ & H & _). contradiction. }
  destruct (decide (pod_storage_matches sts pod))
    as [Hstorage|Hstorage].
  2: { right. intros (_ & _ & H & _). contradiction. }
  left. split_and!; try done.
Defined.

Definition pod_match (sts : StatefulSetV.t) (pod : PodV.t) : Prop :=
  pod_identity_matches sts pod ∧
  pod_immutable_matches sts pod.

#[global] Instance pod_match_decision sts pod : Decision (pod_match sts pod).
Proof. unfold pod_match. apply _. Defined.

Definition pod_is_condemned (set : StatefulSetV.t) (pod : PodV.t) : Prop :=
  ∃ ordinal,
    (ordinal ≤ go_int32_max_nat)%nat ∧
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
      desired_pod_name
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ∧
    (statefulset_replicas set ≤ ordinal)%nat.

Definition pod_is_outdated (set : StatefulSetV.t) (pod : PodV.t) : Prop :=
  ∃ ordinal,
    (ordinal ≤ go_int32_max_nat)%nat ∧
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
      desired_pod_name
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ∧
    (ordinal < statefulset_replicas set)%nat ∧
    ¬ pod_immutable_matches set pod.
