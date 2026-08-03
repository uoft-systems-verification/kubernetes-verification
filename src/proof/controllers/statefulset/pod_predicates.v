From New.proof.controllers.statefulset Require Export top_level.

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

#[global] Instance pod_has_member_name_decision set_name pod_name :
  Decision (pod_has_member_name set_name pod_name).
Proof.
  destruct (parse_member_name set_name pod_name) as [ordinal|] eqn:Hparse.
  - left. exists ordinal. by apply parse_member_name_sound.
  - right. intros [ordinal Hname].
    apply parse_member_name_complete in Hname.
    congruence.
Defined.

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
