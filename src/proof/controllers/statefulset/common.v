From New.proof Require Import prelude empty_ffi.
From New.proof.string Require Export prefix_suffix.
From New.proof.kubernetes_types Require Export prelude.
From New.proof Require Export wp_helpers.

Definition desired_pod_name (set_name : go_string) (ordinal : nat) : go_string :=
  set_name ++ "-"%go ++ decimal_string ordinal.

Definition desired_pod_key sts ordinal : KKey.t := {|
  KKey.Kind' := PodV.kind;
  KKey.Namespace' := sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace');
  KKey.Name' := desired_pod_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal;
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

Definition desired_pvc_name set_name claim_template_name ordinal : go_string :=
  claim_template_name ++ "-"%go ++ set_name ++ "-"%go ++ decimal_string ordinal.

Definition desired_pvc_key sts claim_template_name ordinal : KKey.t := {|
  KKey.Kind' := PersistentVolumeClaimV.kind;
  KKey.Namespace' := sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace');
  KKey.Name' := desired_pvc_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') claim_template_name ordinal;
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
    with ((sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-"%go) ++ "01"%go)
    in Hparse by (rewrite -List.app_assoc; done).
  rewrite New.proof.string.prefix_suffix.strip_prefix_complete in Hparse.
  simpl in Hparse. done.
Qed.
