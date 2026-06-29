From New.proof Require Import prelude empty_ffi.
From New.proof.string Require Export prefix_suffix.
From New.proof.kubernetes_model Require Export get index create delete.
From New.proof Require Export util.
From New.proof.controllers Require Export common.
From New.proof.controllers.statefulset Require Export statefulset_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.statefulset.statefulset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.statefulset.statefulset.import_controller_Assumption.
#[local] Instance runtime_sem : code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
  controller.import_runtime_Assumption.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  common.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_core_v1_Assumption.
#[local] Instance apimodel_sem : apimodel.Assumptions | 0.
Proof using package_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
#[local] Instance common_sem : common.Assumptions | 0.
Proof using package_sem.
  constructor; try exact apimodel_sem; try apply _.
Defined.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Definition own_pod_frags γ dq (pod : PodV.t) : iProp Σ :=
  own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq
    pod.(PodV.ObjectMeta') ∗
  own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq
    (ObjectSpecV.PodSpec pod.(PodV.Spec')).

Definition own_pods_frags γ dq (pods : list PodV.t) : iProp Σ :=
  [∗ list] pod ∈ pods, own_pod_frags γ dq pod.

Definition own_pvc_frags γ dq (pvc : PersistentVolumeClaimV.t) : iProp Σ :=
  own_meta_frag γ (PersistentVolumeClaimV.key pvc)
    pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') dq
    pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
  own_spec_frag γ (PersistentVolumeClaimV.key pvc)
    pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') dq
    (ObjectSpecV.PersistentVolumeClaimSpec pvc.(PersistentVolumeClaimV.Spec')).

Definition own_pvcs_frags γ dq (pvcs : list PersistentVolumeClaimV.t) : iProp Σ :=
  [∗ list] pvc ∈ pvcs, own_pvc_frags γ dq pvc.

Definition statefulset_replicas sts : nat :=
  match sts.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') with
  | Some replicas => sint.nat replicas
  | None => 1%nat
  end.

Definition desired_ordinals sts : list nat :=
  seq 0 (statefulset_replicas sts).

Definition pvc_claim_template_names sts : list go_string :=
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

Lemma desired_pvc_keys_no_dup sts : NoDup (desired_pvc_keys sts).
Proof.
  unfold desired_pvc_keys.
  apply NoDup_elements.
Qed.

Definition missing_pvc_keys sts (pvcs : list PersistentVolumeClaimV.t) : list KKey.t :=
  filter (λ key, key ∉ (PersistentVolumeClaimV.key <$> pvcs)) (desired_pvc_keys sts).

Definition pvcs_match sts pvcs : Prop :=
  PersistentVolumeClaimV.key <$> pvcs ≡ₚ desired_pvc_keys sts.

Definition desired_pod_name sts ordinal : go_string :=
  sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-"%go ++ decimal_string ordinal.

(* TODO: complete this definition *)
Parameter pod_match : StatefulSetV.t → PodV.t → Prop.
Axiom pod_match_decision : ∀ sts pod, Decision (pod_match sts pod).
#[local] Existing Instance pod_match_decision.

Definition desired_pod_key sts ordinal : KKey.t := {|
  KKey.Kind' := PodV.kind;
  KKey.Namespace' := sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace');
  KKey.Name' := desired_pod_name sts ordinal;
|}.

Definition desired_pod_keys sts : list KKey.t :=
  desired_pod_key sts <$> desired_ordinals sts.

Definition pod_has_member_name sts pod : Prop :=
  ∃ ordinal,
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = desired_pod_name sts ordinal.

Definition pod_has_member_key sts pod : Prop :=
  ∃ ordinal, PodV.key pod = desired_pod_key sts ordinal.

Definition member_name_prefix sts : go_string :=
  sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ++ "-"%go.

Definition parse_member_name sts pod : option nat :=
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

#[local] Instance pod_has_member_name_decision sts pod :
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

#[local] Instance pod_has_member_key_decision sts pod :
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

Definition pod_key_is_desired sts key : Prop :=
  key ∈ desired_pod_keys sts.

#[local] Instance pod_key_is_desired_decision sts key :
    Decision (pod_key_is_desired sts key).
Proof. unfold pod_key_is_desired. apply _. Defined.

Lemma desired_pod_key_inj sts : Inj (=) (=) (desired_pod_key sts).
Proof.
  intros ordinal1 ordinal2 Hkey.
  apply (f_equal KKey.Name') in Hkey.
  simpl in Hkey.
  unfold desired_pod_name in Hkey.
  apply app_inv_head in Hkey.
  apply app_inv_head in Hkey.
  by apply decimal_string_inj in Hkey.
Qed.

Lemma desired_pod_keys_no_dup sts : NoDup (desired_pod_keys sts).
Proof.
  unfold desired_pod_keys, desired_ordinals.
  apply NoDup_fmap_2.
  - apply desired_pod_key_inj.
  - apply NoDup_seq.
Qed.

Definition missing_pod_keys sts (pods : list PodV.t) : list KKey.t :=
  filter (λ key, key ∉ (PodV.key <$> pods)) (desired_pod_keys sts).

Definition needed_pods sts pods : list PodV.t :=
  filter (λ pod, pod_key_is_desired sts (PodV.key pod)) pods.

Definition outdated_pods sts pods : list PodV.t :=
  filter (λ pod, ¬ pod_match sts pod) (needed_pods sts pods).

Definition bad_name_pods sts pods : list PodV.t :=
  filter (λ pod, ¬ pod_has_member_key sts pod) pods.

Definition alive_condemned_pods sts pods : list PodV.t :=
  filter
    (λ pod, pod_has_member_key sts pod ∧ ¬ pod_key_is_desired sts (PodV.key pod) ∧
      is_pod_alive pod)
    pods.

(* The progress metric gives an outdated desired Pod cost 2 and a missing
   desired Pod cost 1, so deleting one outdated Pod strictly reduces the
   distance even though the desired replacement Pod is created by a later run. *)
Definition pod_distance sts pods : nat :=
  length (missing_pod_keys sts pods) +
  2 * length (outdated_pods sts pods) +
  length (bad_name_pods sts pods) +
  length (alive_condemned_pods sts pods).

Definition undesired_pvc_keys sts pvcs : list KKey.t :=
  filter (λ key, key ∉ desired_pvc_keys sts) (PersistentVolumeClaimV.key <$> pvcs).

Definition pvc_distance sts pvcs : nat :=
  length (missing_pvc_keys sts pvcs) + length (undesired_pvc_keys sts pvcs).

Definition match_distance sts pods pvcs : nat :=
  pod_distance sts pods + pvc_distance sts pvcs.

Definition pods_match sts pods : Prop :=
  Forall (pod_has_member_key sts) pods ∧
  Forall (λ pod, ¬ pod_key_is_desired sts (PodV.key pod) → ¬ is_pod_alive pod) pods ∧
  PodV.key <$> needed_pods sts pods ≡ₚ desired_pod_keys sts ∧
  Forall (pod_match sts) (needed_pods sts pods).

Definition current_state_matches sts pods pvcs : Prop :=
  pods_match sts pods ∧ pvcs_match sts pvcs.

Lemma own_pods_frags_no_dup γ pods :
  own_pods_frags γ 1 pods -∗
  ⌜ NoDup (PodV.key <$> pods) ⌝.
Proof.
  iIntros "Hpods".
  iAssert ([∗ list] pod ∈ pods,
      own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta'))%I
    with "[Hpods]" as "Hpod_meta_frags".
  { unfold own_pods_frags, own_pod_frags.
    iInduction pods as [|pod pods] "IH".
    - rewrite !big_sepL_nil. done.
    - rewrite !big_sepL_cons.
      iDestruct "Hpods" as "[(Hmeta & _) Hpods]".
      iFrame "Hmeta".
      iApply ("IH" with "Hpods"). }
  iPoseProof (kview.own_meta_list_no_dup PodV.key PodV.ObjectMeta'
    with "Hpod_meta_frags") as "%Hnodup".
  done.
Qed.

Lemma own_pvcs_frags_no_dup γ pvcs :
  own_pvcs_frags γ 1 pvcs -∗
  ⌜ NoDup (PersistentVolumeClaimV.key <$> pvcs) ⌝.
Proof.
  iIntros "Hpvcs".
  iAssert ([∗ list] pvc ∈ pvcs,
      own_meta_frag γ (PersistentVolumeClaimV.key pvc)
        pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1
        pvc.(PersistentVolumeClaimV.ObjectMeta'))%I
    with "[Hpvcs]" as "Hpvc_meta_frags".
  { unfold own_pvcs_frags, own_pvc_frags.
    iInduction pvcs as [|pvc pvcs] "IH".
    - rewrite !big_sepL_nil. done.
    - rewrite !big_sepL_cons.
      iDestruct "Hpvcs" as "[(Hmeta & _) Hpvcs]".
      iFrame "Hmeta".
      iApply ("IH" with "Hpvcs"). }
  iPoseProof (kview.own_meta_list_no_dup
    PersistentVolumeClaimV.key PersistentVolumeClaimV.ObjectMeta'
    with "Hpvc_meta_frags") as "%Hnodup".
  done.
Qed.

Lemma match_distance_zero_matches γ sts pods pvcs :
  own_pods_frags γ 1 pods -∗
  own_pvcs_frags γ 1 pvcs -∗
  ⌜ match_distance sts pods pvcs = 0%nat ↔ current_state_matches sts pods pvcs ⌝.
Proof.
  iIntros "Hpods Hpvcs".
  iPoseProof (own_pods_frags_no_dup with "Hpods") as "%Hpods_nodup".
  iPoseProof (own_pvcs_frags_no_dup with "Hpvcs") as "%Hpvcs_nodup".
  iPureIntro.
  pose proof (desired_pod_keys_no_dup sts) as Hdesired_pods_nodup.
  pose proof (desired_pvc_keys_no_dup sts) as Hdesired_pvcs_nodup.
  split.
  - intros Hdist.
    unfold match_distance, pod_distance, pvc_distance in Hdist.
    assert (Hmissing_pods : length (missing_pod_keys sts pods) = 0%nat) by lia.
    assert (Houtdated_pods : length (outdated_pods sts pods) = 0%nat) by lia.
    assert (Hbad_name_pods : length (bad_name_pods sts pods) = 0%nat) by lia.
    assert (Halive_condemned_pods :
        length (alive_condemned_pods sts pods) = 0%nat) by lia.
    assert (Hmissing_pvcs : length (missing_pvc_keys sts pvcs) = 0%nat) by lia.
    assert (Hundesired_pvcs : length (undesired_pvc_keys sts pvcs) = 0%nat) by lia.
    assert (Hpod_good_name : ∀ pod,
        pod ∈ pods → pod_has_member_key sts pod).
    { intros pod Hpod.
      destruct (decide (pod_has_member_key sts pod)) as [Hgood|Hbad]; [done|].
      exfalso.
      eapply (filter_length_zero_not_elem
        (λ pod, ¬ pod_has_member_key sts pod) pods pod);
        [exact Hbad_name_pods|exact Hpod|exact Hbad]. }
    assert (Hdesired_pod_actual : ∀ key,
        key ∈ desired_pod_keys sts → key ∈ PodV.key <$> pods).
    { intros key Hdesired.
      destruct (decide (key ∈ PodV.key <$> pods)) as [Hactual|Hnot_actual]; [done|].
      exfalso.
      eapply (filter_length_zero_not_elem
        (λ key, key ∉ (PodV.key <$> pods)) (desired_pod_keys sts) key);
        [exact Hmissing_pods|exact Hdesired|exact Hnot_actual]. }
    split.
    + split.
      * apply Forall_forall. intros pod Hpod.
        rewrite <- list_elem_of_In in Hpod.
        by apply Hpod_good_name.
      * split.
        -- apply Forall_forall. intros pod Hpod Hnot_desired Halive.
           rewrite <- list_elem_of_In in Hpod.
           eapply (filter_length_zero_not_elem
             (λ pod, pod_has_member_key sts pod ∧ ¬ pod_key_is_desired sts (PodV.key pod) ∧
               is_pod_alive pod)
             pods pod);
             [exact Halive_condemned_pods|exact Hpod|].
           repeat split; [by apply Hpod_good_name|exact Hnot_desired|exact Halive].
        -- split.
           ++ apply NoDup_Permutation.
              ** apply NoDup_fmap_filter. exact Hpods_nodup.
              ** exact Hdesired_pods_nodup.
              ** intros key. split.
                 --- intros Hactual.
                     apply list_elem_of_fmap_1 in Hactual as (pod & Hkey_eq & Hpod_filter).
                     apply list_elem_of_filter in Hpod_filter as [Hpod_desired _].
                     unfold pod_key_is_desired in Hpod_desired.
                     rewrite Hkey_eq. exact Hpod_desired.
                 --- intros Hdesired.
                     apply Hdesired_pod_actual in Hdesired as Hactual.
                     apply list_elem_of_fmap_1 in Hactual as (pod & Hkey_eq & Hpod).
                     rewrite Hkey_eq.
                     apply list_elem_of_fmap_2.
                     apply list_elem_of_filter.
                     split; [|exact Hpod].
                     unfold pod_key_is_desired.
                     rewrite -Hkey_eq. exact Hdesired.
           ++ apply Forall_forall. intros pod Hpod.
              rewrite <- list_elem_of_In in Hpod.
              assert (Hpod_needed : pod ∈ needed_pods sts pods) by exact Hpod.
              unfold needed_pods in Hpod.
              apply list_elem_of_filter in Hpod as [Hpod_desired Hpod].
              destruct (decide (pod_match sts pod)) as [Hmatch|Hnot_match]; [exact Hmatch|].
              exfalso.
              eapply (filter_length_zero_not_elem
                (λ pod, ¬ pod_match sts pod)
                (needed_pods sts pods) pod);
                [|exact Hpod_needed|exact Hnot_match].
              unfold outdated_pods in Houtdated_pods. exact Houtdated_pods.
    + apply NoDup_Permutation; [exact Hpvcs_nodup|exact Hdesired_pvcs_nodup|].
      intros key. split.
      * intros Hactual.
        destruct (decide (key ∈ desired_pvc_keys sts)) as [Hdesired|Hnot_desired]; [done|].
        exfalso.
        eapply (filter_length_zero_not_elem
          (λ key, key ∉ desired_pvc_keys sts) (PersistentVolumeClaimV.key <$> pvcs) key);
          [exact Hundesired_pvcs|exact Hactual|exact Hnot_desired].
      * intros Hdesired.
        destruct (decide (key ∈ PersistentVolumeClaimV.key <$> pvcs)) as [Hactual|Hnot_actual]; [done|].
        exfalso.
        eapply (filter_length_zero_not_elem
          (λ key, key ∉ (PersistentVolumeClaimV.key <$> pvcs)) (desired_pvc_keys sts) key);
          [exact Hmissing_pvcs|exact Hdesired|exact Hnot_actual].
  - intros [[Hmember [Hcondemned [Hneeded_perm Hneeded_match]]] Hpvcs_perm].
    unfold match_distance, pod_distance, pvc_distance.
    assert (Hmissing_pods_nil : missing_pod_keys sts pods = []).
    { unfold missing_pod_keys.
      apply filter_none. intros key Hdesired Hnot_actual.
      apply Hnot_actual.
      rewrite -Hneeded_perm in Hdesired.
      apply list_elem_of_fmap_1 in Hdesired as (pod & Hkey_eq & Hpod_needed).
      rewrite Hkey_eq. apply list_elem_of_fmap_2.
      unfold needed_pods in Hpod_needed.
      apply list_elem_of_filter in Hpod_needed as [_ Hpod].
      exact Hpod. }
    assert (Houtdated_pods_nil : outdated_pods sts pods = []).
    { unfold outdated_pods.
      apply filter_none. intros pod Hpod Hnot_match.
      rewrite Forall_forall in Hneeded_match.
      rewrite list_elem_of_In in Hpod.
      exact (Hnot_match (Hneeded_match pod Hpod)). }
    assert (Hbad_name_pods_nil : bad_name_pods sts pods = []).
    { unfold bad_name_pods.
      apply filter_none. intros pod Hpod Hnot_member.
      rewrite Forall_forall in Hmember.
      rewrite list_elem_of_In in Hpod.
      exact (Hnot_member (Hmember pod Hpod)). }
    assert (Halive_condemned_pods_nil : alive_condemned_pods sts pods = []).
    { unfold alive_condemned_pods.
      apply filter_none. intros pod Hpod (_ & Hnot_desired & Halive).
      rewrite Forall_forall in Hcondemned.
      rewrite list_elem_of_In in Hpod.
      exact (Hcondemned pod Hpod Hnot_desired Halive). }
    assert (Hmissing_pvcs_nil : missing_pvc_keys sts pvcs = []).
    { unfold missing_pvc_keys.
      apply filter_none. intros key Hdesired Hnot_actual.
      apply Hnot_actual. by rewrite Hpvcs_perm. }
    assert (Hundesired_pvcs_nil : undesired_pvc_keys sts pvcs = []).
    { unfold undesired_pvc_keys.
      apply filter_none. intros key Hactual Hnot_desired.
      apply Hnot_desired. by rewrite -Hpvcs_perm. }
    rewrite Hmissing_pods_nil Houtdated_pods_nil Hbad_name_pods_nil
      Halive_condemned_pods_nil Hmissing_pvcs_nil Hundesired_pvcs_nil.
    done.
Qed.

Definition pod_key_set (pods : list PodV.t) : gset KKey.t :=
  list_to_set (PodV.key <$> pods).

Definition pod_meta_except_resource_version_changed
    (pods pods' : list PodV.t) : Prop :=
  ∃ pod pod',
    pod ∈ pods ∧
    pod' ∈ pods' ∧
    PodV.key pod = PodV.key pod' ∧
    ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta') ≠
      ObjectMetaV.without_resource_version pod'.(PodV.ObjectMeta').

Definition pod_spec_changed (pods pods' : list PodV.t) : Prop :=
  ∃ pod pod',
    pod ∈ pods ∧
    pod' ∈ pods' ∧
    PodV.key pod = PodV.key pod' ∧
    pod.(PodV.Spec') ≠ pod'.(PodV.Spec').

Definition pods_progress_observed (pods pods' : list PodV.t) : Prop :=
  pod_key_set pods ≠ pod_key_set pods' ∨
  pod_meta_except_resource_version_changed pods pods' ∨
  pod_spec_changed pods pods'.

Lemma wp_syncStatefulSet_progress γ l (gv: schema.GroupVersion.t) namespace name sts dq pods pvcs :
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr apps_v1.SchemeGroupVersion) ↦□ gv ∗
      "Hown_sts_meta_frag" ∷ own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        dq sts.(StatefulSetV.ObjectMeta') ∗
      "Hown_sts_spec_frag" ∷ own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      "Hown_pod_frags" ∷ own_pods_frags γ 1 pods ∗
      "Hown_pvc_frags" ∷ own_pvcs_frags γ 1 pvcs ∗
      "Hown_children_frag" ∷ own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        1 (list_to_set (PodV.key <$> pods)) ∗
      "Hown_reserved_missing_pod_keys" ∷ ([∗ list] key ∈ missing_pod_keys sts pods, own_reserved_frag γ key) ∗
      "Hown_reserved_missing_pvc_keys" ∷ ([∗ list] key ∈ missing_pvc_keys sts pvcs, own_reserved_frag γ key) ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hdeletion_timestamp_eq" ∷ ⌜ sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "%Hnot_match" ∷ ⌜ ¬ current_state_matches sts pods pvcs ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ (pods' : list PodV.t) (pvcs' : list PersistentVolumeClaimV.t) (err : interface.t), RET #err;
      ⌜ current_state_matches sts pods' pvcs' ∨
        pods_progress_observed pods pods' ∧ match_distance sts pods pvcs > match_distance sts pods' pvcs' ⌝ ∗
      own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        dq sts.(StatefulSetV.ObjectMeta') ∗
      own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      own_pods_frags γ 1 pods' ∗
      own_pvcs_frags γ 1 pvcs' ∗
      own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        1 (list_to_set (PodV.key <$> pods'))
  }}}.
Proof.
Admitted.

Lemma wp_syncStatefulSet_stability γ l (gv: schema.GroupVersion.t) namespace name sts dq pods pvcs :
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr apps_v1.SchemeGroupVersion) ↦□ gv ∗
      "Hown_sts_meta_frag" ∷ own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        dq sts.(StatefulSetV.ObjectMeta') ∗
      "Hown_sts_spec_frag" ∷ own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      "Hown_pod_frags" ∷ own_pods_frags γ dq pods ∗
      "Hown_pvc_frags" ∷ own_pvcs_frags γ dq pvcs ∗
      "Hown_children_frag" ∷ own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        dq (list_to_set (PodV.key <$> pods)) ∗
      "Hown_reserved_missing_pod_keys" ∷ ([∗ list] key ∈ missing_pod_keys sts pods, own_reserved_frag γ key) ∗
      "Hown_reserved_missing_pvc_keys" ∷ ([∗ list] key ∈ missing_pvc_keys sts pvcs, own_reserved_frag γ key) ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hdeletion_timestamp_eq" ∷ ⌜ sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "%Hnot_match" ∷ ⌜ current_state_matches sts pods pvcs ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ RET #interface.nil;
      own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        dq sts.(StatefulSetV.ObjectMeta') ∗
      own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      own_pods_frags γ dq pods ∗
      own_pvcs_frags γ dq pvcs ∗
      own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
        dq (list_to_set (PodV.key <$> pods))
  }}}.
Proof.
Admitted.

End proof.
