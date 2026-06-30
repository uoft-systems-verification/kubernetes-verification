From New.proof Require Import prelude empty_ffi.
From New.proof.string Require Export prefix_suffix.
From New.proof.kubernetes_model Require Export get index create delete.
From New.proof Require Export util.
From New.proof.controllers Require Export common.
From New.proof.controllers.statefulset Require Export name.
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

(* TODO: complete this definition *)
Parameter pod_match : StatefulSetV.t → PodV.t → Prop.
Axiom pod_match_decision : ∀ sts pod, Decision (pod_match sts pod).
#[local] Existing Instance pod_match_decision.

Definition missing_pod_keys sts (pods : list PodV.t) : list KKey.t :=
  filter (λ key, key ∉ (PodV.key <$> pods)) (desired_pod_keys sts).

Definition needed_pods sts pods : list PodV.t :=
  filter (λ pod, pod_key_is_desired sts (PodV.key pod)) pods.

Definition outdated_pods sts pods : list PodV.t :=
  filter (λ pod, ¬ pod_match sts pod) (needed_pods sts pods).

Definition bad_name_pods sts pods : list PodV.t :=
  filter (λ pod, ¬ pod_has_member_key sts pod) pods.

Definition condemned_pods sts pods : list PodV.t :=
  filter (λ pod, pod_has_member_key sts pod ∧ ¬ pod_key_is_desired sts (PodV.key pod)) pods.

(* The progress metric gives an outdated desired Pod cost 2 and a missing
   desired Pod cost 1, so deleting one outdated Pod strictly reduces the
   distance even though the desired replacement Pod is created by a later run.
   Once the delete only sets DeletionTimestamp, the Pod is no longer alive and
   should not keep contributing to the outdated-Pod distance. *)
Definition pod_distance sts pods : nat :=
  length (missing_pod_keys sts pods) +
  2 * length (filter is_pod_alive (outdated_pods sts pods)) +
  length (filter is_pod_alive (condemned_pods sts pods)) +
  length (bad_name_pods sts pods).

Definition missing_pvc_keys sts (pvcs : list PersistentVolumeClaimV.t) : list KKey.t :=
  filter (λ key, key ∉ (PersistentVolumeClaimV.key <$> pvcs)) (desired_pvc_keys sts).

Definition pvc_distance sts pvcs : nat :=
  length (missing_pvc_keys sts pvcs).

Definition match_distance sts pods pvcs : nat :=
  pod_distance sts pods + pvc_distance sts pvcs.

Definition pods_match sts pods : Prop :=
  PodV.key <$> pods ≡ₚ desired_pod_keys sts ∧
  Forall is_pod_alive pods ∧
  Forall (pod_match sts) pods.

Definition pvcs_match sts (pvcs : list PersistentVolumeClaimV.t) : Prop :=
  ∀ key, key ∈ desired_pvc_keys sts →
    key ∈ (PersistentVolumeClaimV.key <$> pvcs).

Definition current_state_matches sts pods pvcs : Prop :=
  pods_match sts pods ∧ pvcs_match sts pvcs.

Lemma match_distance_zero_matches γ sts pods pvcs :
  (∀ pod, pod ∈ pods → is_pod_alive pod) →
  ([∗ list] pod ∈ pods, own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) -∗
  ⌜ match_distance sts pods pvcs = 0%nat ↔ current_state_matches sts pods pvcs ⌝.
Proof.
  iIntros (Hpods_alive) "Hpod_meta_frags".
  iPoseProof (kview.own_meta_list_no_dup PodV.key PodV.ObjectMeta'
    with "Hpod_meta_frags") as "%Hpods_nodup".
  iPureIntro.
  assert (Hdesired_pods_nodup : NoDup (desired_pod_keys sts)).
  { unfold desired_pod_keys, desired_ordinals.
    apply NoDup_fmap_2.
    - intros ordinal1 ordinal2 Hkey.
      apply (f_equal KKey.Name') in Hkey.
      simpl in Hkey.
      unfold desired_pod_name in Hkey.
      apply app_inv_head in Hkey.
      apply app_inv_head in Hkey.
      by apply decimal_string_inj in Hkey.
    - apply NoDup_seq. }
	split.
	- intros Hdist.
	  unfold match_distance, pod_distance, pvc_distance in Hdist.
	  assert (Hmissing_pods : length (missing_pod_keys sts pods) = 0%nat) by lia.
    assert (Halive_outdated_pods :
        length (filter is_pod_alive (outdated_pods sts pods)) = 0%nat) by lia.
    assert (Hbad_name_pods : length (bad_name_pods sts pods) = 0%nat) by lia.
    assert (Halive_condemned_pods :
        length (filter is_pod_alive (condemned_pods sts pods)) = 0%nat) by lia.
    assert (Hmissing_pvcs : length (missing_pvc_keys sts pvcs) = 0%nat) by lia.
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
	  assert (Hactual_pod_desired : ∀ pod,
	      pod ∈ pods → pod_key_is_desired sts (PodV.key pod)).
	  { intros pod Hpod.
	    destruct (decide (pod_key_is_desired sts (PodV.key pod))) as [Hdesired|Hnot_desired]; [done|].
	    exfalso.
	    assert (Hpod_condemned : pod ∈ condemned_pods sts pods).
	    { unfold condemned_pods.
	      apply list_elem_of_filter. split; [split; [by apply Hpod_good_name|exact Hnot_desired]|exact Hpod]. }
	    eapply (filter_length_zero_not_elem
	      is_pod_alive (condemned_pods sts pods) pod);
	      [exact Halive_condemned_pods|exact Hpod_condemned|by apply Hpods_alive]. }
	  assert (Hpods_perm : PodV.key <$> pods ≡ₚ desired_pod_keys sts).
	  { apply NoDup_Permutation; [exact Hpods_nodup|exact Hdesired_pods_nodup|].
	    intros key. split.
	    - intros Hactual.
	      apply list_elem_of_fmap_1 in Hactual as (pod & Hkey_eq & Hpod).
	      rewrite Hkey_eq. by apply Hactual_pod_desired.
	    - intros Hdesired. by apply Hdesired_pod_actual. }
	  split.
	  + split; [exact Hpods_perm|].
	    split.
	    * apply Forall_forall. intros pod Hpod.
	      rewrite <- list_elem_of_In in Hpod.
	      by apply Hpods_alive.
	    * apply Forall_forall. intros pod Hpod.
	      rewrite <- list_elem_of_In in Hpod.
	      destruct (decide (pod_match sts pod)) as [Hmatch|Hnot_match]; [exact Hmatch|].
	      exfalso.
	      assert (Hpod_needed : pod ∈ needed_pods sts pods).
	      { unfold needed_pods.
	        apply list_elem_of_filter. split; [by apply Hactual_pod_desired|exact Hpod]. }
	      assert (Hpod_outdated : pod ∈ outdated_pods sts pods).
	      { unfold outdated_pods.
	        apply list_elem_of_filter. split; [exact Hnot_match|exact Hpod_needed]. }
	      eapply (filter_length_zero_not_elem
	        is_pod_alive
	        (outdated_pods sts pods) pod);
	        [exact Halive_outdated_pods|exact Hpod_outdated|].
	      by apply Hpods_alive.
	  + intros key Hdesired.
	    destruct (decide (key ∈ PersistentVolumeClaimV.key <$> pvcs)) as [Hactual|Hnot_actual]; [done|].
	    exfalso.
	    eapply (filter_length_zero_not_elem
	      (λ key, key ∉ (PersistentVolumeClaimV.key <$> pvcs)) (desired_pvc_keys sts) key);
	      [exact Hmissing_pvcs|exact Hdesired|exact Hnot_actual].
	- intros [[Hpods_perm [Hpods_alive_forall Hpods_match_forall]] Hpvcs_match].
	  unfold match_distance, pod_distance, pvc_distance.
	  assert (Hmissing_pods_nil : missing_pod_keys sts pods = []).
	  { unfold missing_pod_keys.
	    apply filter_none. intros key Hdesired Hnot_actual.
	    apply Hnot_actual.
	    rewrite Hpods_perm. exact Hdesired. }
	  assert (Houtdated_pods_nil : outdated_pods sts pods = []).
	  { unfold outdated_pods.
	    apply filter_none. intros pod Hpod Hnot_match.
	    rewrite Forall_forall in Hpods_match_forall.
	    unfold needed_pods in Hpod.
	    apply list_elem_of_filter in Hpod as [_ Hpod].
	    rewrite list_elem_of_In in Hpod.
	    exact (Hnot_match (Hpods_match_forall pod Hpod)). }
	  assert (Hbad_name_pods_nil : bad_name_pods sts pods = []).
	  { unfold bad_name_pods.
	    apply filter_none. intros pod Hpod Hnot_member.
	    apply Hnot_member.
	    assert (Hkey_desired : PodV.key pod ∈ desired_pod_keys sts).
	    { rewrite -Hpods_perm. by apply list_elem_of_fmap_2. }
	    unfold desired_pod_keys in Hkey_desired.
	    apply list_elem_of_fmap_1 in Hkey_desired as (ordinal & Hkey_eq & _).
	    exists ordinal. exact Hkey_eq. }
	  assert (Halive_condemned_pods_nil : filter is_pod_alive (condemned_pods sts pods) = []).
	  { apply filter_none. intros pod Hpod Halive.
	    unfold condemned_pods in Hpod.
	    apply list_elem_of_filter in Hpod as ((_ & Hnot_desired) & Hpod).
	    apply Hnot_desired.
	    unfold pod_key_is_desired.
	    rewrite -Hpods_perm. by apply list_elem_of_fmap_2. }
	  assert (Hmissing_pvcs_nil : missing_pvc_keys sts pvcs = []).
	  { unfold missing_pvc_keys.
	    apply filter_none. intros key Hdesired Hnot_actual.
      apply Hnot_actual. by apply Hpvcs_match. }
    rewrite Hmissing_pods_nil Houtdated_pods_nil Hbad_name_pods_nil
      Halive_condemned_pods_nil Hmissing_pvcs_nil.
    done.
Qed.

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
  list_to_set (C:=gset KKey.t) (PodV.key <$> pods) ≠
    list_to_set (C:=gset KKey.t) (PodV.key <$> pods') ∨
  pod_meta_except_resource_version_changed pods pods' ∨
  pod_spec_changed pods pods'.

Lemma wp_syncStatefulSet_progress γ l (gv: schema.GroupVersion.t) namespace name sts dq pods pvcs :
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr apps_v1.SchemeGroupVersion) ↦□ gv ∗
      "Hown_sts_meta_frag" ∷ own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq sts.(StatefulSetV.ObjectMeta') ∗
      "Hown_sts_spec_frag" ∷ own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      "Hown_pod_frags" ∷ ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_pvc_frags" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
        own_spec_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PersistentVolumeClaimSpec pvc.(PersistentVolumeClaimV.Spec'))) ∗
      "Hown_children_frag" ∷ own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods)) ∗
      "Hown_reserved_missing_pod_keys" ∷ ([∗ list] key ∈ missing_pod_keys sts pods, own_reserved_frag γ key) ∗
      "Hown_reserved_missing_pvc_keys" ∷ ([∗ list] key ∈ missing_pvc_keys sts pvcs, own_reserved_frag γ key) ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hdeletion_timestamp_eq" ∷ ⌜ sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ (pods' : list PodV.t) (pvcs' : list PersistentVolumeClaimV.t) (err : interface.t), RET #err;
      (* We expect one of the three cases when reconcile finishes:
        (1) the current state (pods' and pvcs') matches the desired state encoded in sts,
        (2) the distance is reduced and a new reoncile is rescheduled because of changes to pods
        (3) the distance doesn't get increased because the controller needs to wait for some terminating pods
      *)
      ⌜ current_state_matches sts pods' pvcs' ∨
        pods_progress_observed pods pods' ∧ match_distance sts pods' pvcs' < match_distance sts pods pvcs ∨
        (∃ pod, pod ∈ pods ∧ ¬ is_pod_alive pod) ∧ match_distance sts pods' pvcs' ≤ match_distance sts pods pvcs ⌝ ∗
      own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq sts.(StatefulSetV.ObjectMeta') ∗
      own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      ([∗ list] pvc ∈ pvcs',
        own_meta_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
        own_spec_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PersistentVolumeClaimSpec pvc.(PersistentVolumeClaimV.Spec'))) ∗
      own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods'))
  }}}.
Proof.
Admitted.

End proof.
