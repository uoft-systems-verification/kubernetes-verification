From New.proof.controllers.statefulset Require Export reconcile_preservation.
From New.proof.controllers.statefulset Require Import release.
From New.proof.kubernetes_model Require Import get.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.statefulset.statefulset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.statefulset.statefulset.import_controller_Assumption.
#[local] Instance runtime_sem :
    code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
  controller.import_runtime_Assumption.
#[local] Instance runtime_object_underlying_eq :
    runtime.Object ≤u runtime.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
#[local] Instance meta_object_underlying_eq :
    meta_v1.Object ≤u meta_v1.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
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

Lemma pod_storage_view_filter_pending_perm sts pods1 pods2 :
  pod_storage_view <$> pods1 ≡ₚ pod_storage_view <$> pods2 →
  pod_storage_view <$> filter (pending_pod sts) pods1 ≡ₚ
    pod_storage_view <$> filter (pending_pod sts) pods2.
Proof.
  intros Hperm.
  set pending_view := (λ view,
    ¬ pod_view_alive view ∧
    pod_has_int32_member_name
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      (pod_view_meta view).(ObjectMetaV.Name')).
  assert (Hfilter : ∀ pods : list PodV.t,
      filter pending_view (pod_storage_view <$> pods) =
        pod_storage_view <$> filter (pending_pod sts) pods).
  { intros pods. apply filter_fmap_comm. intros pod.
    unfold pending_view. symmetry. apply pod_storage_view_pending. }
  pose proof (perm_filter pending_view _ _ Hperm) as Hfiltered.
  rewrite !Hfilter in Hfiltered. exact Hfiltered.
Qed.

Lemma pod_storage_view_filter_not_pending_perm sts pods1 pods2 :
  pod_storage_view <$> pods1 ≡ₚ pod_storage_view <$> pods2 →
  pod_storage_view <$> filter (λ pod, not (pending_pod sts pod)) pods1 ≡ₚ
    pod_storage_view <$>
      filter (λ pod, not (pending_pod sts pod)) pods2.
Proof.
  intros Hperm.
  set pending_view := (λ view,
    ¬ pod_view_alive view ∧
    pod_has_int32_member_name
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      (pod_view_meta view).(ObjectMetaV.Name')).
  set not_pending_view := (λ view, not (pending_view view)).
  assert (Hfilter : ∀ pods : list PodV.t,
      filter not_pending_view (pod_storage_view <$> pods) =
        pod_storage_view <$>
          filter (λ pod, not (pending_pod sts pod)) pods).
  { intros pods. apply filter_fmap_comm. intros pod.
    unfold not_pending_view, pending_view.
    rewrite pod_storage_view_pending. done. }
  pose proof (perm_filter not_pending_view _ _ Hperm) as Hfiltered.
  rewrite !Hfilter in Hfiltered. exact Hfiltered.
Qed.

Lemma replace_reserved_storage_perm originals reserved pods :
  pod_storage_view <$> originals ≡ₚ pod_storage_view <$> reserved →
  NoDup (PodV.key <$> reserved) →
  NoDup (PodV.key <$> pods) →
  reserved ⊆ pods →
  pod_storage_view <$>
      (originals ++ filter (pod_key_not_reserved reserved) pods) ≡ₚ
    pod_storage_view <$> pods.
Proof.
  intros Horiginal Hreserved_nodup Hpods_nodup Hsubset.
  set selected := (λ pod : PodV.t,
    PodV.key pod ∈ PodV.key <$> reserved).
  assert (filter selected pods ≡ₚ reserved) as Hselected.
  { apply NoDup_Permutation.
    - apply list.NoDup_filter. by apply NoDup_fmap_1 in Hpods_nodup.
    - by apply NoDup_fmap_1 in Hreserved_nodup.
    - intros pod. split.
      + intros Hpod. apply list_elem_of_filter in Hpod as [Hkey Hpod].
        apply list_elem_of_fmap_1 in Hkey as
          (reserved_pod & Hkey & Hreserved_pod).
        assert (pod = reserved_pod) as ->.
        { eapply NoDup_fmap_inj_on; try exact Hpods_nodup.
          - exact Hpod.
          - by apply Hsubset.
          - exact Hkey. }
        exact Hreserved_pod.
      + intros Hpod. apply list_elem_of_filter. split.
        * by apply list_elem_of_fmap_2.
        * by apply Hsubset. }
  assert (filter (pod_key_not_reserved reserved) pods =
      filter (λ pod, not (selected pod)) pods) as Hnot_selected by done.
  rewrite Hnot_selected fmap_app.
  eapply Permutation_trans.
  - apply Permutation_app; last reflexivity.
    etrans; first exact Horiginal.
    symmetry. by apply Permutation_map.
  - rewrite -fmap_app. apply Permutation_map.
    apply filter_partition_perm.
Qed.

Lemma filter_unreserved_pending_perm sts pods :
  NoDup (PodV.key <$> pods) →
  filter (pod_key_not_reserved (filter (pending_pod sts) pods)) pods ≡ₚ
    filter (λ pod, not (pending_pod sts pod)) pods.
Proof.
  intros Hnodup. apply NoDup_Permutation.
  - apply list.NoDup_filter. by apply NoDup_fmap_1 in Hnodup.
  - apply list.NoDup_filter. by apply NoDup_fmap_1 in Hnodup.
  - intros pod. split.
    + intros Hpod. apply list_elem_of_filter in Hpod as
        [Hunreserved Hpod].
      apply list_elem_of_filter. split; last exact Hpod.
      intros Hpending. apply Hunreserved.
      apply list_elem_of_fmap_2. apply list_elem_of_filter. done.
    + intros Hpod. apply list_elem_of_filter in Hpod as
        [Hnot_pending Hpod].
      apply list_elem_of_filter. split; last exact Hpod.
      intros Hkey.
      apply list_elem_of_fmap_1 in Hkey as
        (pending & Hkey & Hpending).
      apply list_elem_of_filter in Hpending as
        [Hpending Hpending_in].
      assert (pod = pending) as ->.
      { eapply NoDup_fmap_inj_on; try exact Hnodup; done. }
      exact (Hnot_pending Hpending).
Qed.

Lemma filter_filter_commute {A} (P Q : A → Prop)
    `{!∀ x, Decision (P x)} `{!∀ x, Decision (Q x)} (xs : list A) :
  filter P (filter Q xs) = filter Q (filter P xs).
Proof.
  rewrite !list_filter_filter.
  apply list_filter_iff. intros x. tauto.
Qed.

Lemma replace_reserved_unreserved_eq originals reserved pods :
  PodV.key <$> originals ≡ₚ PodV.key <$> reserved →
  filter (pod_key_not_reserved originals)
      (originals ++ filter (pod_key_not_reserved reserved) pods) =
    filter (pod_key_not_reserved reserved) pods.
Proof.
  intros Hkeys. rewrite list.filter_app.
  assert (filter (pod_key_not_reserved originals) originals = [])
    as ->.
  { apply filter_none. intros pod Hpod Hunreserved. apply Hunreserved.
    by apply list_elem_of_fmap_2. }
  simpl. apply filter_all. intros pod Hpod.
  apply list_elem_of_filter in Hpod as [Hunreserved Hpod].
  unfold pod_key_not_reserved in *. intros Hkey.
  apply Hunreserved.
  rewrite list_elem_of_In.
  eapply Permutation_in; first exact Hkeys.
  by rewrite -list_elem_of_In.
Qed.

Lemma wp_syncStatefulSet_preservation γ l namespace name sts dq pending_dqs pods pvcs :
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hown_sts_meta_frag" ∷ own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq sts.(StatefulSetV.ObjectMeta') ∗
      "Hown_sts_spec_frag" ∷ own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      "Hown_terminating_pod_frags" ∷
        ([∗ list] pod;pending_dq ∈ filter (pending_pod sts) pods;pending_dqs,
          own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') pending_dq pod.(PodV.ObjectMeta') ∗
          own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') pending_dq (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_other_pod_frags" ∷
        ([∗ list] pod ∈ filter (λ pod, not (pending_pod sts pod)) pods,
          own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
          own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_pvc_frags" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      "Hown_children_frag" ∷ own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods)) ∗
      "Hown_reserved_missing_pod_keys" ∷ ([∗ list] key ∈ missing_pod_keys sts pods, own_reserved_frag γ key) ∗
      "Hown_reserved_missing_pvc_keys" ∷ ([∗ list] key ∈ missing_pvc_keys sts pvcs, own_reserved_frag γ key) ∗
      "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
      "%Hpending_nonempty" ∷
        ⌜ filter (pending_pod sts) pods ≠ [] ⌝ ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement sts ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hdeletion_timestamp_eq" ∷ ⌜ sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ (pods' : list PodV.t) (pvcs' : list PersistentVolumeClaimV.t)
      (err : interface.t), RET #err;
      ⌜ match_distance sts pods' pvcs' ≤ match_distance sts pods pvcs ⌝ ∗
      ⌜ filter (pending_pod sts) pods ⊆ filter (pending_pod sts) pods' ⌝ ∗
      own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq sts.(StatefulSetV.ObjectMeta') ∗
      own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      ([∗ list] pod;pending_dq ∈ filter (pending_pod sts) pods;pending_dqs,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') pending_dq pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') pending_dq (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      ([∗ list] pod ∈ filter (λ pod,
          PodV.key pod ∉ PodV.key <$> filter (pending_pod sts) pods) pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      ([∗ list] pvc ∈ pvcs',
        own_meta_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods'))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iAssert (is_pkg_init common) as "#Hcommon_init".
  { iPkgInit. }
  iAssert (is_pkg_init apimodel) as "#Hapimodel_init".
  { iPkgInit. }
  wp_apply (wp_State__StatefulSetGet with
    "[$Hown_sts_meta_frag $Hown_sts_spec_frag]").
  { iFrame "#". iPureIntro.
    rewrite /StatefulSetV.key /StatefulSetV.meta_key
      Hnamespace_eq Hname_eq. done. }
  iIntros (set_l set) "Hget". iNamedPrefix "Hget" "Hget_".
  iRename "Hget_Hdeepown_l" into "Hset".
  iRename "Hget_Hown_meta_frag" into "Hown_sts_meta_frag".
  iRename "Hget_Hown_spec_frag" into "Hown_sts_spec_frag".
  wp_auto.
  wp_apply (wp_IsNotFound interface.nil with "[]").
  replace (bool_decide (not_found_error interface.nil)) with false by
    (symmetry; apply bool_decide_false; exact not_found_error_nil).
  wp_auto.

  rewrite KObjectV.valid_eq_valid2 in Hget_Hvalid'.
  assert (StatefulSetV.valid set) as Hset_valid by exact Hget_Hvalid'.
  destruct Hset_valid as
    (Hset_typemeta_valid & Hset_resource_version_valid &
      Hset_meta_valid & Hset_spec_valid & Hset_status_valid).
  assert (Hset_valid : StatefulSetV.valid set).
  { split_and!; done. }
  destruct Hset_typemeta_valid as [_ Hset_kind_valid].
  pose proof (valid_kind_slash_free _ Hset_kind_valid) as Hkind_slash_free.
  pose proof (ObjectMetaV.valid_namespace_of_valid _ Hset_meta_valid)
    as Hnamespace_valid.
  pose proof (ObjectMetaV.valid_name_of_valid _ Hset_meta_valid)
    as Hname_valid.
  pose proof (ObjectMetaV.valid_uid_of_valid _ Hset_meta_valid)
    as Huid_valid.
  pose proof (valid_namespace_slash_free _ Hnamespace_valid)
    as Hnamespace_slash_free.
  pose proof (valid_name_slash_free _ Hname_valid) as Hname_slash_free.
  pose proof (valid_uid_slash_free _ Huid_valid) as Huid_slash_free.
  assert (Hset_view :
      statefulset_storage_view sts = statefulset_storage_view set).
  { unfold statefulset_storage_view.
    unfold ObjectMetaV.equiv_except_resource_version in Hget_Hmeta_eq.
    rewrite Hget_Hspec_eq. f_equal. symmetry. exact Hget_Hmeta_eq. }
  assert (Hset_key : StatefulSetV.key sts = StatefulSetV.key set)
    by exact Hget_Hkey_eq.
  assert (Hset_uid :
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') =
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')).
  { symmetry. apply ObjectMetaV.equiv_except_resource_version_uid.
    exact Hget_Hmeta_eq. }

  set pending_original := filter (pending_pod sts) pods.
  set other_original := filter (λ pod, not (pending_pod sts pod)) pods.
  set spec_pods := pending_original ++ other_original.
  set spec_dqs := pending_dqs ++
    replicate (length other_original) (1 : dfrac).
  assert (Hspec_perm : spec_pods ≡ₚ pods).
  { unfold spec_pods, pending_original, other_original.
    apply filter_partition_perm. }
  assert (Hspec_key_perm : PodV.key <$> spec_pods ≡ₚ PodV.key <$> pods).
  { by apply Permutation_map. }
  assert (Hspec_nodup : NoDup (PodV.key <$> spec_pods)).
  { rewrite Hspec_key_perm. exact Hpods_nodup. }
  iAssert (([∗ list] pod;pod_dq ∈ other_original;
      replicate (length other_original) (1 : dfrac),
      own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') pod_dq
        pod.(PodV.ObjectMeta') ∗
      own_spec_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') pod_dq
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))))%I
    with "[Hown_other_pod_frags]" as "Hother_original".
  { rewrite big_sepL2_replicate_r; [done|].
    iExact "Hown_other_pod_frags". }
  iAssert (([∗ list] pod;pod_dq ∈ spec_pods;spec_dqs,
      own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') pod_dq
        pod.(PodV.ObjectMeta') ∗
      own_spec_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') pod_dq
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))))%I
    with "[Hown_terminating_pod_frags Hother_original]"
    as "Hspec_frags".
  { unfold spec_pods, spec_dqs.
    iApply (big_sepL2_app with "Hown_terminating_pod_frags").
    iApply (big_sepL2_mono with "Hother_original").
    iIntros (k pod pod_dq Hpod Hpod_dq) "Hpod".
    iExact "Hpod". }
  assert (list_to_set (C:=gset KKey.t) (PodV.key <$> spec_pods) =
      filter (λ key, key.(KKey.Kind') = "Pod"%go)
        (list_to_set (C:=gset KKey.t) (PodV.key <$> pods))) as Hdom_eq.
  { rewrite Hspec_key_perm. apply set_eq. intros key.
    rewrite elem_of_filter. split.
    - intros Hkey. split; last done.
      apply elem_of_list_to_set in Hkey.
      apply list_elem_of_fmap_1 in Hkey as (pod & -> & _).
      rewrite /PodV.key /PodV.meta_key /PodV.kind //.
    - intros [_ Hkey]. exact Hkey. }
  iEval (rewrite Hset_key Hset_uid) in "Hown_children_frag".

  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_meta &
      Hset_spec & Hset_status)".
  wp_apply (common.wp_FilterPodsByOwner_with_spec
    _ _ _ _ _ _ spec_pods spec_dqs 1
    (list_to_set (PodV.key <$> pods))
    with "[$Hset_meta $Hspec_frags $Hown_children_frag]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (all_sl all_ptrs all_pods pod_dq)
    "(Hall_sl & Hall_pods & %Hall_storage_spec_perm & %Hall_valid &
      %Hall_parent_refs & %Hall_nodup & Hset_meta &
      Hspec_frags & Hown_children_frag)".
  assert (Hall_storage_perm :
      pod_storage_view <$> all_pods ≡ₚ pod_storage_view <$> pods).
  { etrans; first exact Hall_storage_spec_perm.
    by apply Permutation_map. }
  pose proof (pod_storage_view_perm_keys _ _ Hall_storage_perm)
    as Hall_key_perm.
  assert (Hall_namespaces : Forall
      (λ pod,
        pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace'))
      all_pods).
  { eapply Forall_impl; last exact Hall_parent_refs.
    intros pod Hparent.
    by apply (meta_parent_ref_namespace _ _ _ Hparent). }
  assert (Hall_name_lengths : Forall
      (λ pod,
        Z.of_nat
          (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max)
      all_pods).
  { eapply Forall_impl; last exact Hall_valid.
    intros pod Hpod_valid.
    by apply pod_name_length_le_go_int_max_of_valid. }
  iAssert (own_children_frag γ (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (list_to_set (PodV.key <$> all_pods)))%I
    with "[Hown_children_frag]" as "Hown_children_frag".
  { rewrite Hall_key_perm. iExact "Hown_children_frag". }
  iDestruct (big_sepL2_length with "Hspec_frags") as %Hspec_len.
  assert (Hpending_len : length pending_original = length pending_dqs).
  { unfold spec_pods, spec_dqs in Hspec_len.
    rewrite !length_app length_replicate in Hspec_len. lia. }
  iEval (unfold spec_pods, spec_dqs) in "Hspec_frags".
  iDestruct (big_sepL2_app_inv with "Hspec_frags") as
    "[Hown_terminating_pod_frags Hother_original]".
  { left. exact Hpending_len. }
  iEval (rewrite big_sepL2_replicate_r; [done|]) in "Hother_original".

  iDestruct "Hset_meta" as (set_meta_c)
    "[Hset_meta_field Hset_meta_deepown]".
  iNamedPrefix "Hset_meta_deepown" "Hset_meta_".
  assert (set_meta_c.(v1.ObjectMeta.DeletionTimestamp') = null)
    as Hset_deletion_timestamp_null.
  { apply Hset_meta_Hdeepown_deletiontimestamp_none.
    rewrite (ObjectMetaV.equiv_except_resource_version_deletion_timestamp
      _ _ Hget_Hmeta_eq).
    exact Hdeletion_timestamp_eq. }
  assert (set.(StatefulSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') =
      None) as Hset_deletion_timestamp_none.
  { rewrite (ObjectMetaV.equiv_except_resource_version_deletion_timestamp
      _ _ Hget_Hmeta_eq).
    exact Hdeletion_timestamp_eq. }
  wp_auto. rewrite Hset_deletion_timestamp_null. wp_auto.
  iEval (rewrite Hset_deletion_timestamp_none) in
    "Hset_meta_Hdeepown_deletiontimestamp_some".
  iAssert (ObjectMetaV.deepown set_meta_c
      set.(StatefulSetV.ObjectMeta') 1)
    with "[Hset_meta_Hdeepown_creationtimestamp
      Hset_meta_Hdeepown_deletiongraceperiodseconds_some
      Hset_meta_Hdeepown_labels_some Hset_meta_Hdeepown_annotations_some
      Hset_meta_Hdeepown_ownerreferences_some
      Hset_meta_Hdeepown_finalizers_some
      Hset_meta_Hdeepown_managedfields_some]" as "Hset_meta_deepown".
  { rewrite /ObjectMetaV.deepown Hset_deletion_timestamp_none.
    iFrame "%". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
      set.(StatefulSetV.ObjectMeta') 1)
    with "[Hset_meta_field Hset_meta_deepown]" as "Hset_meta".
  { iExists set_meta_c. iFrame. }
  iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
    with "[$Hset_typemeta $Hset_meta $Hset_spec $Hset_status]") as "Hset".

  assert (Hpending_original_set :
      filter (pending_pod set) pods = pending_original).
  { unfold pending_original. apply list_filter_iff. intros pod.
    symmetry. apply statefulset_storage_view_pending_pod. exact Hset_view. }
  assert (Hother_original_set :
      filter (λ pod, not (pending_pod set pod)) pods = other_original).
  { unfold other_original. apply list_filter_iff. intros pod.
    pose proof (statefulset_storage_view_pending_pod sts set pod Hset_view)
      as Hpending. split; intros Hnot Hpending'; apply Hnot.
    - by apply (proj1 Hpending).
    - by apply (proj2 Hpending). }
  set nonpending_all :=
    filter (λ pod, not (pending_pod set pod)) all_pods.
  assert (Hnonpending_storage_perm :
      pod_storage_view <$> nonpending_all ≡ₚ
        pod_storage_view <$> other_original).
  { unfold nonpending_all.
    pose proof (pod_storage_view_filter_not_pending_perm
      set all_pods pods Hall_storage_perm) as Hperm.
    rewrite Hother_original_set in Hperm. exact Hperm. }
  iAssert (([∗ list] pod ∈ nonpending_all,
      own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod.(PodV.ObjectMeta') ∗
      own_spec_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))))%I
    with "[Hother_original]" as "Hnonpending_frags".
  { rewrite (own_pod_frags_as_storage_views γ 1 nonpending_all).
    rewrite Hnonpending_storage_perm.
    rewrite -own_pod_frags_as_storage_views.
    iExact "Hother_original". }

  set Good := (λ pod : PodV.t,
    pod_has_int32_member_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
  set good_pods := filter Good all_pods.
  set bad_pods := filter (λ pod, ¬ Good pod) all_pods.
  set good_nonpending := filter Good nonpending_all.
  iEval (rewrite big_sepL_sep) in "Hnonpending_frags".
  iDestruct "Hnonpending_frags" as
    "[Hnonpending_meta Hnonpending_spec]".
  iDestruct (big_sepL_filter_partition Good _ nonpending_all
    with "Hnonpending_meta") as "[Hgood_meta Hbad_meta]".
  iDestruct (big_sepL_filter_partition Good _ nonpending_all
    with "Hnonpending_spec") as "[Hgood_spec Hbad_spec]".
  iEval (fold good_nonpending) in "Hgood_meta Hgood_spec".
  assert (Hbad_nonpending :
      filter (λ pod, ¬ Good pod) nonpending_all = bad_pods).
  { unfold nonpending_all, bad_pods.
    apply filter_filter_absorb. intros pod Hbad.
    intros Hpending. apply Hbad. exact (proj2 Hpending). }
  iEval (rewrite Hbad_nonpending) in "Hbad_meta Hbad_spec".
  assert (Hbad_definition : bad_pods = pods_with_bad_names set all_pods).
  { unfold bad_pods, pods_with_bad_names, Good. done. }
  assert (Hbad_releaseable : Forall
      (λ pod,
        PodV.valid pod ∧
        meta_parent_ref pod.(PodV.ObjectMeta') =
          Some (StatefulSetV.key set,
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')) ∧
        PodV.key pod ∈
          list_to_set (C:=gset KKey.t) (PodV.key <$> all_pods))
      bad_pods).
  { unfold bad_pods.
    apply Forall_filter.
    pose proof (Forall_and Hall_valid Hall_parent_refs) as Hvalid_parent.
    pose proof (Forall_fmap_list_to_set PodV.key all_pods) as Hkeys.
    pose proof (Forall_and Hvalid_parent Hkeys) as Hall.
    eapply Forall_impl; last exact Hall.
    intros pod [[Hvalid Hparent] Hkey]. split_and!; done. }
  wp_apply (wp_releasePodsWithBadNames γ l set_l all_sl
    set all_ptrs all_pods bad_pods
    (list_to_set (PodV.key <$> all_pods)) 1 pod_dq
    with "[$Hset $Hall_sl $Hall_pods $Hbad_meta $Hbad_spec
      $Hown_children_frag]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros "Hrelease". iNamedPrefix "Hrelease" "Hrelease_".
  wp_auto.
  iAssert (own_children_frag γ (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (list_to_set (PodV.key <$> good_pods)))%I
    with "[Hrelease_Hown_children]" as "Hgood_children".
  { unfold good_pods, bad_pods.
    rewrite (list_to_set_fmap_filter_difference PodV.key Good all_pods
      Hall_nodup).
    iExact "Hrelease_Hown_children". }
  iCombine "Hgood_meta Hgood_spec" as "Hgood_nonpending_frags".
  iEval (rewrite -big_sepL_sep) in "Hgood_nonpending_frags".
  wp_apply (wp_filterPodsForStatefulSet set_l all_sl set all_ptrs
    all_pods 1 pod_dq
    with "[$Hrelease_Hset $Hrelease_Hpods_sl $Hrelease_Hpods]").
  { iPureIntro. intros pod Hpod.
    rewrite Forall_forall in Hall_name_lengths.
    apply Hall_name_lengths. by rewrite -list_elem_of_In. }
  iIntros (good_sl good_ptrs)
    "(Hset & Hall_sl & Hgood_sl & Hgood_pods)".
  iEval (fold Good; fold good_pods) in "Hgood_pods".

  assert (Hgood_valid : Forall PodV.valid good_pods).
  { unfold good_pods. by apply Forall_filter. }
  assert (Hgood_members : Forall Good good_pods).
  { unfold good_pods. apply Forall_forall. intros pod Hpod.
    rewrite -list_elem_of_In in Hpod.
    by apply list_elem_of_filter in Hpod as [Hgood _]. }
  assert (Hgood_member_keys : Forall
      (pod_has_int32_member_key set) good_pods).
  { apply Forall_forall. intros pod Hpod.
    rewrite -list_elem_of_In in Hpod.
    apply list_elem_of_filter in Hpod as [Hgood Hpod].
    split; first last.
    - exact Hgood.
    - rewrite Forall_forall in Hall_namespaces.
      apply Hall_namespaces. by rewrite -list_elem_of_In. }
  assert (Hgood_nodup : NoDup (PodV.key <$> good_pods)).
  { unfold good_pods. by apply NoDup_fmap_filter. }
  set pending_actual := filter (pending_pod set) good_pods.
  assert (Hpending_good_all :
      pending_actual = filter (pending_pod set) all_pods).
  { unfold pending_actual, good_pods.
    apply filter_filter_absorb. intros pod Hpending. exact (proj2 Hpending). }
  assert (Hpending_storage_perm :
      pod_storage_view <$> pending_actual ≡ₚ
        pod_storage_view <$> pending_original).
  { rewrite Hpending_good_all.
    pose proof (pod_storage_view_filter_pending_perm
      set all_pods pods Hall_storage_perm) as Hperm.
    rewrite Hpending_original_set in Hperm. exact Hperm. }
  assert (Hpending_actual_nonempty : pending_actual ≠ []).
  { intros Hempty. rewrite Hempty /= in Hpending_storage_perm.
    pose proof (Permutation_length Hpending_storage_perm) as Hlen.
    rewrite map_length in Hlen.
    destruct pending_original eqn:Hpending_original; simpl in *; [|lia].
    apply Hpending_nonempty.
    unfold pending_original in Hpending_original.
    exact Hpending_original. }
  assert (Hpending_actual_nodup :
      NoDup (PodV.key <$> pending_actual)).
  { unfold pending_actual. by apply NoDup_fmap_filter. }
  assert (Hpending_actual_subset : pending_actual ⊆ good_pods).
  { intros pod Hpod. apply list_elem_of_filter in Hpod as [_ Hpod]. done. }
  assert (Hgood_nonpending_eq :
      good_nonpending =
        filter (λ pod, not (pending_pod set pod)) good_pods).
  { unfold good_nonpending, nonpending_all, good_pods.
    apply filter_filter_commute. }
  iEval (rewrite Hgood_nonpending_eq) in "Hgood_nonpending_frags".
  iAssert (own_unreserved_pods γ pending_actual good_pods)
    with "[Hgood_nonpending_frags]" as "Hgood_frags".
  { unfold own_unreserved_pods, pending_actual.
    rewrite (filter_unreserved_pending_perm set good_pods Hgood_nodup).
    iExact "Hgood_nonpending_frags". }
  assert (Hinput_requirement_set : input_requirement set).
  { apply (proj1
      (statefulset_storage_view_input_requirement sts set Hset_view)).
    exact Hinput_requirement. }
  assert (Hmissing_pods :
      missing_pod_keys set good_pods = missing_pod_keys sts pods).
  { unfold good_pods.
    rewrite (filter_int32_member_names_eq set all_pods Hall_namespaces).
    rewrite missing_pod_keys_filter_int32_members.
    rewrite (missing_pod_keys_storage_view_perm set all_pods pods
      Hall_storage_perm).
    apply statefulset_storage_view_missing_pod_keys.
    symmetry. exact Hset_view. }
  assert (Hmissing_pvcs :
      missing_pvc_keys set pvcs = missing_pvc_keys sts pvcs).
  { apply statefulset_storage_view_missing_pvc_keys.
    symmetry. exact Hset_view. }
  iEval (rewrite -Hmissing_pods) in "Hown_reserved_missing_pod_keys".
  iEval (rewrite -Hmissing_pvcs) in "Hown_reserved_missing_pvc_keys".
  wp_auto.
  wp_apply (wp_reconcileReplicas_preservation γ l set_l good_sl set
    good_ptrs good_pods pending_actual pvcs 1 pod_dq
    with "[$Hset $Hgood_sl $Hgood_pods $Hgood_frags
      $Hown_pvc_frags $Hgood_children
      $Hown_reserved_missing_pod_keys $Hown_reserved_missing_pvc_keys]").
  { iFrame "#". iPureIntro. split_and!; try done. }
  iIntros (pods1 pvcs') "Hreconcile".
  iNamedPrefix "Hreconcile" "Hreconcile_". wp_auto.

  set pods' := pending_original ++
    filter (pod_key_not_reserved pending_actual) pods1.
  assert (Hfinal_storage_perm :
      pod_storage_view <$> pods' ≡ₚ pod_storage_view <$> pods1).
  { unfold pods'. eapply replace_reserved_storage_perm; try done. }
  pose proof (pod_storage_view_perm_keys _ _ Hpending_storage_perm)
    as Hpending_key_perm.
  assert (Hpending_key_perm' :
      PodV.key <$> pending_original ≡ₚ PodV.key <$> pending_actual).
  { symmetry. exact Hpending_key_perm. }
  pose proof (pod_storage_view_perm_keys _ _ Hfinal_storage_perm)
    as Hfinal_key_perm.
  iAssert (([∗ list] pod ∈ filter (λ pod,
      PodV.key pod ∉ PodV.key <$> pending_original) pods',
      own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod.(PodV.ObjectMeta') ∗
      own_spec_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))))%I
    with "[Hreconcile_Hown_pods]" as "Hfinal_pod_frags".
  { unfold pods'.
    rewrite (replace_reserved_unreserved_eq pending_original
      pending_actual pods1 Hpending_key_perm').
    iExact "Hreconcile_Hown_pods". }
  assert (Hpending_preserved :
      filter (pending_pod sts) pods ⊆ filter (pending_pod sts) pods').
  { intros pod Hpod. apply list_elem_of_filter in Hpod as [Hpending Hpod_in].
    apply list_elem_of_filter. split; first exact Hpending.
    unfold pods', pending_original. apply elem_of_app. left.
    apply list_elem_of_filter. done. }
  assert (Hinitial_distance :
      match_distance set all_pods pvcs = match_distance sts pods pvcs).
  { rewrite (match_distance_storage_view_perm set all_pods pods pvcs
      Hall_storage_perm).
    apply statefulset_storage_view_match_distance.
    symmetry. exact Hset_view. }
  assert (Hbad_distance :
      match_distance set all_pods pvcs =
        (match_distance set good_pods pvcs + length bad_pods)%nat).
  { unfold match_distance. rewrite pod_distance_filter_int32_members.
    assert (filter (pod_has_int32_member_key set) all_pods = good_pods)
      as Hgood_filter.
    { rewrite -(filter_int32_member_names_eq set all_pods Hall_namespaces).
      done. }
    assert (bad_name_pods set all_pods = bad_pods) as Hbad_filter.
    { symmetry. unfold bad_pods, Good.
      apply filter_bad_int32_member_names_eq. exact Hall_namespaces. }
    rewrite Hgood_filter Hbad_filter. lia. }
  assert (Hfinal_distance :
      match_distance sts pods' pvcs' = match_distance set pods1 pvcs').
  { transitivity (match_distance set pods' pvcs').
    - apply statefulset_storage_view_match_distance. exact Hset_view.
    - apply match_distance_storage_view_perm. exact Hfinal_storage_perm. }
  assert (Hdistance :
      match_distance sts pods' pvcs' ≤ match_distance sts pods pvcs).
  { rewrite Hfinal_distance -Hinitial_distance. lia. }
  iEval (rewrite -Hfinal_key_perm -Hset_key -Hset_uid) in
    "Hreconcile_Hown_children".
  iApply ("HΦ" $! pods' pvcs' interface.nil).
  iFrame "Hown_sts_meta_frag Hown_sts_spec_frag
    Hown_terminating_pod_frags Hfinal_pod_frags
    Hreconcile_Hown_pvcs Hreconcile_Hown_children".
  iPureIntro. split; done.
Qed.

End proof.
