From New.proof.controllers.statefulset Require Export reconcile_stability.
From New.proof.controllers.statefulset Require Export top_level.
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

Lemma wp_syncStatefulSet_stability γ l namespace name sts dq pods pvcs :
  ⊢ syncStatefulSet_stability_spec γ l namespace name sts dq pods pvcs.
Proof.
  unfold syncStatefulSet_stability_spec.
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
  pose proof (valid_kind_slash_free _ Hset_kind_valid)
    as Hkind_slash_free.
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

  assert (NoDup (PodV.key <$> pods)) as Hpods_nodup.
  { pose proof (proj1 (proj1 Hmatch)) as Hkeys.
    rewrite Hkeys. apply desired_pod_keys_nodup. }
  assert (list_to_set (C:=gset KKey.t) (PodV.key <$> pods) =
      filter (λ key, key.(KKey.Kind') = "Pod"%go)
        (list_to_set (C:=gset KKey.t) (PodV.key <$> pods))) as Hdom_eq.
  { apply set_eq. intros key. rewrite elem_of_filter. split.
    - intros Hkey. split; last done.
      apply elem_of_list_to_set in Hkey.
      apply list_elem_of_fmap_1 in Hkey as (pod & -> & _).
      rewrite /PodV.key /PodV.meta_key /PodV.kind //.
    - intros [_ Hkey]. exact Hkey. }
  iEval (rewrite Hset_key Hset_uid) in "Hown_children_frag".

  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_meta &
      Hset_spec & Hset_status)".
  wp_apply (common.wp_FilterPodsByOwner_uniform_with_spec
    _ _ _ _ _ _ pods dq dq
    (list_to_set (PodV.key <$> pods))
    with "[$Hset_meta $Hown_pod_frags $Hown_children_frag]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (all_sl all_ptrs all_pods pod_dq)
    "(Hall_sl & Hall_pods & %Hall_storage_perm & %Hall_valid &
      %Hall_parent_refs & %Hall_nodup & Hset_meta &
      Hall_frags & Hown_children_frag)".
  pose proof (pod_storage_view_perm_keys _ _ Hall_storage_perm)
    as Hall_key_perm.
  assert (Hall_name_lengths : Forall
      (λ pod,
        Z.of_nat
          (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max)
      all_pods).
  { eapply Forall_impl; last exact Hall_valid.
    intros pod Hpod_valid.
    by apply pod_name_length_le_go_int_max_of_valid. }
  iAssert (own_children_frag γ (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq
      (list_to_set (PodV.key <$> all_pods)))%I
    with "[Hown_children_frag]" as "Hown_children_frag".
  { rewrite Hall_key_perm. iExact "Hown_children_frag". }

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
    with "[$Hset_typemeta $Hset_meta $Hset_spec $Hset_status]")
    as "Hset".

  assert (Hmatch_all_sts : current_state_matches sts all_pods pvcs).
  { apply (proj2 (current_state_matches_storage_view_perm
      sts all_pods pods pvcs Hall_storage_perm)).
    exact Hmatch. }
  assert (Hmatch_all : current_state_matches set all_pods pvcs).
  { apply (proj1
      (statefulset_storage_view_current_state_matches
        sts set all_pods pvcs Hset_view)).
    exact Hmatch_all_sts. }
  pose proof (pods_match_members set all_pods (proj1 Hmatch_all))
    as Hall_members.
  assert (Hall_member_names : Forall (λ pod,
      pod_has_int32_member_name
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) all_pods).
  { eapply Forall_impl; last exact Hall_members.
    intros pod Hmember. exact (proj2 Hmember). }

  wp_apply (wp_releasePodsWithBadNames_stability
    set_l all_sl set all_ptrs all_pods 1 pod_dq
    with "[$Hset $Hall_sl $Hall_pods]").
  { iFrame "#". iPureIntro. split; done. }
  iIntros "(Hset & Hall_sl & Hall_pods)". wp_auto.
  wp_apply (wp_filterPodsForStatefulSet set_l all_sl set all_ptrs
    all_pods 1 pod_dq with "[$Hset $Hall_sl $Hall_pods]").
  { iPureIntro. intros pod Hpod.
    rewrite Forall_forall in Hall_name_lengths.
    apply Hall_name_lengths. by rewrite -list_elem_of_In. }
  iIntros (good_sl good_ptrs)
    "(Hset & Hall_sl & Hgood_sl & Hgood_pods)".
  assert (Hgood_eq : filter (λ pod,
      pod_has_int32_member_name
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) all_pods = all_pods).
  { apply filter_all. rewrite Forall_forall in Hall_member_names.
    intros pod Hpod. apply Hall_member_names.
    by rewrite -list_elem_of_In. }
  iEval (rewrite Hgood_eq) in "Hgood_pods".

  wp_auto.
  wp_apply (wp_reconcileReplicas_stability γ l set_l good_sl set
    good_ptrs all_pods pvcs 1 pod_dq dq dq dq
    with "[$Hset $Hgood_sl $Hgood_pods $Hall_frags
      $Hown_pvc_frags $Hown_children_frag]").
  { iFrame "# %". }
  iIntros
    "(Hset & Hgood_sl & Hgood_pods & Hall_frags &
      Hown_pvc_frags & Hown_children_frag)".
  wp_auto.

  iAssert (([∗ list] pod ∈ pods,
      own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq
        pod.(PodV.ObjectMeta') ∗
      own_spec_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))))%I
    with "[Hall_frags]" as "Hown_pod_frags".
  { iAssert (([∗ list] view ∈ pod_storage_view <$> all_pods,
        own_pod_storage_view_frag γ dq view))%I
      with "[Hall_frags]" as "Hall_view_frags".
    { rewrite -own_pod_frags_as_storage_views.
      iExact "Hall_frags". }
    iAssert (([∗ list] view ∈ pod_storage_view <$> pods,
        own_pod_storage_view_frag γ dq view))%I
      with "[Hall_view_frags]" as "Hpod_view_frags".
    { rewrite -Hall_storage_perm. iExact "Hall_view_frags". }
    rewrite own_pod_frags_as_storage_views.
    iExact "Hpod_view_frags". }
  iEval (rewrite Hall_key_perm -Hset_key -Hset_uid) in
    "Hown_children_frag".
  iApply ("HΦ" $! interface.nil).
  iFrame "Hown_sts_meta_frag Hown_sts_spec_frag
    Hown_pod_frags Hown_pvc_frags Hown_children_frag".
Qed.

End proof.
