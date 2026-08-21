From New.proof.controllers.replicaset Require Export progress.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.replicaset.replicaset.import_controller_Assumption.
#[local] Instance runtime_sem : code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
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

Lemma wp_syncReplicaSet_preservation γ l namespace name rs dq pods :
  ⊢ preservation_spec γ l namespace name rs dq pods.
Proof.
  unfold preservation_spec.
  wp_start as "H". iNamed "H". iNamed "Hresources".
  iEval (simpl) in "Hown_rs_meta_frag Hown_rs_spec_frag Hown_pod_meta_frags
    Hown_children_frag Hown_terminating_children_frag".
  iDestruct "Hown_terminating_children_frag" as (phase) "Hown_terminating_children_frag".
  unfold input_requirement in Hinput_requirement.
  destruct Hinput_requirement as [Hrs_name_short Hrs_template_finalizers_valid].
  wp_auto.
  iAssert (is_pkg_init common) as "#Hcommon_init".
  { iPkgInit. }
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  wp_apply (wp_State__ReplicaSetGet with "[$Hown_rs_meta_frag $Hown_rs_spec_frag]").
  { iFrame "#".
    iPureIntro.
    rewrite /ReplicaSetV.key /ReplicaSetV.meta_key Hnamespace_eq Hname_eq.
    done. }
  iIntros (rs_l rs_get) "Hget". iNamedPrefix "Hget" "Hget_".
  iRename "Hget_Hdeepown_l" into "Hdeepown_l_rs".
  iRename "Hget_Hown_meta_frag" into "Hown_rs_meta_frag".
  iRename "Hget_Hown_spec_frag" into "Hown_rs_spec_frag".
  assert (ReplicaSetSpecV.valid rs_get.(ReplicaSetV.Spec')) as Hrs_get_spec_valid.
  { destruct Hget_Hvalid' as (_ & _ & _ & Hrs_get_spec_valid & _).
    exact Hrs_get_spec_valid. }
  assert (ReplicaSetSpecV.valid rs.(ReplicaSetV.Spec')) as Hrs_spec_valid.
  { rewrite Hget_Hspec_eq. exact Hrs_get_spec_valid. }
  wp_auto.
  wp_apply (wp_IsNotFound interface.nil with "[]").
  replace (bool_decide (not_found_error interface.nil)) with false by
    (symmetry; apply bool_decide_false; exact not_found_error_nil).
  wp_auto.
  iPoseProof (ReplicaSetV.deepown_l_split with "Hdeepown_l_rs") as
    "(%Hrs_l_not_null & Hdeepown_t_l_rs & Hdeepown_m_l_rs & Hdeepown_s_l_rs & Hdeepown_st_l_rs)".
  iPoseProof (kview.own_meta_valid with "Hown_rs_meta_frag") as "%Hrs_meta_frag_valid".
  destruct Hrs_meta_frag_valid as (_ & _ & _ & Hrs_meta_valid & Hdeletion_timestamp_eq).
  assert (ObjectMetaV.valid ReplicaSetV.kind rs_get.(ReplicaSetV.ObjectMeta')) as Hrs_get_meta_valid.
  { eapply ObjectMetaV.equiv_except_resource_version_valid.
    - apply ObjectMetaV.equiv_except_resource_version_sym. exact Hget_Hmeta_eq.
    - exact Hrs_meta_valid. }
  destruct Hget_Hvalid' as [Hrs_valid_typemeta _].
  destruct Hrs_valid_typemeta as (_ & Hrs_kind_valid & _).
  pose proof (valid_kind_slash_free _ Hrs_kind_valid) as Hrs_kind_slash_free.
  pose proof (ObjectMetaV.valid_namespace_of_valid _ Hrs_get_meta_valid) as Hrs_namespace_valid.
  pose proof (ObjectMetaV.valid_name_of_valid _ Hrs_get_meta_valid) as Hrs_name_valid.
  pose proof (ObjectMetaV.valid_uid_of_valid _ Hrs_get_meta_valid) as Hrs_uid_valid.
  pose proof (valid_namespace_slash_free _ Hrs_namespace_valid) as Hrs_namespace_slash_free.
  pose proof (valid_name_slash_free _ Hrs_name_valid) as Hrs_name_slash_free.
  pose proof (valid_uid_slash_free _ Hrs_uid_valid) as Hrs_uid_slash_free.
  assert (list_to_set (C:=gset KKey.t) (PodV.key <$> pods) =
      filter (λ key, key.(KKey.Kind') = "Pod"%go)
        (list_to_set (C:=gset KKey.t) (PodV.key <$> pods))) as Hdom_eq.
  { apply set_eq. intros key.
    rewrite elem_of_filter.
    split.
    - intros Hkey_in. split; [|done].
      apply elem_of_list_to_set in Hkey_in.
      apply list_elem_of_fmap_1 in Hkey_in as (pod & Hkey_eq & _).
      subst key.
      rewrite /PodV.key /PodV.meta_key /PodV.kind //.
    - intros [_ Hkey_in]. done. }
  assert (ReplicaSetV.key rs = ReplicaSetV.key rs_get) as Hrs_key_eq.
  { exact Hget_Hkey_eq. }
  assert (rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') =
      rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) as Hrs_uid_eq.
  { symmetry. apply ObjectMetaV.equiv_except_resource_version_uid. exact Hget_Hmeta_eq. }
  iEval (rewrite Hrs_key_eq Hrs_uid_eq) in "Hown_children_frag".
  iEval (rewrite Hrs_key_eq Hrs_uid_eq) in "Hown_terminating_children_frag".
  wp_apply (common.wp_FilterPodsByOwner_uniform_combined with
    "[$Hdeepown_m_l_rs $Hown_pod_meta_frags $Hown_children_frag
      $Hown_terminating_children_frag]").
  { iFrame "#".
    iPureIntro. split_and!; try done. }
  iIntros (all_sl all_ptrs all_pods dq')
    "(Hall_sl & Hall_deepown_pods & %Hall_living_meta_perm & %Hall_valid & %Hall_nodup &
      Hdeepown_m_l_rs & Hall_deletion_observed_frags & Hactive_meta_frags &
      Hown_children_frag & Hown_terminating_children_frag)".
  wp_auto.
  wp_apply (common.wp_FilterActivePods with "[$Hall_sl $Hall_deepown_pods]").
  iIntros (active_sl active_ptrs) "(Hactive_sl & Hactive_deepown_pods)".
  wp_auto.
  assert (PodV.key <$> filter is_pod_alive all_pods ≡ₚ PodV.key <$> pods) as Hactive_key_perm.
  { apply pod_key_meta_perm. exact Hall_living_meta_perm. }
  iAssert (([∗ list] pod ∈ filter is_pod_alive all_pods,
      own_unreserved_key_frag γ (PodV.key pod)))%I
    with "[Hown_pod_unreserved_key_frags]" as "#Hall_unreserved_key_frags".
  { rewrite (own_unreserved_key_frag_list_as_keys γ (filter is_pod_alive all_pods)).
    rewrite (big_sepL_permutation (own_unreserved_key_frag γ)
      (PodV.key <$> filter is_pod_alive all_pods) (PodV.key <$> pods) Hactive_key_perm).
    iEval (rewrite (own_unreserved_key_frag_list_as_keys γ pods))
      in "Hown_pod_unreserved_key_frags".
    iExact "Hown_pod_unreserved_key_frags". }
  assert (list_to_set (C:=gset KKey.t) (PodV.key <$> filter is_pod_alive all_pods) =
      list_to_set (C:=gset KKey.t) (PodV.key <$> pods)) as Hchildren_keys_eq.
  { rewrite Hactive_key_perm. done. }
  iAssert (own_children_frag γ (ReplicaSetV.key rs_get)
      rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (list_to_set (C:=gset KKey.t) (PodV.key <$> (filter is_pod_alive all_pods ++ []))))%I
    with "[Hown_children_frag]" as "Hown_children_frag".
  { rewrite app_nil_r Hchildren_keys_eq.
    iExact "Hown_children_frag". }
  iDestruct "Hdeepown_m_l_rs" as (rs_meta_c) "[Hrs_meta_l Hdeepown_m_rs]".
  iNamedPrefix "Hdeepown_m_rs" "Hrs_meta_".
  assert (rs_meta_c.(v1.ObjectMeta.DeletionTimestamp') = null) as Hrs_deletion_timestamp_null.
  { apply Hrs_meta_Hdeepown_deletiontimestamp_none.
    rewrite (ObjectMetaV.equiv_except_resource_version_deletion_timestamp _ _ Hget_Hmeta_eq).
    exact Hdeletion_timestamp_eq. }
  assert (rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None)
    as Hdeletion_timestamp_eq_get.
  { rewrite (ObjectMetaV.equiv_except_resource_version_deletion_timestamp _ _ Hget_Hmeta_eq).
    exact Hdeletion_timestamp_eq. }
  wp_auto.
  rewrite Hrs_deletion_timestamp_null.
  wp_auto.
  iEval (rewrite Hdeletion_timestamp_eq_get) in "Hrs_meta_Hdeepown_deletiontimestamp_some".
  iAssert (ObjectMetaV.deepown rs_meta_c rs_get.(ReplicaSetV.ObjectMeta') 1)
    with "[Hrs_meta_Hdeepown_creationtimestamp
      Hrs_meta_Hdeepown_deletiongraceperiodseconds_some
      Hrs_meta_Hdeepown_labels_some Hrs_meta_Hdeepown_annotations_some
      Hrs_meta_Hdeepown_ownerreferences_some Hrs_meta_Hdeepown_finalizers_some
      Hrs_meta_Hdeepown_managedfields_some]" as "Hdeepown_m_rs".
  { rewrite /ObjectMetaV.deepown Hdeletion_timestamp_eq_get.
    iFrame "%". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (ReplicaSetV.objectmeta_ptr rs_l) rs_get.(ReplicaSetV.ObjectMeta') 1)
    with "[Hrs_meta_l Hdeepown_m_rs]" as "Hdeepown_m_l_rs".
  { iExists rs_meta_c. iFrame. }
  iPoseProof (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_not_null with
    "[$Hdeepown_t_l_rs $Hdeepown_m_l_rs $Hdeepown_s_l_rs $Hdeepown_st_l_rs]") as
    "Hdeepown_l_rs".
  pose proof (ReplicaSetSpecV.valid_replicas _ Hrs_spec_valid) as (n & Hreplicas_eq & _).
  assert (rs_get.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n) as Hreplicas_eq_get.
  { rewrite <-Hget_Hspec_eq. exact Hreplicas_eq. }
  assert (length rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58) as Hrs_get_name_short.
  { rewrite (ObjectMetaV.equiv_except_resource_version_name _ _ Hget_Hmeta_eq).
    exact Hrs_name_short. }
  assert (valid_finalizers
      rs_get.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers'))
    as Hrs_get_template_finalizers_valid.
  { rewrite <-Hget_Hspec_eq. exact Hrs_template_finalizers_valid. }
  assert (NoDup (PodV.key <$> filter is_pod_alive all_pods)) as Hactive_nodup.
  { eapply sublist_NoDup; first exact Hall_nodup.
    apply fmap_sublist, sublist_filter. }
  wp_apply (wp_manageReplicas γ l active_sl rs_l active_ptrs
    (filter is_pod_alive all_pods) []
    rs_get n phase dq' 1 with
    "[$Hactive_sl $Hactive_deepown_pods $Hdeepown_l_rs $Hactive_meta_frags $Hown_children_frag
      $Hown_terminating_children_frag]").
  { iFrame "#".
    iPureIntro. split_and!; try done.
    - intros pod Hpod.
      apply list_elem_of_filter in Hpod as [Halive _].
      exact Halive.
    - rewrite app_nil_r. exact Hactive_nodup. }
  iIntros (pods_managed) "(%Hmanaged_len & Hphase & Hdeepown_l_rs &
    Hmanaged_meta_frags & #Hmanaged_unreserved_key_frags &
    Hown_children_frag)".
  iDestruct "Hphase" as (phase') "Hown_terminating_children_frag".
  wp_auto.
  iEval (rewrite app_nil_r) in "Hown_children_frag".
  iEval (rewrite -Hrs_key_eq -Hrs_uid_eq) in "Hown_children_frag".
  iEval (rewrite -Hrs_key_eq -Hrs_uid_eq) in "Hown_terminating_children_frag".
  iPoseProof (kview.own_meta_list_no_dup PodV.key PodV.ObjectMeta'
    with "Hmanaged_meta_frags") as "%Hpods'_nodup".
  iAssert (∃ phase, own_terminating_children_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') phase)%I
    with "[Hown_terminating_children_frag]" as "Hown_terminating_children_frag".
  { iExists phase'. iFrame. }
  iApply ("HΦ" $! pods_managed).
  rewrite /owned_resources /=.
  iFrame "Hown_rs_meta_frag Hown_rs_spec_frag Hmanaged_meta_frags
    Hmanaged_unreserved_key_frags Hown_children_frag Hown_terminating_children_frag".
  iPureIntro. split; first exact Hpods'_nodup.
  assert (match_distance rs pods_managed = 0%nat) as Hdistance_zero.
  { unfold match_distance.
    rewrite Hreplicas_eq /= Hmanaged_len. lia. }
  lia.
Qed.

End proof.
