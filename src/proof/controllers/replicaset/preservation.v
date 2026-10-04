From New.proof.controllers.replicaset Require Export progress.
From New.proof.controllers.replicaset Require Import update_replicaset_status.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.replicaset.replicaset.import_controller_Assumption.
#[local] Instance clientset_sem : kubernetes.Assumptions :=
  code.controllers.replicaset.replicaset.import_kubernetes_Assumption.
#[local] Instance client_core_v1_sem : client_core_v1.Assumptions :=
  kubernetes.import_core_v1_Assumption.
#[local] Instance client_apps_v1_sem : client_apps_v1.Assumptions :=
  kubernetes.import_apps_v1_Assumption.
#[local] Instance client_gentype_sem : client_gentype.Assumptions :=
  client_core_v1.import_gentype_Assumption.
#[local] Instance app_listers_sem : app_listers.Assumptions :=
  code.controllers.replicaset.replicaset.import_listers_apps_v1_Assumption.
#[local] Instance generic_listers_sem : generic_listers.Assumptions :=
  app_listers.import_listers_Assumption.
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

Context `{!KObjectV.ObjectInterfaceAssumptions}.

Lemma wp_syncReplicaSet_preservation γ l (ctx : context.Context.t) (kube_client : loc) (burst : w64)
    (rsc_clock : interface.t) (controller_features : replicaset.ReplicaSetControllerFeatures.t) namespace name rs
    dq pods :
  ⊢ preservation_spec γ l ctx kube_client burst rsc_clock controller_features namespace name rs dq pods.
Proof.
  unfold preservation_spec.
  wp_start as "H". iNamed "H". iNamed "Hresources".
  iEval (simpl) in "Hown_rs_meta_frag Hown_rs_spec_frag Hown_rs_status_frag Hown_pod_meta_frags
    Hown_children_frag Hown_terminating_children_frag".
  iDestruct "Hown_terminating_children_frag" as (has_terminating_children) "Hown_terminating_children_frag".
  unfold input_requirement in Hinput_requirement.
  destruct Hinput_requirement as (Hrs_name_short & Hrs_template_finalizers_valid & Hlabels_bound & Hgeneration_nonneg).
  iAssert (is_pkg_init common) as "#Hcommon_init".
  { iPkgInit. }
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  wp_auto.
  wp_bind (null @! (go.PointerType app_listers.replicaSetLister) @! "ReplicaSets" #namespace)%E.
  wp_method_call. rewrite /trusted_app_listers.replicaSetLister__ReplicaSetsⁱᵐᵖˡ. wp_call. try wp_auto.
  wp_method_call. rewrite /trusted_generic_listers.ResourceIndexer__Getⁱᵐᵖˡ decide_True; try reflexivity.
  rewrite /trusted_generic_listers.resourceIndexerGet. wp_pures.
  wp_auto.
  wp_apply (wp_State__ReplicaSetGet_status with "[$Hown_rs_meta_frag $Hown_rs_spec_frag $Hown_rs_status_frag]").
  { iFrame "#".
    iPureIntro.
    rewrite /ReplicaSetV.key /ReplicaSetV.meta_key Hnamespace_eq Hname_eq.
    done. }
  iIntros (rs_l rs_get) "Hget". iNamedPrefix "Hget" "Hget_".
  iRename "Hget_Hdeepown_l" into "Hdeepown_l_rs".
  iRename "Hget_Hown_meta_frag" into "Hown_rs_meta_frag".
  iRename "Hget_Hown_spec_frag" into "Hown_rs_spec_frag".
  iRename "Hget_Hown_status_frag" into "Hown_rs_status_frag".
  pose proof Hget_Hvalid' as Hrs_get_valid.
  assert (ReplicaSetSpecV.valid rs_get.(ReplicaSetV.Spec')) as Hrs_get_spec_valid.
  { destruct Hget_Hvalid' as (_ & _ & _ & Hrs_get_spec_valid & _).
    exact Hrs_get_spec_valid. }
  assert (ReplicaSetSpecV.valid rs.(ReplicaSetV.Spec')) as Hrs_spec_valid.
  { rewrite Hget_Hspec_eq. exact Hrs_get_spec_valid. }
  wp_auto.
  rewrite decide_True; try reflexivity.
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
  { destruct Hget_Hvalid' as (_ & _ & Hvalid_meta & _). exact Hvalid_meta. }
  pose proof Hget_Hmeta_eq as Hget_Hmeta_fields.
  rewrite /ObjectMetaV.equiv_except_resource_version
    /ObjectMetaV.without_resource_version in Hget_Hmeta_fields.
  pose proof (f_equal ObjectMetaV.Name' Hget_Hmeta_fields) as Hget_Hname_eq.
  pose proof (f_equal ObjectMetaV.UID' Hget_Hmeta_fields) as Hget_Huid_eq.
  pose proof (f_equal ObjectMetaV.DeletionTimestamp' Hget_Hmeta_fields)
    as Hget_Hdeletion_timestamp_eq.
  simpl in Hget_Hname_eq, Hget_Huid_eq, Hget_Hdeletion_timestamp_eq.
  destruct Hget_Hvalid' as [Hrs_valid_typemeta _].
  destruct Hrs_valid_typemeta as (_ & Hrs_kind_valid & _).
  pose proof (valid_kind_slash_free _ Hrs_kind_valid) as Hrs_kind_slash_free.
  assert (valid_namespace rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace'))
    as Hrs_namespace_valid by (unfold ObjectMetaV.valid in Hrs_get_meta_valid; tauto).
  assert (valid_name ReplicaSetV.kind rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name'))
    as Hrs_name_valid by (unfold ObjectMetaV.valid in Hrs_get_meta_valid; tauto).
  assert (valid_uid rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID'))
    as Hrs_uid_valid by (unfold ObjectMetaV.valid in Hrs_get_meta_valid; tauto).
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
  { symmetry. exact Hget_Huid_eq. }
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
  (* The pods are only read: share them between the two filters, management
     and the status calculation. *)
  iMod (big_sepL2_persist PodV.deepown_l with "Hall_deepown_pods") as "#Hall_deepown_pods".
  { intros. apply PodV.deepown_l_persist. }
  wp_apply (common.wp_FilterActivePods with "[$Hall_sl $Hall_deepown_pods]").
  iIntros (active_sl active_ptrs) "(Hactive_sl & #Hactive_deepown_pods & Hall_sl)".
  wp_auto.
  (* Terminating pods are collected only when the feature is enabled; either way
     only the length of the result matters. *)
  iAssert (is_pkg_init controller) as "#Hcontroller_init".
  { iPkgInit. }
  wp_bind (if: _ then _ else do: #())%E.
  iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗
      ∃ (term_sl : slice.t) (term_ptrs : list loc),
        "terminatingPods" ∷ terminatingPods_ptr ↦ term_sl ∗
        "Hterm_sl" ∷ term_sl ↦* term_ptrs ∗
        "%Hterm_len" ∷ ⌜ length term_ptrs ≤ length all_ptrs ⌝ ∗
        "Hall_sl" ∷ all_sl ↦* all_ptrs ∗
        "allRSPods" ∷ allRSPods_ptr ↦ all_sl ∗
        "controllerFeatures" ∷ controllerFeatures_ptr ↦ controller_features)%I
    with "[terminatingPods Hall_sl allRSPods controllerFeatures]").
  { wp_bind (MethodResolve featuregate.FeatureGate "Enabled"%go
      (![featuregate.FeatureGate] #(global_addr utilfeature.DefaultFeatureGate)) _)%E.
    iApply wp_DefaultFeatureGate_Enabled; first done.
    iNext. iIntros (gate) "_".
    destruct gate; wp_auto;
      [destruct (replicaset.ReplicaSetControllerFeatures.EnableStatusTerminatingReplicas'
        controller_features); wp_auto|].
    - wp_apply (wp_FilterTerminatingPods with "[$Hall_sl $Hall_deepown_pods]").
      iIntros (term_sl term_ptrs) "(Hterm_sl & %Hterm_len & Hall_sl & _)". wp_auto.
      iSplit; first done. iExists term_sl, term_ptrs. iFrame. done.
    - iSplit; first done. iExists slice.nil, []. iFrame.
      iSplitR; first iApply own_slice_nil. iPureIntro. simpl. lia.
    - iSplit; first done. iExists slice.nil, []. iFrame.
      iSplitR; first iApply own_slice_nil. iPureIntro. simpl. lia. }
  iIntros (v) "(-> & H)". iNamed "H".
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
    rewrite Hget_Hdeletion_timestamp_eq.
    exact Hdeletion_timestamp_eq. }
  assert (rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None)
    as Hdeletion_timestamp_eq_get.
  { rewrite Hget_Hdeletion_timestamp_eq.
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
  { rewrite Hget_Hname_eq.
    exact Hrs_name_short. }
  assert (valid_finalizers
      rs_get.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers'))
    as Hrs_get_template_finalizers_valid.
  { rewrite <-Hget_Hspec_eq. exact Hrs_template_finalizers_valid. }
  assert (NoDup (PodV.key <$> filter is_pod_alive all_pods)) as Hactive_nodup.
  { eapply sublist_NoDup; first exact Hall_nodup.
    apply fmap_sublist, sublist_filter. }
  (* manageReplicas only reads the ReplicaSet and returns it. *)
  iMod (ReplicaSetV.deepown_l_persist with "Hdeepown_l_rs") as "Hdeepown_l_rs".
  wp_apply (wp_manageReplicas γ l ctx kube_client burst active_sl rs_l active_ptrs
    (filter is_pod_alive all_pods) []
    rs_get n has_terminating_children with
    "[$Hactive_sl $Hactive_deepown_pods $Hdeepown_l_rs $Hactive_meta_frags $Hown_children_frag
      $Hown_terminating_children_frag]").
  { iFrame "#".
    iPureIntro. split_and!; try done.
    all: try (intros pod Hpod; apply list_elem_of_filter in Hpod as [Halive _]; exact Halive).
    all: try lia.
    rewrite app_nil_r; exact Hactive_nodup. }
  iIntros (pods_managed) "(%Hmanaged_len & %Hmanaged_alive & Hhas_terminating_children &
    Hmanaged_meta_frags & #Hmanaged_unreserved_key_frags &
    Hown_children_frag & (%active_ptrs' & %active_pods' & Hactive_sl & #Hactive_deepown_pods' &
      %Hactive_perm) & Hdeepown_l_rs)".
  iDestruct "Hhas_terminating_children" as (has_terminating_children') "Hown_terminating_children_frag".
  wp_auto.
  iEval (rewrite app_nil_r) in "Hown_children_frag".
  iEval (rewrite -Hrs_key_eq -Hrs_uid_eq) in "Hown_children_frag".
  iEval (rewrite -Hrs_key_eq -Hrs_uid_eq) in "Hown_terminating_children_frag".
  iPoseProof (kview.own_meta_list_no_dup PodV.key PodV.ObjectMeta'
    with "Hmanaged_meta_frags") as "%Hpods'_nodup".
  iAssert (∃ has_terminating_children, own_terminating_children_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') has_terminating_children)%I
    with "[Hown_terminating_children_frag]" as "Hown_terminating_children_frag".
  { iExists has_terminating_children'. iFrame. }
  (* rs = rs.DeepCopy() *)
  iDestruct "Hdeepown_l_rs" as (rs_phy) "[Hrs_l Hrs]".
  wp_apply (wp_ReplicaSet__DeepCopy with "[$Hrs_l $Hrs]").
  iIntros (copy_l) "(Hcopy & _ & _)".
  wp_pures. wp_store. wp_pures. wp_alloc now_ptr as "now". wp_pures. wp_load.
  (* now := rscClock.Now(), before the interface call is resolved. *)
  wp_bind (MethodResolve clock.PassiveClock "Now" _ _)%E.
  iApply ("Hclock" with "[//]"). iNext. iIntros (now) "_". wp_auto.
  iDestruct "Hcopy" as (copy_phy) "[Hcopy_l Hcopy]".
  wp_apply (wp_calculateStatus_no_manage_error with
    "[$Hcopy_l $Hcopy $Hactive_sl $Hactive_deepown_pods' $Hterm_sl]").
  { iPureIntro. split; first exact Hrs_get_valid.
    rewrite -Hget_Hspec_eq. exact Hlabels_bound. }
  iIntros (status_c status) "(Hcopy_l & Hcopy & #Hstatus & Hactive_sl & _ & Hterm_sl &
    %Hstatus_replicas & %Hstatus_og & %Hstatus_valid)".
  wp_auto.
  (* updateReplicaSetStatus(kubeClient.AppsV1().ReplicaSets(rs.Namespace), rs, newStatus) *)
  iAssert (⌜ copy_phy.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Namespace') =
    rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝)%I as %Hcopy_ns.
  { iNamed "Hcopy". iNamed "Hdeepown_objectmeta". done. }
  rewrite Hcopy_ns.
  wp_bind (MethodResolve _ "ReplicaSets"%go _ _)%E.
  (* Instantiated explicitly: applying the lemma directly fails to unify. *)
  iPoseProof (wp_AppsV1_ReplicaSets kube_client
    rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace')) as "Hrs_client".
  iApply ("Hrs_client" with "[//]"). iNext. iIntros (c) "#Hclient". wp_auto.
  iEval (rewrite Hrs_key_eq Hrs_uid_eq) in "Hown_rs_meta_frag Hown_rs_spec_frag Hown_rs_status_frag".
  iPoseProof (meta_frag_equiv Hget_Hmeta_eq with "Hown_rs_meta_frag") as "Hown_rs_meta_frag".
  iEval (rewrite Hget_Hspec_eq) in "Hown_rs_spec_frag".
  iEval (rewrite Hget_Hstatus_eq) in "Hown_rs_status_frag".
  wp_apply (wp_updateReplicaSetStatus γ l c copy_l copy_phy rs_get status_c status dq
    with "[$Hcopy_l $Hcopy $Hown_rs_meta_frag $Hown_rs_spec_frag $Hown_rs_status_frag]").
  { iFrame "#". done. }
  iIntros (result_l err rs') "(%Hchanged & Hown_rs_meta_frag & Hown_rs_spec_frag & Hown_rs_status_frag & _)".
  destruct Hchanged as (Hmeta_changed & Hspec_changed).
  wp_auto.  (* The ReplicaSet after the sync: the stored one, which differs from [rs]
     only in status and resource version. Its TypeMeta is not tracked by any
     fragment, so take [rs]'s. *)
  set rs'' := rs' <| ReplicaSetV.TypeMeta' := rs.(ReplicaSetV.TypeMeta') |>.
  destruct (meta_equiv_key_uid _ _ Hmeta_changed) as (Hkey' & Huid' & _ & _).
  assert (ReplicaSetV.key rs'' = ReplicaSetV.key rs_get) as Hkey''.
  { rewrite /ReplicaSetV.key /=. exact Hkey'. }
  assert (rs''.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') =
    rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) as Huid'' by exact Huid'.
  assert (ReplicaSetV.status_only_changed rs rs'') as Hstatus_only.
  { rewrite /ReplicaSetV.status_only_changed /=. split_and!; first done.
    - rewrite /ObjectMetaV.equiv_except_resource_version in Hmeta_changed Hget_Hmeta_eq |- *.
      congruence.
    - congruence. }
  iAssert (owned_resources γ rs'' pods_managed (mutating_fractions dq) false)%I
    with "[Hown_rs_meta_frag Hown_rs_spec_frag Hown_rs_status_frag Hmanaged_meta_frags
      Hown_children_frag Hown_terminating_children_frag]" as "Hresources".
  { rewrite /owned_resources /= Hkey'' Huid'' -Hrs_key_eq -Hrs_uid_eq.
    rewrite -Hspec_changed.
    iFrame "∗ #". iPureIntro. exact Hpods'_nodup. }
  assert (match_distance rs pods_managed ≤ match_distance rs pods) as Hdistance.
  {
  (* one sync moves the live count toward the desired count by at most [burst] *)
    assert (length (filter is_pod_alive (filter is_pod_alive all_pods)) = length (filter is_pod_alive pods))
      as Hliving_active_len.
    { apply active_pod_count_erased_meta_perm. exact Hall_living_meta_perm. }
    assert (length (filter is_pod_alive pods) = length (filter is_pod_alive all_pods)) as Hpods_active_len.
    { rewrite -Hliving_active_len. f_equal. apply filter_all.
      intros pod Hpod. apply list_elem_of_filter in Hpod as [Halive _]. exact Halive. }
    pose proof (capped_replica_count_distance (length (filter is_pod_alive all_pods)) (sint.nat n) (sint.nat burst))
      as Hcap.
    rewrite -Hmanaged_len in Hcap.
    rewrite !(match_distance_replica_distance _ _ n Hreplicas_eq).
    rewrite (filter_all is_pod_alive pods_managed Hmanaged_alive) Hpods_active_len.
    lia.
  }
  destruct err; wp_auto.
  - iApply ("HΦ" $! rs'' pods_managed with "[$Hresources //]").
  - iApply ("HΦ" $! rs'' pods_managed with "[$Hresources //]").
Qed.

End proof.
