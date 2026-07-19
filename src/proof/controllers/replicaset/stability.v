
From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get index create delete.
From New.proof Require Export util.
From New.proof Require Export external_wp.
From New.proof.controllers Require Export common.
From New.proof.controllers.replicaset Require Export progress.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{hG: !heapGS Σ}.
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

Lemma active_pod_count_erased_meta_perm pods1 pods2 :
  ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods1) ≡ₚ
    ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods2) →
  length (filter is_pod_alive pods1) = length (filter is_pod_alive pods2).
Proof.
  intros Hperm.
  assert (Hcount : ∀ pods,
    length (filter is_pod_alive pods) =
    length (filter (λ meta : ObjectMetaV.t, meta.(ObjectMetaV.DeletionTimestamp') = None)
      (ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods)))).
  { intros pods. induction pods as [|pod pods IH]; simpl; first done.
    destruct (decide (is_pod_alive pod)) as [Halive|Hnot_alive].
    - destruct (decide ((ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta')).(ObjectMetaV.DeletionTimestamp') = None))
        as [Herased_alive|Hnot_erased_alive].
      + rewrite (filter_cons_True is_pod_alive pod pods Halive).
        rewrite (filter_cons_True
          (λ meta : ObjectMetaV.t, meta.(ObjectMetaV.DeletionTimestamp') = None)
          (ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta'))
          (ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods))
          Herased_alive).
        simpl. f_equal. exact IH.
      + exfalso. apply Hnot_erased_alive.
        unfold is_pod_alive, ObjectMetaV.without_resource_version in *.
        destruct pod as [? [] ? ?]. exact Halive.
    - destruct (decide ((ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta')).(ObjectMetaV.DeletionTimestamp') = None))
        as [Herased_alive|Hnot_erased_alive].
      + exfalso. apply Hnot_alive.
        unfold is_pod_alive, ObjectMetaV.without_resource_version in *.
        destruct pod as [? [] ? ?]. exact Herased_alive.
      + rewrite (filter_cons_False is_pod_alive pod pods Hnot_alive).
        rewrite (filter_cons_False
          (λ meta : ObjectMetaV.t, meta.(ObjectMetaV.DeletionTimestamp') = None)
          (ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta'))
          (ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods))
          Hnot_erased_alive).
        exact IH. }
  rewrite !Hcount.
  apply Permutation_length.
  apply perm_filter.
  exact Hperm.
Qed.

Lemma wp_manageReplicas_stability sl rs_l ptrs active_pods rs n dq1 dq2 :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hdeepown_l_active_pods" ∷ ([∗ list] ptr;pod ∈ ptrs;active_pods, PodV.deepown_l ptr pod dq1) ∗
      "Hdeepown_l_rs" ∷ ReplicaSetV.deepown_l rs_l rs dq2 ∗
      "%Hreplicas_eq" ∷ ⌜ rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n ⌝ ∗
      "%Hn_nonneg" ∷ ⌜ 0 ≤ sint.Z n ⌝ ∗
      "%Hlen_active" ∷ ⌜ length active_pods = sint.nat n ⌝
  }}}
    @! replicaset.manageReplicas #sl #rs_l
  {{{ RET #interface.nil;
      sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;active_pods, PodV.deepown_l ptr pod dq1) ∗
      ReplicaSetV.deepown_l rs_l rs dq2
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  iPoseProof (ReplicaSetV.deepown_l_split with "Hdeepown_l_rs") as
    "(%Hrs_l_not_null & Hdeepown_t_l_rs & Hdeepown_m_l_rs & Hdeepown_s_l_rs & Hdeepown_st_l_rs)".
  iDestruct "Hdeepown_s_l_rs" as "(%rs_spec_c & Hrs_spec_l & Hdeepown_rs_spec)".
  iNamedPrefix "Hdeepown_rs_spec" "Hrs_".
  iAssert ((rs_spec_c.(v1.ReplicaSetSpec.Replicas') ↦{dq2} n)%I) with "[Hrs_Hdeepown_replicas_some]"
    as "Hrs_Hdeepown_replicas".
  { rewrite Hreplicas_eq. iDestruct "Hrs_Hdeepown_replicas_some" as "(%replicas & Hreplicas & ->)".
    done. }
  wp_auto.
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hdeepown_l_active_pods") as %Hlen.
  wp_if_destruct.
  - exfalso. rewrite -Hlen Hsl_len1 in Hlen_active. word.
  - wp_if_destruct.
    + exfalso. rewrite -Hlen Hsl_len1 in Hlen_active. word.
    + iApply "HΦ". iFrame.
      iApply (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_not_null). iFrame.
      iSplitR. 1: done. iSplitL. 2: done.
      rewrite Hreplicas_eq. iExists n. iSplitL. all: done.
Qed.

Lemma wp_syncReplicaSet_stability γ l (gv: schema.GroupVersion.t) namespace name rs dq pods :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr apps_v1.SchemeGroupVersion) ↦□ gv ∗
      "Hown_rs_meta_frag" ∷ own_meta_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
        rs.(ReplicaSetV.ObjectMeta') ∗
      "Hown_rs_spec_frag" ∷ own_spec_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
        (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      "Hown_pod_meta_frags" ∷ ([∗ list] k ↦ pod ∈ pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq pod.(PodV.ObjectMeta')) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
        (list_to_set (PodV.key <$> pods)) ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hdeletion_timestamp_eq" ∷ ⌜ rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "%Hrs_name_short" ∷ ⌜ length rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ⌝ ∗
      "%Hmatch" ∷ ⌜ current_state_matches rs pods ⌝ ∗
      "%Hpods_no_dup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝
  }}}
    @! replicaset.syncReplicaSet #namespace #name
  {{{ (err : interface.t), RET #err;
      own_meta_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs.(ReplicaSetV.ObjectMeta') ∗
      own_spec_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq pod.(PodV.ObjectMeta')) ∗
      own_children_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (list_to_set (PodV.key <$> pods))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
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
  wp_apply (wp_IsNotFound_nil with "[]").
  { done. }
  wp_pures.
  iPoseProof (ReplicaSetV.deepown_l_split with "Hdeepown_l_rs") as
    "(%Hrs_l_not_null & Hdeepown_t_l_rs & Hdeepown_m_l_rs & Hdeepown_s_l_rs & Hdeepown_st_l_rs)".
  iPoseProof (kview.own_meta_valid with "Hown_rs_meta_frag") as "%Hrs_meta_frag_valid".
  destruct Hrs_meta_frag_valid as (_ & _ & _ & Hrs_meta_valid).
  assert (ObjectMetaV.valid ReplicaSetV.kind rs_get.(ReplicaSetV.ObjectMeta')) as Hrs_get_meta_valid.
  { eapply ObjectMetaV.equiv_except_resource_version_valid.
    - apply ObjectMetaV.equiv_except_resource_version_sym. exact Hget_Hmeta_eq.
    - exact Hrs_meta_valid. }
  destruct Hget_Hvalid' as [Hrs_valid_typemeta _].
  destruct Hrs_valid_typemeta as [_ Hrs_kind_valid].
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
  wp_apply (common.wp_FilterPodsByOwner with
    "[$Hdeepown_m_l_rs $Hown_pod_meta_frags $Hown_children_frag]").
  { iFrame "#".
    iPureIntro. split_and!; try done. }
  iIntros (all_sl all_ptrs all_pods dq') "(Hall_sl & Hall_deepown_pods & %Hall_meta_perm & %Hall_valid & %Hall_nodup &
    Hdeepown_m_l_rs & Hall_meta_frags & Hown_children_frag)".
  wp_auto.
  wp_apply (common.wp_FilterActivePods with "[$Hall_sl $Hall_deepown_pods]").
  iIntros (active_sl active_ptrs) "(Hactive_sl & Hactive_deepown_pods)".
  wp_auto.
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
  pose proof (ReplicaSetSpecV.valid_replicas _ Hrs_spec_valid) as
    (n & Hreplicas_eq & Hn_nonneg).
  assert (rs_get.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n) as Hreplicas_eq_get.
  { rewrite <-Hget_Hspec_eq. exact Hreplicas_eq. }
  assert (length (filter is_pod_alive all_pods) = sint.nat n) as Hactive_len.
  { unfold current_state_matches in Hmatch.
    rewrite Hreplicas_eq in Hmatch. simpl in Hmatch.
    rewrite (active_pod_count_erased_meta_perm all_pods pods Hall_meta_perm).
    exact Hmatch. }
  wp_apply (wp_manageReplicas_stability active_sl rs_l active_ptrs
    (filter is_pod_alive all_pods) rs_get n dq' 1 with
    "[$Hactive_sl $Hactive_deepown_pods $Hdeepown_l_rs]").
  { iFrame "#".
    iPureIntro. split_and!; try done. }
  iIntros "(Hactive_sl & Hactive_deepown_pods & Hdeepown_l_rs)".
  wp_auto.
  iAssert (([∗ list] pod ∈ pods,
      own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq
        pod.(PodV.ObjectMeta')))%I
    with "[Hall_meta_frags]" as "Hown_pod_meta_frags".
  { iAssert (([∗ list] meta ∈
        ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> all_pods),
        own_meta_frag γ (PodV.meta_key meta) meta.(ObjectMetaV.UID') dq meta))%I
      with "[Hall_meta_frags]" as "Herased_meta_frags".
    { rewrite -own_meta_frag_list_as_erased_metas. iExact "Hall_meta_frags". }
    iAssert (([∗ list] meta ∈
        ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods),
        own_meta_frag γ (PodV.meta_key meta) meta.(ObjectMetaV.UID') dq meta))%I
      with "[Herased_meta_frags]" as "Herased_meta_frags".
    { rewrite -Hall_meta_perm. iExact "Herased_meta_frags". }
    rewrite own_meta_frag_list_as_erased_metas.
    iExact "Herased_meta_frags". }
  assert (owner_ref_key ReplicaSetV.kind rs_get.(ReplicaSetV.ObjectMeta') =
      ReplicaSetV.key rs_get) as Howner_key_eq.
  { rewrite /owner_ref_key /ReplicaSetV.key /ReplicaSetV.meta_key /ReplicaSetV.kind. done. }
  iEval (rewrite Howner_key_eq -Hrs_key_eq -Hrs_uid_eq) in "Hown_children_frag".
  iApply ("HΦ" $! interface.nil).
  iFrame "Hown_rs_meta_frag Hown_rs_spec_frag Hown_pod_meta_frags Hown_children_frag".
Qed.

End proof.
