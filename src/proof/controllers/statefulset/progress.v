From New.proof.controllers.statefulset Require Export reconcile_progress.
From New.proof.controllers.statefulset Require Import common.
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

Lemma wp_syncStatefulSet_progress γ l namespace name sts dq pods pvcs :
  ⊢ syncStatefulSet_progress_spec γ l namespace name sts dq pods pvcs.
Proof.
  unfold syncStatefulSet_progress_spec.
  wp_start as "H". iNamed "H". iNamed "Hresources".
  iEval (simpl) in "Hown_sts_meta_frag".
  iEval (simpl) in "Hown_sts_spec_frag".
  iEval (simpl) in "Hown_pod_frags".
  iEval (simpl) in "Hown_children_frag".
  iEval (simpl) in "Hown_terminating_children_frag".
  iEval (simpl) in "Hown_pvc_frags".
  iPoseProof (kview.own_meta_valid with "Hown_sts_meta_frag")
    as "%Hsts_meta_valid".
  destruct Hsts_meta_valid as (_ & _ & _ & _ & Hdeletion_timestamp_eq).
  iPoseProof (own_pod_frags_living with "Hown_pod_frags")
    as "%Hpods_living".
  assert (filter (pending_pod sts) pods = []) as Hpending_pods_empty.
  { apply filter_none. intros pod Hpod [Hnot_alive _].
    rewrite Forall_forall in Hpods_living. apply Hnot_alive, Hpods_living.
    by rewrite -list_elem_of_In. }
  wp_auto.
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
  destruct Hset_typemeta_valid as (_ & Hset_kind_valid & _).
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

  iEval (rewrite big_sepL_sep) in "Hown_pod_frags".
  iDestruct "Hown_pod_frags" as
    "[Hown_pod_meta_frags Hown_pod_spec_frags]".
  iPoseProof (kview.own_meta_list_no_dup PodV.key PodV.ObjectMeta'
    with "Hown_pod_meta_frags") as "%Hpods_nodup".
  iCombine "Hown_pod_meta_frags Hown_pod_spec_frags" as
    "Hown_pod_frags".
  iEval (rewrite -big_sepL_sep) in "Hown_pod_frags".
  assert (list_to_set (C:=gset KKey.t) (PodV.key <$> pods) =
      filter (λ key, key.(KKey.Kind') = "Pod"%go)
        (list_to_set (C:=gset KKey.t) (PodV.key <$> pods))) as Hdom_eq.
  { apply set_eq. intros key. rewrite elem_of_filter. split.
    - intros Hkey. split; last done.
      apply elem_of_list_to_set in Hkey.
      apply list_elem_of_fmap_1 in Hkey as (pod & -> & _).
      rewrite /PodV.key /PodV.meta_key /PodV.kind //.
    - intros [_ Hkey]. exact Hkey. }
  iEval (rewrite Hset_key Hset_uid) in
    "Hown_children_frag Hown_terminating_children_frag".

  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_meta &
      Hset_spec & Hset_status)".
  wp_apply (common.wp_FilterPodsByOwner_uniform_with_spec
    _ _ _ _ _ _ pods 1 1
    (list_to_set (PodV.key <$> pods))
    with "[$Hset_meta $Hown_pod_frags $Hown_children_frag
      $Hown_terminating_children_frag]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (all_sl all_ptrs all_pods pod_dq)
    "(Hall_sl & Hall_pods & %Hall_living_storage_perm &
      %Hall_quiescent_storage_perm & %Hall_valid & %Hall_parent_refs &
      %Hall_nodup & Hset_meta & #Hall_deletion_observed &
      Hall_frags & Hown_children_frag & Hown_terminating_children_frag)".
  pose proof (Hall_quiescent_storage_perm eq_refl) as Hall_storage_perm.
  assert (filter is_pod_alive all_pods = all_pods) as Hall_living.
  { assert (Forall is_pod_alive all_pods) as Hall.
    { apply (filter_length_eq_Forall is_pod_alive all_pods).
      pose proof (Permutation_length Hall_living_storage_perm) as Hliving_len.
      pose proof (Permutation_length Hall_storage_perm) as Hall_len.
      rewrite !map_length in Hliving_len, Hall_len. lia. }
    apply filter_all. intros pod Hpod. rewrite Forall_forall in Hall.
    apply Hall. by rewrite -list_elem_of_In. }
  iEval (rewrite Hall_living) in "Hall_frags".
  pose proof (pod_storage_view_perm_reservation_identities _ _ Hall_storage_perm)
    as Hall_reservation_identities.
  iAssert (own_occupied_pods γ all_pods) with "[Hoccupied_pods]" as "Hall_occupied".
  { rewrite !own_occupied_pods_as_identities.
    rewrite (big_sepL_permutation (λ identity, own_occupied_reserved_frag γ identity.1 identity.2)
      (pod_reservation_identity <$> all_pods)
      (pod_reservation_identity <$> pods) Hall_reservation_identities).
    iExact "Hoccupied_pods". }
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

  set Good := (λ pod : PodV.t,
    pod_has_int32_member_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
  set good_pods := filter Good all_pods.
  set bad_pods := filter (λ pod, ¬ Good pod) all_pods.
  iEval (rewrite big_sepL_sep) in "Hall_frags".
  iDestruct "Hall_frags" as "[Hall_meta_frags Hall_spec_frags]".
  iDestruct (big_sepL_filter_partition Good _ all_pods
    with "Hall_meta_frags") as "[Hgood_meta Hbad_meta]".
  iDestruct (big_sepL_filter_partition Good _ all_pods
    with "Hall_spec_frags") as "[Hgood_spec Hbad_spec]".
  iDestruct (big_sepL_filter_partition Good _ all_pods
    with "Hall_occupied") as "[Hgood_occupied Hbad_occupied]".
  iEval (fold good_pods) in "Hgood_meta Hgood_spec Hgood_occupied".
  iEval (fold bad_pods) in "Hbad_meta Hbad_spec".
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
  iCombine "Hgood_meta Hgood_spec" as "Hgood_frags".
  iEval (rewrite -big_sepL_sep) in "Hgood_frags".
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
  assert (Hpending_all_sts : filter (pending_pod sts) all_pods = []).
  { eapply pending_pods_empty_storage_view_perm.
    - exact (Permutation_sym Hall_storage_perm).
    - exact Hpending_pods_empty. }
  assert (Hpending_good : filter (pending_pod set) good_pods = []).
  { apply filter_none. intros pod Hpod Hpending_set.
    apply list_elem_of_filter in Hpod as [_ Hpod].
    pose proof (proj2
      (statefulset_storage_view_pending_pod sts set pod Hset_view)
      Hpending_set) as Hpending_sts.
    assert (pod ∈ filter (pending_pod sts) all_pods) as Hcontra.
    { apply list_elem_of_filter. split; done. }
    rewrite Hpending_all_sts in Hcontra. inversion Hcontra. }
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
  iEval (rewrite -Hmissing_pods) in "Hreserved_pods".
  assert (NoDup (missing_pvc_keys set pvcs)) as Hmissing_pvcs_nodup.
  { unfold missing_pvc_keys. apply list.NoDup_filter.
    unfold desired_pvc_keys. apply NoDup_elements. }
  iEval (rewrite /own_missing_pvc_reservations -Hmissing_pvcs
    (big_sepS_list_to_set _ _ Hmissing_pvcs_nodup)) in "Hreserved_pvcs".
  wp_auto.
  wp_apply (wp_reconcileReplicas_progress γ l set_l good_sl set
    good_ptrs good_pods pvcs 1 pod_dq Quiescent
    with "[$Hset $Hgood_sl $Hgood_pods $Hgood_frags
      $Hgood_occupied $Hown_pvc_frags $Hoccupied_pvcs $Hgood_children
      $Hown_terminating_children_frag $Hreserved_pods $Hreserved_pvcs]").
  { iFrame "#". iFrame "%". }
  iIntros (pods' pvcs' deletion) "Hreconcile".
  iNamedPrefix "Hreconcile" "Hreconcile_". wp_auto.

  assert (Hinitial_distance :
      match_distance set all_pods pvcs = match_distance sts pods pvcs).
  { rewrite (match_distance_storage_view_perm set all_pods pods pvcs
      Hall_storage_perm).
    apply statefulset_storage_view_match_distance.
    symmetry. exact Hset_view. }
  assert (Hfinal_distance :
      match_distance sts pods' pvcs' = match_distance set pods' pvcs').
  { apply statefulset_storage_view_match_distance. exact Hset_view. }
  assert (Hmissing_pods_final :
      missing_pod_keys set pods' = missing_pod_keys sts pods').
  { apply statefulset_storage_view_missing_pod_keys. symmetry. exact Hset_view. }
  assert (Hmissing_pvcs_final :
      missing_pvc_keys set pvcs' = missing_pvc_keys sts pvcs').
  { apply statefulset_storage_view_missing_pvc_keys. symmetry. exact Hset_view. }
  iEval (rewrite /own_missing_pod_reservations Hmissing_pods_final) in
    "Hreconcile_Hreserved_pods".
  iEval (rewrite /own_missing_pvc_reservations Hmissing_pvcs_final) in
    "Hreconcile_Hreserved_pvcs".
  destruct (decide (bad_pods = [])) as [Hbad_empty|Hbad_nonempty].
  - assert (Hall_good : Forall Good all_pods).
    { apply Forall_forall. intros pod Hpod.
      rewrite -list_elem_of_In in Hpod.
      destruct (decide (Good pod)) as [Hgood|Hnot_good]; first done.
      exfalso.
      assert (pod ∈ bad_pods) as Hbad.
      { unfold bad_pods. apply list_elem_of_filter. split; done. }
      rewrite Hbad_empty in Hbad. inversion Hbad. }
    assert (Hgood_eq : good_pods = all_pods).
    { rewrite Forall_forall in Hall_good.
      unfold good_pods. apply filter_all. intros pod Hpod.
      apply Hall_good. by rewrite -list_elem_of_In. }
    destruct Hreconcile_Hprogress as [Hcomplete|[Hprogress Hstrict]].
    + assert (current_state_matches sts pods' pvcs') as Hcomplete_sts.
      { apply (proj2
          (statefulset_storage_view_current_state_matches sts set
            pods' pvcs' Hset_view)).
        exact Hcomplete. }
      iEval (rewrite -Hset_key -Hset_uid) in
        "Hreconcile_Hown_children Hreconcile_Hterminating_children_frag".
      iApply ("HΦ" $! pods' pvcs' (phase_after_deletion Quiescent deletion) interface.nil).
      rewrite /statefulset_owned_resources /=.
      iFrame "Hown_sts_meta_frag Hown_sts_spec_frag
        Hreconcile_Hown_pods Hreconcile_Hown_pvcs
        Hreconcile_Hown_children Hreconcile_Hterminating_children_frag
        Hreconcile_Hoccupied_pods Hreconcile_Hoccupied_pvcs
        Hreconcile_Hreserved_pods Hreconcile_Hreserved_pvcs".
      iPureIntro. left. exact Hcomplete_sts.
    + assert (pod_storage_view <$> good_pods ≡ₚ
        pod_storage_view <$> pods) as Hgood_storage_perm.
      { rewrite Hgood_eq. exact Hall_storage_perm. }
      assert (pods_progress_observed pods pods') as Hprogress_sts.
      { eapply pods_progress_observed_storage_view_perm_left;
          [exact Hgood_storage_perm|exact Hprogress]. }
      assert (match_distance sts pods' pvcs' <
          match_distance sts pods pvcs) as Hstrict_sts.
      { rewrite Hfinal_distance -Hinitial_distance.
        rewrite Hgood_eq in Hstrict. exact Hstrict. }
      iEval (rewrite -Hset_key -Hset_uid) in
        "Hreconcile_Hown_children Hreconcile_Hterminating_children_frag".
      iApply ("HΦ" $! pods' pvcs' (phase_after_deletion Quiescent deletion) interface.nil).
      rewrite /statefulset_owned_resources /=.
      iFrame "Hown_sts_meta_frag Hown_sts_spec_frag
        Hreconcile_Hown_pods Hreconcile_Hown_pvcs
        Hreconcile_Hown_children Hreconcile_Hterminating_children_frag
        Hreconcile_Hoccupied_pods Hreconcile_Hoccupied_pvcs
        Hreconcile_Hreserved_pods Hreconcile_Hreserved_pvcs".
      iPureIntro. right. split; done.
  - assert (Hbad_distance :
      match_distance set all_pods pvcs =
        (match_distance set good_pods pvcs + length bad_pods)%nat).
    { assert (living_pods good_pods = good_pods) as Hgood_living.
      { unfold living_pods. apply filter_all. intros pod Hpod.
        unfold good_pods in Hpod.
        apply list_elem_of_filter in Hpod as [_ Hpod].
        assert (pod ∈ filter is_pod_alive all_pods) as Halive.
        { rewrite Hall_living. exact Hpod. }
        by apply list_elem_of_filter in Halive as [Halive _]. }
      change (filter is_pod_alive good_pods = good_pods) in Hgood_living.
      unfold match_distance, living_pods. rewrite Hall_living Hgood_living.
      rewrite pod_distance_filter_int32_members.
      assert (filter (pod_has_int32_member_key set) all_pods = good_pods)
        as Hgood_filter.
      { rewrite -(filter_int32_member_names_eq set all_pods Hall_namespaces).
        done. }
      assert (bad_name_pods set all_pods = bad_pods) as Hbad_filter.
      { symmetry.
        unfold bad_pods, Good.
        apply filter_bad_int32_member_names_eq. exact Hall_namespaces. }
      rewrite Hgood_filter Hbad_filter. lia. }
    assert (Hstrict_sts : match_distance sts pods' pvcs' <
        match_distance sts pods pvcs).
    { rewrite Hfinal_distance -Hinitial_distance.
      destruct bad_pods; [contradiction|]. simpl in Hbad_distance. lia. }
    assert (Hprogress_sts : pods_progress_observed pods pods').
    { left. intros Hsame_keys.
      destruct bad_pods as [|bad_pod bad_pods_tail] eqn:Hbad;
        first contradiction.
      assert (bad_pod ∈ bad_pods) as Hbad_pod by
        (rewrite Hbad; left).
      unfold bad_pods in Hbad_pod.
      apply list_elem_of_filter in Hbad_pod as [Hbad_name Hbad_all].
      assert (PodV.key bad_pod ∈ PodV.key <$> pods) as Hbad_initial.
      { rewrite -Hall_key_perm. by apply list_elem_of_fmap_2. }
      assert (PodV.key bad_pod ∈
          list_to_set (C:=gset KKey.t) (PodV.key <$> pods))
        as Hbad_initial_set by
        (rewrite elem_of_list_to_set; exact Hbad_initial).
      rewrite Hsame_keys elem_of_list_to_set in Hbad_initial_set.
      apply list_elem_of_fmap_1 in Hbad_initial_set as
        (final_pod & Hkey & Hfinal_pod).
      rewrite Forall_forall in Hreconcile_Hpods_members.
      assert (In final_pod pods') as Hfinal_pod_In.
      { by rewrite -list_elem_of_In. }
      pose proof (Hreconcile_Hpods_members final_pod Hfinal_pod_In)
        as Hfinal_good.
      apply Hbad_name. unfold Good in *.
      pose proof (f_equal KKey.Name' Hkey) as Hname.
      unfold PodV.key, PodV.meta_key in Hname. simpl in Hname.
      rewrite Hname. exact (proj2 Hfinal_good). }
    iEval (rewrite -Hset_key -Hset_uid) in
      "Hreconcile_Hown_children Hreconcile_Hterminating_children_frag".
    iApply ("HΦ" $! pods' pvcs' (phase_after_deletion Quiescent deletion) interface.nil).
    rewrite /statefulset_owned_resources /=.
    iFrame "Hown_sts_meta_frag Hown_sts_spec_frag
      Hreconcile_Hown_pods Hreconcile_Hown_pvcs
      Hreconcile_Hown_children Hreconcile_Hterminating_children_frag
      Hreconcile_Hoccupied_pods Hreconcile_Hoccupied_pvcs
      Hreconcile_Hreserved_pods Hreconcile_Hreserved_pvcs".
    iPureIntro. right. split; done.
Qed.

End proof.
