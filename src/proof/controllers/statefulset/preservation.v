From New.proof.controllers.statefulset Require Export reconcile_preservation.
From New.proof.controllers.statefulset Require Export top_level.
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

Lemma elem_of_drop_full {A} (xs : list A) n x :
  x ∈ drop n xs → x ∈ xs.
Proof.
  intros Hx. rewrite -(take_drop n xs). apply elem_of_app. right. exact Hx.
Qed.

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

Lemma filter_unreserved_pending_eq sts pods :
  NoDup (PodV.key <$> pods) →
  filter (pod_key_not_reserved (filter (pending_pod sts) pods)) pods =
    filter (λ pod, not (pending_pod sts pod)) pods.
Proof.
  intros Hnodup. apply list_filter_iff_strong. intros i pod Hlookup.
  assert (pod ∈ pods) as Hpod by exact (list_elem_of_lookup_2 pods i pod Hlookup).
  split.
  - intros Hunreserved Hpending. apply Hunreserved.
    apply list_elem_of_fmap_2. apply list_elem_of_filter. done.
  - intros Hnot_pending Hkey.
    apply list_elem_of_fmap_1 in Hkey as (pending & Hkey & Hpending).
    apply list_elem_of_filter in Hpending as [Hpending Hpending_in].
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

Lemma wp_syncStatefulSet_preservation γ l namespace name sts dq pods pvcs phase :
  ⊢ syncStatefulSet_preservation_spec γ l namespace name sts dq pods pvcs phase.
Proof.
  unfold syncStatefulSet_preservation_spec.
  wp_start as "H". iNamed "H". iNamed "Hresources".
  iEval (simpl) in "Hown_sts_meta_frag".
  iEval (simpl) in "Hown_sts_spec_frag".
  iEval (simpl) in "Hown_pod_frags".
  iEval (simpl) in "Hown_children_frag".
  iEval (simpl) in "Hown_terminating_children_frag".
  iEval (simpl) in "Hown_pvc_frags".
  iPoseProof (kview.own_meta_valid with "Hown_sts_meta_frag") as "%Hsts_meta_valid".
  destruct Hsts_meta_valid as (_ & _ & _ & _ & Hdeletion_timestamp_eq).
  iPoseProof (own_pod_frags_living with "Hown_pod_frags") as "%Hpods_living".
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
  set living_all := filter is_pod_alive all_pods.
  iEval (fold living_all) in "Hall_frags".
  change (pod_storage_view <$> living_all ≡ₚ pod_storage_view <$> pods)
    in Hall_living_storage_perm.
  pose proof (pod_storage_view_perm_keys _ _ Hall_living_storage_perm)
    as Hall_key_perm.
  pose proof (pod_storage_view_perm_reservation_identities _ _ Hall_living_storage_perm)
    as Hall_reservation_identities.
  iAssert ([∗ list] pod ∈ living_all,
      own_occupied_reserved_frag γ 1 (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID'))%I
    with "[Hoccupied_pods]" as "Hall_occupied".
  { rewrite !own_occupied_pods_as_identities.
    rewrite (big_sepL_permutation (λ identity, own_occupied_reserved_frag γ 1 identity.1 identity.2)
      (pod_reservation_identity <$> living_all)
      (pod_reservation_identity <$> pods) Hall_reservation_identities).
    iExact "Hoccupied_pods". }
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
      (list_to_set (PodV.key <$> living_all)))%I
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
  set good_living := filter Good living_all.
  set bad_living := filter (λ pod, ¬ Good pod) living_all.
  set BadLiving := (λ pod : PodV.t, ¬ Good pod ∧ is_pod_alive pod).
  assert (HGood_member : ∀ pod, pod ∈ all_pods →
      (Good pod ↔ pod_has_int32_member_key set pod)).
  { intros pod Hpod. unfold Good, pod_has_int32_member_key.
    split; intros Hgood.
    - split; last exact Hgood. rewrite Forall_forall in Hall_namespaces.
      apply Hall_namespaces. by rewrite -list_elem_of_In.
    - exact (proj2 Hgood). }
  assert (Hliving_nodup : NoDup (PodV.key <$> living_all)).
  { unfold living_all. by apply NoDup_fmap_filter. }
  assert (Hbad_living_eq : filter BadLiving all_pods = bad_living).
  { unfold BadLiving, bad_living, living_all.
    rewrite list_filter_filter. apply list_filter_iff. intros pod. tauto. }
  iEval (rewrite big_sepL_sep) in "Hall_frags".
  iDestruct "Hall_frags" as "[Hall_meta Hall_spec]".
  iDestruct (big_sepL_filter_partition Good _ living_all with "Hall_meta")
    as "[Hgood_meta Hbad_meta]".
  iDestruct (big_sepL_filter_partition Good _ living_all with "Hall_spec")
    as "[Hgood_spec Hbad_spec]".
  iDestruct (big_sepL_filter_partition Good _ living_all with "Hall_occupied")
    as "[Hgood_occupied Hbad_occupied]".
  iEval (fold good_living; fold bad_living) in
    "Hgood_meta Hgood_spec Hgood_occupied Hbad_meta Hbad_spec Hbad_occupied".
  iEval (rewrite -Hbad_living_eq) in "Hbad_meta Hbad_spec Hbad_occupied".
  assert (Hbad_releaseable : Forall
      (λ pod,
        PodV.valid pod ∧
        meta_parent_ref pod.(PodV.ObjectMeta') =
          Some (StatefulSetV.key set,
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')))
      all_pods).
  { exact (Forall_and Hall_valid Hall_parent_refs). }
  wp_apply (wp_releasePodsWithBadNames_combined γ l set_l all_sl
    set all_ptrs all_pods (list_to_set (PodV.key <$> living_all)) 1 pod_dq phase
    with "[$Hset $Hall_sl $Hall_pods $Hbad_meta $Hbad_spec
      $Hbad_occupied $Hall_deletion_observed $Hown_children_frag $Hown_terminating_children_frag]").
  { iFrame "#". iPureIntro. split_and!; done. }
  iIntros (released err) "Hrelease". iNamedPrefix "Hrelease" "Hrelease_".
  destruct err as [err_ok|].
  { wp_auto.
    set remaining_bad := filter BadLiving (drop released all_pods).
    set remaining_pods := good_living ++ remaining_bad.
    assert (Hremaining_children :
        list_to_set (C:=gset KKey.t) (PodV.key <$> remaining_pods) =
          list_to_set (PodV.key <$> living_all) ∖
            list_to_set (PodV.key <$> filter BadLiving (take released all_pods))).
    { unfold remaining_pods, remaining_bad, good_living, living_all.
      apply set_eq. intros key.
      rewrite elem_of_difference !elem_of_list_to_set fmap_app elem_of_app.
      split.
      - intros [Hgood|Hremaining].
        + apply list_elem_of_fmap_1 in Hgood as (pod & -> & Hgood).
          apply list_elem_of_filter in Hgood as [HGood Halive].
          apply list_elem_of_filter in Halive as [Halive Hall]. split.
          * apply list_elem_of_fmap_2. apply list_elem_of_filter. done.
          * intros Hbad. apply list_elem_of_fmap_1 in Hbad as (bad & Hkey & Hbad).
            apply list_elem_of_filter in Hbad as [[Hnot_good _] Hbad].
            assert (pod = bad) as ->.
            { eapply NoDup_fmap_inj_on; first exact Hall_nodup.
              - exact Hall.
              - rewrite elem_of_take in Hbad. destruct Hbad as (j & Hj & _).
                by eapply list_elem_of_lookup_2.
              - exact Hkey. }
            contradiction.
        + apply list_elem_of_fmap_1 in Hremaining as (pod & -> & Hremaining).
          apply list_elem_of_filter in Hremaining as [[_ Halive] Hdrop]. split.
          * apply list_elem_of_fmap_2. apply list_elem_of_filter. split; first done.
            eapply elem_of_drop_full. exact Hdrop.
          * intros Htaken. apply list_elem_of_fmap_1 in Htaken as (taken & Hkey & Htaken).
            apply list_elem_of_filter in Htaken as [_ Htake].
            assert (pod = taken) as ->.
            { eapply NoDup_fmap_inj_on; first exact Hall_nodup.
              - eapply elem_of_drop_full. exact Hdrop.
              - rewrite elem_of_take in Htake. destruct Htake as (j & Hj & _).
                by eapply list_elem_of_lookup_2.
              - exact Hkey. }
            pose proof Hall_nodup as Hall_pods_nodup.
            apply NoDup_fmap_1 in Hall_pods_nodup.
            rewrite elem_of_take in Htake.
            rewrite list_elem_of_lookup in Hdrop.
            destruct Hdrop as (j & Hj).
            rewrite lookup_drop in Hj.
            destruct Htake as (k & Hk & Hk_lt).
            pose proof (NoDup_lookup all_pods (released + j) k taken Hall_pods_nodup Hj Hk). lia.
      - intros [Hall Hnot_taken].
        apply list_elem_of_fmap_1 in Hall as (pod & -> & Halive).
        apply list_elem_of_filter in Halive as [Halive Hall].
        destruct (decide (Good pod)) as [Hgood|Hbad].
        + left. apply list_elem_of_fmap_2. apply list_elem_of_filter. split; first done.
          apply list_elem_of_filter. done.
        + right. apply list_elem_of_fmap_2. apply list_elem_of_filter. split; first done.
          rewrite -(take_drop released all_pods) in Hall.
          apply elem_of_app in Hall as [Htake|Hdrop]; last done.
          exfalso. apply Hnot_taken. apply list_elem_of_fmap_2. apply list_elem_of_filter. done. }
    assert (Hdesired_good : ∀ pod, pod ∈ all_pods →
        pod_key_is_desired set (PodV.key pod) → Good pod).
    { intros pod Hpod Hdesired. apply (proj2 (HGood_member pod Hpod)).
      apply pod_key_desired_is_int32_member. exact Hdesired. }
    assert (Hmissing_remaining :
        missing_pod_keys sts remaining_pods = missing_pod_keys sts pods).
    { transitivity (missing_pod_keys set remaining_pods).
      - apply statefulset_storage_view_missing_pod_keys. exact Hset_view.
      - transitivity (missing_pod_keys set living_all).
        2: { transitivity (missing_pod_keys set pods).
          - apply missing_pod_keys_storage_view_perm. exact Hall_living_storage_perm.
          - apply statefulset_storage_view_missing_pod_keys. symmetry. exact Hset_view. }
        unfold missing_pod_keys. apply list_filter_iff_strong. intros i key Hlookup.
        split; intros Hnot Hin; apply Hnot.
        + apply list_elem_of_fmap_1 in Hin as (pod & Hkey & Hliving).
          rewrite Hkey. apply list_elem_of_fmap_2. unfold remaining_pods. apply elem_of_app. left.
          unfold good_living. apply list_elem_of_filter in Hliving as [Halive Hall].
          apply list_elem_of_filter. split; last (apply list_elem_of_filter; done).
          apply (Hdesired_good pod Hall).
          unfold desired_pod_keys in Hlookup.
          apply list_elem_of_lookup_2 in Hlookup.
          apply list_elem_of_fmap_1 in Hlookup as (ordinal & Hkey' & Hordinal).
          unfold pod_key_is_desired, desired_pod_keys. rewrite -Hkey Hkey'. by apply list_elem_of_fmap_2.
        + unfold remaining_pods in Hin. apply list_elem_of_fmap_1 in Hin as (pod & Hkey & Hremaining).
          apply elem_of_app in Hremaining as [Hgood|Hremaining]; rewrite Hkey; apply list_elem_of_fmap_2.
          * unfold good_living in Hgood. by apply list_elem_of_filter in Hgood as [_ Hgood].
          * unfold remaining_bad in Hremaining. apply list_elem_of_filter in Hremaining as [[_ Halive] Hdrop].
            apply list_elem_of_filter. split; first done. eapply elem_of_drop_full; exact Hdrop. }
    assert (Hdistance_remaining :
      match_distance sts remaining_pods pvcs ≤ match_distance sts pods pvcs).
    { transitivity (match_distance set remaining_pods pvcs).
      { rewrite (statefulset_storage_view_match_distance sts set remaining_pods pvcs Hset_view). done. }
      transitivity (match_distance set living_all pvcs).
      2: { rewrite (match_distance_storage_view_perm set living_all pods pvcs Hall_living_storage_perm).
        rewrite (statefulset_storage_view_match_distance sts set pods pvcs Hset_view). done. }
      unfold match_distance.
      assert (Hremaining_alive : living_pods remaining_pods = remaining_pods).
      { unfold living_pods. apply filter_all. intros pod Hpod.
        unfold remaining_pods in Hpod. apply elem_of_app in Hpod as [Hgood|Hremaining].
        - unfold good_living in Hgood. apply list_elem_of_filter in Hgood as [_ Hliving].
          unfold living_all in Hliving. by apply list_elem_of_filter in Hliving as [Halive _].
        - unfold remaining_bad in Hremaining. by apply list_elem_of_filter in Hremaining as [[_ Halive] _]. }
      assert (Hliving_all_alive : living_pods living_all = living_all).
      { unfold living_pods, living_all. rewrite list_filter_filter.
        apply list_filter_iff. intros pod. tauto. }
      rewrite Hremaining_alive Hliving_all_alive.
      rewrite pod_distance_filter_int32_members.
      assert (Hmembers : filter (pod_has_int32_member_key set) remaining_pods = good_living).
      { unfold remaining_pods. rewrite list.filter_app.
        assert (filter (pod_has_int32_member_key set) good_living = good_living) as ->.
        { apply filter_all. intros pod Hpod.
          assert (pod ∈ all_pods) as Hall.
          { unfold good_living, living_all in Hpod.
            apply list_elem_of_filter in Hpod as [_ Hpod].
            by apply list_elem_of_filter in Hpod as [_ Hpod]. }
          apply (proj1 (HGood_member pod Hall)).
          unfold good_living in Hpod. by apply list_elem_of_filter in Hpod as [Hgood _]. }
        assert (filter (pod_has_int32_member_key set) remaining_bad = []) as ->.
        { apply filter_none. intros pod Hpod Hmember. unfold remaining_bad in Hpod.
          apply list_elem_of_filter in Hpod as [[Hbad _] Hdrop]. apply Hbad.
          apply (proj2 (HGood_member pod (elem_of_drop_full _ _ _ Hdrop))). exact Hmember. }
        apply app_nil_r. }
      rewrite Hmembers.
      assert (Hbad_names_le : length (bad_name_pods set remaining_pods) ≤ length bad_living).
      { assert (NoDup (bad_name_pods set remaining_pods)) as Hbad_nodup.
        { unfold bad_name_pods. apply list.NoDup_filter.
          apply NoDup_fmap_1 in Hall_nodup.
          apply list.NoDup_app. split_and!.
          + unfold good_living, living_all. apply list.NoDup_filter. apply list.NoDup_filter. exact Hall_nodup.
          + intros pod Hgood Hbad. unfold good_living, living_all in Hgood.
            apply list_elem_of_filter in Hgood as [HGood Hgood].
            apply list_elem_of_filter in Hgood as [_ Hall].
            unfold remaining_bad in Hbad. apply list_elem_of_filter in Hbad as [[Hnot_good _] _]. contradiction.
          + unfold remaining_bad. apply list.NoDup_filter.
            rewrite -(take_drop released all_pods) in Hall_nodup.
            by apply list.NoDup_app in Hall_nodup as (_ & _ & Hall_nodup). }
        assert (∀ pod, pod ∈ bad_name_pods set remaining_pods → pod ∈ bad_living) as Hbad_incl.
        { unfold bad_name_pods, bad_living. intros pod Hpod.
          apply list_elem_of_filter in Hpod as [Hnot_member Hremaining].
          apply list_elem_of_filter. split.
          + intros Hgood. apply Hnot_member.
            assert (pod ∈ all_pods) as Hall.
            { unfold remaining_pods in Hremaining. apply elem_of_app in Hremaining as [Hliving|Hbad].
              -- unfold good_living, living_all in Hliving.
                 apply list_elem_of_filter in Hliving as [_ Hliving].
                 by apply list_elem_of_filter in Hliving as [_ Hliving].
              -- unfold remaining_bad in Hbad. apply list_elem_of_filter in Hbad as [_ Hdrop].
                 eapply elem_of_drop_full. exact Hdrop. }
            exact ((proj1 (HGood_member pod Hall)) Hgood).
          + unfold remaining_pods in Hremaining. apply elem_of_app in Hremaining as [Hgood|Hbad].
            * exfalso. apply Hnot_member. unfold good_living, living_all in Hgood.
              apply list_elem_of_filter in Hgood as [HGood Hliving].
              apply list_elem_of_filter in Hliving as [_ Hall].
              exact ((proj1 (HGood_member pod Hall)) HGood).
            * unfold remaining_bad in Hbad. apply list_elem_of_filter in Hbad as [[Hnot_good Halive] Hdrop].
              apply list_elem_of_filter. split; first exact Halive. eapply elem_of_drop_full; exact Hdrop. }
        assert (List.incl (bad_name_pods set remaining_pods) bad_living) as Hbad_incl'.
        { intros pod Hpod. apply list_elem_of_In. apply Hbad_incl. by apply list_elem_of_In. }
        apply NoDup_ListNoDup in Hbad_nodup.
        pose proof (NoDup_incl_length Hbad_nodup Hbad_incl'). lia. }
      rewrite (pod_distance_filter_int32_members set living_all).
      assert (Forall (λ pod,
          pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')) living_all) as Hliving_namespaces.
      { unfold living_all. by apply Forall_filter. }
      assert (Hliving_members : filter (pod_has_int32_member_key set) living_all = good_living).
      { unfold good_living, Good.
        rewrite -(filter_int32_member_names_eq set living_all Hliving_namespaces). done. }
      assert (Hbad_living_keys : bad_name_pods set living_all = bad_living).
      { symmetry. unfold bad_living, Good. apply filter_bad_int32_member_names_eq. exact Hliving_namespaces. }
      rewrite Hliving_members Hbad_living_keys. lia. }
    iCombine "Hgood_meta Hgood_spec" as "Hgood_frags".
    iEval (rewrite -big_sepL_sep) in "Hgood_frags".
    iCombine "Hrelease_Hown_meta Hrelease_Hown_spec" as "Hremaining_bad_frags".
    iEval (rewrite -big_sepL_sep) in "Hremaining_bad_frags".
    iCombine "Hgood_frags Hremaining_bad_frags" as "Hremaining_frags".
    iAssert (([∗ list] pod ∈ remaining_pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec')))%I)
      with "[Hremaining_frags]" as "Hremaining_frags".
    { rewrite /remaining_pods big_sepL_app. iFrame. }
    iEval (rewrite big_sepL_sep) in "Hremaining_frags".
    iDestruct "Hremaining_frags" as "[Hremaining_meta Hremaining_spec]".
    iPoseProof (kview.own_meta_list_no_dup PodV.key PodV.ObjectMeta'
      with "Hremaining_meta") as "%Hremaining_nodup".
    iCombine "Hremaining_meta Hremaining_spec" as "Hremaining_frags".
    iEval (rewrite -big_sepL_sep) in "Hremaining_frags".
    iCombine "Hgood_occupied Hrelease_Hown_occupied" as "Hremaining_occupied".
    iAssert ([∗ list] pod ∈ remaining_pods,
        own_occupied_reserved_frag γ 1 (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID'))%I
      with "[Hremaining_occupied]" as "Hremaining_occupied".
    { rewrite /remaining_pods big_sepL_app. iFrame. }
    iAssert (own_missing_pod_reservations γ sts remaining_pods)
      with "[Hreserved_pods]" as "Hreserved_pods".
    { unfold own_missing_pod_reservations. rewrite Hmissing_remaining. iFrame. }
    iAssert (own_children_frag γ (StatefulSetV.key sts)
        sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> remaining_pods)))
      with "[Hrelease_Hown_children]" as "Hremaining_children".
    { rewrite Hset_key Hset_uid Hremaining_children. iFrame. }
    iEval (rewrite -Hset_key -Hset_uid) in "Hrelease_Hown_terminating_children_frag".
    iApply ("HΦ" $! remaining_pods pvcs phase (interface.ok err_ok)).
    rewrite /statefulset_owned_resources /=.
    iFrame "Hown_sts_meta_frag Hown_sts_spec_frag Hremaining_frags Hremaining_occupied
      Hown_pvc_frags Hoccupied_pvcs Hremaining_children Hrelease_Hown_terminating_children_frag
      Hreserved_pods Hreserved_pvcs".
    iPureIntro. split; done. }
  specialize (Hrelease_Hdone eq_refl). subst released. wp_auto.
  assert (Htake_all_pods : take (length all_pods) all_pods = all_pods).
  { apply take_ge. lia. }
  iEval (rewrite Htake_all_pods Hbad_living_eq) in "Hrelease_Hown_children".
  iAssert (own_children_frag γ (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (list_to_set (PodV.key <$> good_living)))%I
    with "[Hrelease_Hown_children]" as "Hgood_children".
  { unfold good_living, bad_living.
    rewrite (list_to_set_fmap_filter_difference PodV.key Good living_all
      Hliving_nodup).
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
  set pending_actual := filter (pending_pod set) good_pods.
  assert (Hpending_actual_nodup :
      NoDup (PodV.key <$> pending_actual)).
  { unfold pending_actual. by apply NoDup_fmap_filter. }
  assert (Hpending_actual_subset : pending_actual ⊆ good_pods).
  { intros pod Hpod. apply list_elem_of_filter in Hpod as [_ Hpod]. done. }
  assert (Hgood_unreserved :
      unreserved_pods pending_actual good_pods = good_living).
  { unfold unreserved_pods.
    rewrite (filter_unreserved_pending_eq set good_pods Hgood_nodup).
    unfold pending_actual, good_pods, good_living, living_all.
    rewrite !list_filter_filter. apply list_filter_iff. intros pod.
    unfold pending_pod, Good. tauto. }
  iAssert (own_unreserved_pods γ pending_actual good_pods)
    with "[Hgood_frags Hgood_occupied]" as "Hgood_owned".
  { unfold own_unreserved_pods. rewrite Hgood_unreserved !big_sepL_sep. iFrame. }
  iAssert (own_children_frag γ (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (list_to_set (PodV.key <$> unreserved_pods pending_actual good_pods)))
    with "[Hgood_children]" as "Hgood_children".
  { rewrite Hgood_unreserved. iFrame. }
  assert (Hinput_requirement_set : input_requirement set).
  { apply (proj1
      (statefulset_storage_view_input_requirement sts set Hset_view)).
    exact Hinput_requirement. }
  assert (Hmissing_pods :
      missing_pod_keys set good_living = missing_pod_keys sts pods).
  { unfold good_living.
    assert (Forall (λ pod,
        pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')) living_all) as Hliving_namespaces.
    { unfold living_all. by apply Forall_filter. }
    rewrite (filter_int32_member_names_eq set living_all Hliving_namespaces).
    rewrite missing_pod_keys_filter_int32_members.
    rewrite (missing_pod_keys_storage_view_perm set living_all pods Hall_living_storage_perm).
    apply statefulset_storage_view_missing_pod_keys.
    symmetry. exact Hset_view. }
  assert (Hmissing_pvcs :
      missing_pvc_keys set pvcs = missing_pvc_keys sts pvcs).
  { apply statefulset_storage_view_missing_pvc_keys.
    symmetry. exact Hset_view. }
  iEval (rewrite /own_missing_pod_reservations -Hmissing_pods) in "Hreserved_pods".
  iEval (rewrite -Hgood_unreserved) in "Hreserved_pods".
  iEval (rewrite /own_missing_pvc_reservations -Hmissing_pvcs) in "Hreserved_pvcs".
  iCombine "Hown_pvc_frags Hoccupied_pvcs" as "Hown_pvcs".
  iEval (rewrite -big_sepL_sep) in "Hown_pvcs".
  wp_auto.
  wp_apply (wp_reconcileReplicas_preservation γ l set_l good_sl set
    good_ptrs good_pods pending_actual pvcs 1 pod_dq phase
    with "[$Hset $Hgood_sl $Hgood_pods $Hgood_owned
      $Hown_pvcs $Hgood_children $Hrelease_Hown_terminating_children_frag
      $Hreserved_pods $Hreserved_pvcs]").
  { iFrame "#". iPureIntro. split_and!; try done. }
  iIntros (pods1 pvcs' phase') "Hreconcile".
  iNamedPrefix "Hreconcile" "Hreconcile_". wp_auto.

  set pods' := unreserved_pods pending_actual pods1.
  assert (Hfinal_storage_perm :
      pod_storage_view <$> (pending_actual ++ pods') ≡ₚ pod_storage_view <$> pods1).
  { unfold pods'. eapply replace_reserved_storage_perm; try done. }
  iEval (rewrite /own_unreserved_pods /pods' !big_sepL_sep) in
    "Hreconcile_Hown_pods".
  iDestruct "Hreconcile_Hown_pods" as
    "[Hfinal_meta [Hfinal_spec Hfinal_occupied]]".
  iPoseProof (kview.own_meta_list_no_dup PodV.key PodV.ObjectMeta'
    with "Hfinal_meta") as "%Hpods'_nodup".
  iCombine "Hfinal_meta Hfinal_spec" as "Hfinal_pod_frags".
  iEval (rewrite -big_sepL_sep) in "Hfinal_pod_frags".
  iPoseProof (own_pod_frags_living with "Hfinal_pod_frags") as "%Hpods'_living".
  iEval (rewrite big_sepL_sep) in "Hreconcile_Hown_pvcs".
  iDestruct "Hreconcile_Hown_pvcs" as "[Hfinal_pvcs Hfinal_occupied_pvcs]".
  assert (Hliving_good : living_pods good_pods = good_living).
  { unfold living_pods, good_pods, good_living, living_all.
    rewrite !list_filter_filter. apply list_filter_iff. intros pod. tauto. }
  assert (Hinitial_distance :
      match_distance set living_all pvcs = match_distance sts pods pvcs).
  { rewrite (match_distance_storage_view_perm set living_all pods pvcs Hall_living_storage_perm).
    apply statefulset_storage_view_match_distance.
    symmetry. exact Hset_view. }
  assert (Hbad_distance :
      match_distance set living_all pvcs =
        (match_distance set good_living pvcs + length bad_living)%nat).
  { assert (living_pods living_all = living_all) as Hliving_idem.
    { unfold living_pods, living_all. rewrite list_filter_filter.
      apply list_filter_iff. intros pod. tauto. }
    unfold match_distance. rewrite Hliving_idem
      (pod_distance_filter_int32_members set living_all).
    assert (filter (pod_has_int32_member_key set) living_all = good_living)
      as Hgood_filter.
    { assert (Forall (λ pod,
          pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')) living_all) as Hliving_namespaces.
      { unfold living_all. by apply Forall_filter. }
      rewrite -(filter_int32_member_names_eq set living_all Hliving_namespaces).
      done. }
    assert (bad_name_pods set living_all = bad_living) as Hbad_filter.
    { symmetry. unfold bad_living, Good.
      assert (Forall (λ pod,
          pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')) living_all) as Hliving_namespaces.
      { unfold living_all. by apply Forall_filter. }
      apply filter_bad_int32_member_names_eq. exact Hliving_namespaces. }
    assert (living_pods good_living = good_living) as Hgood_living_idem.
    { unfold living_pods. apply filter_all. intros pod Hpod.
      unfold good_living in Hpod. apply list_elem_of_filter in Hpod as [_ Hpod].
      unfold living_all in Hpod. by apply list_elem_of_filter in Hpod as [Halive _]. }
    rewrite Hgood_filter Hbad_filter Hgood_living_idem. lia. }
  assert (Hfinal_distance :
      match_distance sts pods' pvcs' = match_distance set pods1 pvcs').
  { transitivity (match_distance set pods' pvcs').
    - apply statefulset_storage_view_match_distance. exact Hset_view.
    - assert (filter is_pod_alive pending_actual = []) as Hpending_dead.
      { apply filter_none. intros pod Hpod Halive.
        unfold pending_actual in Hpod. apply list_elem_of_filter in Hpod as [Hpending _].
        exact ((proj1 Hpending) Halive). }
      assert (filter is_pod_alive pods' = pods') as Hfinal_living.
      { apply filter_all. intros pod Hpod. rewrite Forall_forall in Hpods'_living.
        apply Hpods'_living. by rewrite -list_elem_of_In. }
      transitivity (match_distance set (pending_actual ++ pods') pvcs').
      + assert (living_pods (pending_actual ++ pods') = pods') as Happ_living.
        { unfold living_pods. rewrite list.filter_app.
          rewrite Hpending_dead Hfinal_living. done. }
        unfold match_distance. rewrite Happ_living.
        unfold living_pods. rewrite Hfinal_living. done.
      + apply match_distance_storage_view_perm. exact Hfinal_storage_perm. }
  assert (Hdistance :
      match_distance sts pods' pvcs' ≤ match_distance sts pods pvcs).
  { rewrite Hfinal_distance -Hinitial_distance.
    etrans; first exact Hreconcile_Hdistance.
    assert (match_distance set good_pods pvcs = match_distance set good_living pvcs) as Hgood_distance.
    { unfold match_distance. rewrite Hliving_good.
      assert (living_pods good_living = good_living) as ->.
      { unfold living_pods. apply filter_all. intros pod Hpod.
        unfold good_living in Hpod. apply list_elem_of_filter in Hpod as [_ Hpod].
        unfold living_all in Hpod. by apply list_elem_of_filter in Hpod as [Halive _]. }
      done. }
    rewrite Hgood_distance. lia. }
  assert (Hmissing_final : missing_pod_keys set pods' = missing_pod_keys sts pods').
  { apply statefulset_storage_view_missing_pod_keys. symmetry. exact Hset_view. }
  assert (Hmissing_pvcs_final : missing_pvc_keys set pvcs' = missing_pvc_keys sts pvcs').
  { apply statefulset_storage_view_missing_pvc_keys. symmetry. exact Hset_view. }
  iEval (rewrite /own_missing_pod_reservations Hmissing_final) in
    "Hreconcile_Hreserved_pods".
  iEval (rewrite /own_missing_pvc_reservations Hmissing_pvcs_final) in
    "Hreconcile_Hreserved_pvcs".
  iEval (rewrite -Hset_key -Hset_uid) in
    "Hreconcile_Hown_children Hreconcile_Hown_terminating_children_frag".
  iApply ("HΦ" $! pods' pvcs' phase' interface.nil).
  rewrite /statefulset_owned_resources /=.
  iFrame "Hown_sts_meta_frag Hown_sts_spec_frag Hfinal_pod_frags Hfinal_occupied
    Hfinal_pvcs Hfinal_occupied_pvcs Hreconcile_Hown_children
    Hreconcile_Hown_terminating_children_frag Hreconcile_Hreserved_pods
    Hreconcile_Hreserved_pvcs".
  iPureIntro. split; done.
Qed.

End proof.
