From New.proof.controllers.statefulset Require Export reconcile_progress.
From New.proof.controllers.statefulset Require Import create_pvc update_pod
  release condemned outdated.
From New.proof.kubernetes_model Require Import get.
From New.proof.map Require Import for_range.

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

Lemma pods_match_storage_view_perm set pods1 pods2 :
  pod_storage_view <$> pods1 ≡ₚ pod_storage_view <$> pods2 →
  (pods_match set pods1 ↔ pods_match set pods2).
Proof.
  intros Hperm. unfold pods_match.
  pose proof (Permutation_map pod_view_key Hperm) as Hkeys.
  assert (PodV.key <$> pods1 ≡ₚ PodV.key <$> pods2) as Hkey_perm.
  { assert (∀ pods : list PodV.t,
        map pod_view_key (map pod_storage_view pods) =
          map PodV.key pods) as Hobserve.
    { intros pods. induction pods as [|pod pods IH]; simpl; first done.
      f_equal. exact IH. }
    rewrite (Hobserve pods1) (Hobserve pods2) in Hkeys.
    exact Hkeys. }
  assert (Forall is_pod_alive pods1 ↔ Forall is_pod_alive pods2)
      as Halive.
  { assert (∀ pods : list PodV.t, Forall is_pod_alive pods ↔
        Forall pod_view_alive (pod_storage_view <$> pods)) as Hobserve.
    { intros pods. rewrite Forall_fmap.
      apply Forall_iff. intros pod.
      symmetry.
      exact (proj1 (proj2 (pod_storage_view_observations pod))). }
    assert (Forall pod_view_alive (pod_storage_view <$> pods1) ↔
        Forall pod_view_alive (pod_storage_view <$> pods2)) as Hviews.
    { split; intros H.
      - eapply Permutation_Forall; [exact Hperm|exact H].
      - eapply Permutation_Forall;
          [apply Permutation_sym; exact Hperm|exact H]. }
    rewrite (Hobserve pods1) (Hobserve pods2). exact Hviews. }
  assert (Forall (pod_match set) pods1 ↔
      Forall (pod_match set) pods2) as Hmatches.
  { assert (∀ pods : list PodV.t, Forall (pod_match set) pods ↔
        Forall (pod_view_match set) (pod_storage_view <$> pods))
        as Hobserve.
    { intros pods. rewrite Forall_fmap.
      apply Forall_iff. intros pod.
      symmetry.
      exact (proj2 (proj2
        ((proj2 (proj2 (pod_storage_view_observations pod))) set))). }
    assert (Forall (pod_view_match set) (pod_storage_view <$> pods1) ↔
        Forall (pod_view_match set) (pod_storage_view <$> pods2)) as Hviews.
    { split; intros H.
      - eapply Permutation_Forall; [exact Hperm|exact H].
      - eapply Permutation_Forall;
          [apply Permutation_sym; exact Hperm|exact H]. }
    rewrite (Hobserve pods1) (Hobserve pods2). exact Hviews. }
  rewrite Hkey_perm Halive Hmatches. done.
Qed.

Lemma current_state_matches_storage_view_perm set pods1 pods2 pvcs :
  pod_storage_view <$> pods1 ≡ₚ pod_storage_view <$> pods2 →
  (current_state_matches set pods1 pvcs ↔
   current_state_matches set pods2 pvcs).
Proof.
  intros Hperm. unfold current_state_matches.
  rewrite (pods_match_storage_view_perm set pods1 pods2 Hperm). done.
Qed.

Lemma pods_match_members set pods :
  pods_match set pods →
  Forall (pod_has_int32_member_key set) pods.
Proof.
  intros (Hkeys & _). apply Forall_forall. intros pod Hpod.
  apply pod_key_desired_is_int32_member.
  unfold pod_key_is_desired.
  rewrite -Hkeys.
  apply list_elem_of_fmap_2. by rewrite list_elem_of_In.
Qed.

Lemma pods_match_no_pending set pods :
  pods_match set pods → filter (pending_pod set) pods = [].
Proof.
  intros (_ & Halive & _). apply filter_none.
  rewrite Forall_forall in Halive.
  intros pod Hpod [Hnot_alive _]. apply Hnot_alive.
  apply Halive. by rewrite -list_elem_of_In.
Qed.

Lemma pods_match_no_condemned set pods :
  pods_match set pods →
  Forall (λ pod, ¬ pod_is_condemned set pod) pods.
Proof.
  intros Hmatch.
  pose proof (pods_match_members set pods Hmatch) as Hmembers.
  destruct Hmatch as (Hkeys & _).
  apply Forall_forall. intros pod Hpod Hcondemned.
  assert (pod_key_is_desired set (PodV.key pod)) as Hdesired.
  { unfold pod_key_is_desired. rewrite -Hkeys.
    apply list_elem_of_fmap_2. by rewrite list_elem_of_In. }
  rewrite Forall_forall in Hmembers.
  pose proof (Hmembers pod Hpod) as Hmember.
  apply (proj1 (pod_int32_member_condemned_iff set pod Hmember))
    in Hcondemned.
  exact (Hcondemned Hdesired).
Qed.

Lemma pods_match_no_outdated set pods :
  pods_match set pods →
  Forall (λ pod, ¬ pod_is_outdated set pod) pods.
Proof.
  intros (_ & _ & Hmatches).
  eapply Forall_impl; last exact Hmatches.
  intros pod [_ Himmutable] Houtdated.
  destruct Houtdated as (_ & _ & _ & _ & Hnot_immutable).
  contradiction.
Qed.

Lemma wp_updateStatefulPod_stability set_l pod_l
    (set : StatefulSetV.t) (pod : PodV.t) dq_set dq_pod :
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hpod_name_len" ∷ ⌜ Z.of_nat
        (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max ⌝ ∗
      "%Hidentity" ∷ ⌜ pod_identity_matches set pod ⌝
  }}}
    @! statefulset.updateStatefulPod #set_l #pod_l
  {{{ RET #interface.nil;
      StatefulSetV.deepown_l set_l set dq_set ∗
      PodV.deepown_l pod_l pod dq_pod
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_identityMatches set_l pod_l set pod dq_set dq_pod
    with "[$Hset $Hpod]").
  { iPureIntro. exact Hpod_name_len. }
  iIntros (identity_ret) "(Hset & Hpod & %Hidentity_ret)".
  destruct identity_ret.
  - wp_auto. iApply "HΦ". iFrame.
  - exfalso. apply Hidentity_ret in Hidentity. done.
Qed.

Lemma wp_releasePodsWithBadNames_stability set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc) (pods : list PodV.t)
    dq_set dq_pods :
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "%Hname_lengths" ∷ ⌜ Forall (λ pod,
        Z.of_nat (length
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max)
        pods ⌝ ∗
      "%Hmembers" ∷ ⌜ Forall (λ pod,
        pod_has_int32_member_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) pods ⌝
  }}}
    @! statefulset.releasePodsWithBadNames #set_l #pods_sl
  {{{ RET #interface.nil;
      StatefulSetV.deepown_l set_l set dq_set ∗
      pods_sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iDestruct (own_slice_len with "Hpods_sl") as
    %(Hpods_sl_len1 & Hpods_sl_len2).
  iDestruct (own_slice_wf with "Hpods_sl") as %Hpods_sl_cap.
  iDestruct (big_sepL2_length with "Hpods") as %Hpods_len.
  set I := (∃ (i : w64) (pod_ptr_value : loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Hpod_ptr" ∷ pod_ptr ↦ pod_ptr_value ∗
    "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
    "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
      PodV.deepown_l ptr pod dq_pods) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len pods_sl) ⌝
  )%I.
  iAssert I with "[i set Hset pod Hpods_sl Hpods]" as "Hloop".
  { iExists (W64 0), (zero_val loc). iFrame. iPureIntro. word. }
  wp_for "Hloop". wp_if_destruct.
  - list_elem ptrs (sint.Z i) as this_ptr.
    destruct (decide
      (0 ≤ sint.Z i < sint.Z (slice.len pods_sl)))
      as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hpods_sl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hpods_sl". wp_auto.
    assert (∃ this_pod, pods !! sint.nat i = Some this_pod)
      as [this_pod Hthis_pod_lookup].
    { apply lookup_lt_is_Some_2.
      rewrite -Hpods_len Hpods_sl_len1. word. }
    iDestruct (big_sepL2_lookup_acc with "Hpods")
      as "[Hthis Hpods_restore]";
      [exact Hthis_ptr_lookup|exact Hthis_pod_lookup|].
    iPoseProof (PodV.deepown_l_split with "Hthis") as
      "(%Hthis_not_null & Hthis_typemeta & Hthis_meta_l &
        Hthis_spec_l & Hthis_status_l)".
    iDestruct "Hthis_meta_l" as (this_meta_c)
      "[Hthis_objectmeta_field Hthis_meta]".
    iNamedPrefix "Hthis_meta" "Hthis_meta_".
    iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
      "(%Hset_not_null & Hset_typemeta & Hset_meta_l &
        Hset_spec_l & Hset_status_l)".
    iDestruct "Hset_meta_l" as (set_meta_c)
      "[Hset_objectmeta_field Hset_meta]".
    iNamedPrefix "Hset_meta" "Hset_meta_".
    wp_auto.
    rewrite Hset_meta_Hdeepown_name Hthis_meta_Hdeepown_name.
    wp_apply (wp_isMemberOf with "[]").
    { iPureIntro. rewrite Forall_forall in Hname_lengths.
      apply Hname_lengths.
      rewrite -list_elem_of_In.
      by apply list_elem_of_lookup_2 in Hthis_pod_lookup. }
    iIntros (member) "%Hmember".
    iCombineNamed "Hset_meta_*" as "Hset_meta".
    iAssert (ObjectMetaV.deepown set_meta_c
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_meta]" as "Hset_meta".
    { iNamed "Hset_meta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l
        (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_meta]" as "Hset_meta_l".
    { iExists set_meta_c. iFrame. }
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_not_null
      with "[$Hset_typemeta $Hset_meta_l $Hset_spec_l $Hset_status_l]")
      as "Hset".
    iCombineNamed "Hthis_meta_*" as "Hthis_meta".
    iAssert (ObjectMetaV.deepown this_meta_c
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_meta]" as "Hthis_meta".
    { iNamed "Hthis_meta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr this_ptr)
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta_field Hthis_meta]" as "Hthis_meta_l".
    { iExists this_meta_c. iFrame. }
    iPoseProof (PodV.deepown_l_restore _ _ _ Hthis_not_null
      with "[$Hthis_typemeta $Hthis_meta_l $Hthis_spec_l
        $Hthis_status_l]") as "Hthis".
    assert (pod_has_int32_member_name
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        this_pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) as Hthis_member.
    { rewrite Forall_forall in Hmembers. apply Hmembers.
      rewrite -list_elem_of_In.
      by apply list_elem_of_lookup_2 in Hthis_pod_lookup. }
    destruct member.
    + wp_auto.
      iSpecialize ("Hpods_restore" with "Hthis").
      iApply wp_for_post_continue. wp_auto. iFrame "HΦ".
      iExists (word.add i (W64 1)), this_ptr. iFrame.
      iPureIntro. word.
    + exfalso. apply Hmember in Hthis_member. done.
  - iApply "HΦ". iFrame.
Qed.

Lemma wp_createPersistentVolumeClaim_stability_without_claim_templates
    γ model_l set_l pod_l claim_template_l
    (set : StatefulSetV.t) (pod : PodV.t)
    (claim_template : PersistentVolumeClaimV.t) (ordinal : nat)
    (existing_claim : PersistentVolumeClaimV.t)
    dq_set dq_pod dq_claim_template_ptr dq_claim_template dq_pvc
    set_phy claim_template_phy :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ statefulset_without_claim_templates_l
        set_l set dq_set set_phy ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "Hclaim_template_ptr" ∷
        claim_template_l ↦{dq_claim_template_ptr} claim_template_phy ∗
      "Hclaim_template" ∷ PersistentVolumeClaimV.deepown
        claim_template_phy claim_template dq_claim_template ∗
      "%Hordinal_bound" ∷
        ⌜ (ordinal ≤ go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
          desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ⌝ ∗
      "%Hpod_name_len" ∷
        ⌜ Z.of_nat
          (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤
            go_int_max ⌝ ∗
      "%Hkey" ∷ ⌜ PersistentVolumeClaimV.key existing_claim =
        new_persistent_volume_claim_key set claim_template ordinal ⌝ ∗
      "Hmeta" ∷ own_meta_frag γ
        (new_persistent_volume_claim_key set claim_template ordinal)
        existing_claim.(PersistentVolumeClaimV.ObjectMeta').(
          ObjectMetaV.UID') dq_pvc
        existing_claim.(PersistentVolumeClaimV.ObjectMeta')
  }}}
    @! statefulset.createPersistentVolumeClaim
      #set_l #pod_l #claim_template_l
  {{{ RET #interface.nil;
      statefulset_without_claim_templates_l
        set_l set dq_set set_phy ∗
      PodV.deepown_l pod_l pod dq_pod ∗
      claim_template_l ↦{dq_claim_template_ptr} claim_template_phy ∗
      PersistentVolumeClaimV.deepown
        claim_template_phy claim_template dq_claim_template ∗
      own_meta_frag γ
        (new_persistent_volume_claim_key set claim_template ordinal)
        existing_claim.(PersistentVolumeClaimV.ObjectMeta').(
          ObjectMetaV.UID') dq_pvc
        existing_claim.(PersistentVolumeClaimV.ObjectMeta')
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_newPersistentVolumeClaim_without_claim_templates
    set_l pod_l claim_template_l set pod claim_template ordinal
    dq_set dq_pod dq_claim_template_ptr dq_claim_template
    set_phy claim_template_phy
    with "[$Hpkg $Hset $Hpod $Hclaim_template_ptr $Hclaim_template]").
  { iFrame "%". }
  iIntros (claim_l) "H". iNamed "H".
  iPoseProof (PersistentVolumeClaimV.deepown_l_split with "Hclaim") as
    "(%Hclaim_l_not_null & Hclaim_typemeta & Hclaim_objectmeta_l &
      Hclaim_spec_l & Hclaim_status_l)".
  iDestruct "Hclaim_objectmeta_l" as (claim_meta_c)
    "[Hclaim_objectmeta_field Hclaim_objectmeta]".
  iNamedPrefix "Hclaim_objectmeta" "Hclaim_meta_".
  wp_auto.
  rewrite Hclaim_meta_Hdeepown_namespace Hclaim_meta_Hdeepown_name.
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  wp_apply (wp_State__PersistentVolumeClaimGet
    γ model_l
    (new_persistent_volume_claim_key set claim_template ordinal)
    (new_persistent_volume_claim set claim_template ordinal).(
      PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Namespace')
    (new_persistent_volume_claim set claim_template ordinal).(
      PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name')
    existing_claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')
    dq_pvc existing_claim.(PersistentVolumeClaimV.ObjectMeta')
    with "[$Hmeta]").
  { iFrame "#". iPureIntro.
    unfold new_persistent_volume_claim_key,
      PersistentVolumeClaimV.key, PersistentVolumeClaimV.meta_key,
      new_persistent_volume_claim. done. }
  iIntros (existing_claim_l existing_claim') "Hget".
  iNamedPrefix "Hget" "Hget_". wp_auto.
  wp_apply (wp_IsNotFound interface.nil with "[]").
  replace (bool_decide (not_found_error interface.nil)) with false by
    (symmetry; apply bool_decide_false; exact not_found_error_nil).
  wp_auto. iApply "HΦ".
  iFrame "Hset Hpod Hclaim_template_ptr Hclaim_template Hget_Hown_meta_frag".
Qed.

Lemma wp_createPersistentVolumeClaims_stability γ model_l set_l pod_l
    (set : StatefulSetV.t) (pod : PodV.t) (ordinal : nat)
    (pvcs : list PersistentVolumeClaimV.t) dq_set dq_pod dq_pvc :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')
          dq_pvc pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      "%Hordinal_lt" ∷
        ⌜ (ordinal < statefulset_replicas set)%nat ⌝ ∗
      "%Hpod_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
          desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ⌝ ∗
      "%Hpod_name_len" ∷
        ⌜ Z.of_nat
          (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤
            go_int_max ⌝ ∗
      "%Hpvcs_match" ∷ ⌜ pvcs_match set pvcs ⌝
  }}}
    @! statefulset.createPersistentVolumeClaims #set_l #pod_l
  {{{ RET #interface.nil;
      StatefulSetV.deepown_l set_l set dq_set ∗
      PodV.deepown_l pod_l pod dq_pod ∗
      ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')
          dq_pvc pvc.(PersistentVolumeClaimV.ObjectMeta'))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  pose proof (statefulset_replicas_le_go_int32_max set) as Hreplicas_bound.
  assert ((ordinal ≤ go_int32_max_nat)%nat) as Hordinal_bound by lia.
  wp_apply (wp_volumeClaimTemplatesByName set_l set dq_set with "Hset").
  iIntros (set_phy claim_templates_map claim_templates_list
    claim_templates_phy) "H".
  iDestruct "H" as "[Hset_ptr H]".
  iDestruct "H" as
    "(%Hdeepown_typemeta & Hdeepown_objectmeta &
      %Hdeepown_replicas_none & Hdeepown_replicas_some &
      %Hdeepown_selector_none & Hdeepown_selector_some &
      Hdeepown_template & %Hdeepown_volumeclaimtemplates_none &
      Hdeepown_volumeclaimtemplates &
      %Hclaim_templates_map_values & %Hclaim_templates_list_names &
      %Hclaim_templates_map_dom & %Hclaim_templates_map_eq &
      %Hdeepown_servicename &
      Hdeepown_status & Hclaim_templates_map)".
  iEval (rewrite /deepown_list) in "Hdeepown_volumeclaimtemplates".
  iDestruct "Hdeepown_volumeclaimtemplates" as
    "[Hclaim_templates_slice Hclaim_templates_deepown]".
  iAssert (statefulset_without_claim_templates_l
      set_l set dq_set set_phy)
    with "[Hset_ptr Hdeepown_objectmeta
      Hdeepown_replicas_some Hdeepown_selector_some
      Hdeepown_template Hdeepown_status]" as "Hset".
  { rewrite /statefulset_without_claim_templates_l.
    iFrame. iFrame "%". }
  set claim_templates :=
    StatefulSetSpecV.volume_claim_templates_list
      set.(StatefulSetV.Spec').
  set claim_templates_pure :=
    persistent_volume_claim_templates_by_name claim_templates.
  wp_auto.
  set P := (λ (_ : list go_string) (_ : Z),
    ∃ (last_claim_template : v1.PersistentVolumeClaim.t),
      "set" ∷ set_ptr ↦ set_l ∗
      "pod" ∷ pod_ptr ↦ pod_l ∗
      "claimTemplate" ∷ claimTemplate_ptr ↦ last_claim_template ∗
      "Hset" ∷ statefulset_without_claim_templates_l
        set_l set dq_set set_phy ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "Hclaim_templates_slice" ∷
        set_phy.(v1.StatefulSet.Spec').(
          v1.StatefulSetSpec.VolumeClaimTemplates')
          ↦* claim_templates_list ∗
      "Hclaim_templates_deepown" ∷
        ([∗ list] claim_template_phy;claim_template ∈
          claim_templates_list;claim_templates,
          PersistentVolumeClaimV.deepown
            claim_template_phy claim_template dq_set) ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')
          dq_pvc pvc.(PersistentVolumeClaimV.ObjectMeta')))%I.
  wp_apply (wp_map_for_range_return (key_type:=go.string) P
    with "Hclaim_templates_map").
  iIntros (keys) "%Hkeys".
  iSplitL "set pod claimTemplate Hset Hpod
      Hclaim_templates_slice Hclaim_templates_deepown Hown_pvcs".
  { iExists (zero_val v1.PersistentVolumeClaim.t). iFrame. }
  iSplitL "".
  { iModIntro.
    iIntros (z claim_template_name claim_template_phy)
      "%Hiter HP".
    destruct Hiter as (Hz_bounds & Hkey_lookup & Hclaim_lookup).
    iDestruct "HP" as (last_claim_template) "HP". iNamed "HP".
    iDestruct
      (persistent_volume_claim_template_lookup_acc
        claim_templates_phy claim_templates_list claim_templates
        claim_template_name claim_template_phy dq_set
        Hclaim_templates_map_eq Hclaim_lookup
        with "Hclaim_templates_deepown")
      as (claim_template)
        "(%Hclaim_template_lookup & Hclaim_template &
          Hclaim_templates_restore)".
    pose proof (Hclaim_templates_map_values _ _ Hclaim_lookup) as
      [_ Hclaim_template_phy_name].
    iDestruct (persistent_volume_claim_deepown_name with
      "Hclaim_template") as
      "[%Hclaim_template_deepown_name Hclaim_template]".
    assert (Hclaim_template_name :
        claim_template.(PersistentVolumeClaimV.ObjectMeta').(
          ObjectMetaV.Name') = claim_template_name) by congruence.
    assert (Hdesired_key : desired_pvc_key set claim_template_name ordinal
        ∈ desired_pvc_keys set).
    { eapply desired_pvc_key_of_template_is_desired;
        [exact Hordinal_lt|exact Hclaim_template_lookup]. }
    pose proof (Hpvcs_match _ Hdesired_key) as Hexisting.
    apply list_elem_of_fmap_1 in Hexisting as
      (existing_claim & Hexisting_key & Hexisting_in).
    assert (PersistentVolumeClaimV.key existing_claim =
        desired_pvc_key set claim_template_name ordinal)
      as Hexisting_key' by (symmetry; exact Hexisting_key).
    apply list_elem_of_lookup_1 in Hexisting_in as
      (existing_idx & Hexisting_lookup).
    iDestruct (big_sepL_lookup_acc with "Hown_pvcs") as
      "[Hexisting Hown_pvcs_restore]";
      first exact Hexisting_lookup.
    wp_auto.
    iAssert (own_meta_frag γ
        (new_persistent_volume_claim_key set claim_template ordinal)
        existing_claim.(PersistentVolumeClaimV.ObjectMeta').(
          ObjectMetaV.UID') dq_pvc
        existing_claim.(PersistentVolumeClaimV.ObjectMeta'))
      with "[Hexisting]" as "Hexisting".
    { rewrite new_persistent_volume_claim_key_eq
        Hclaim_template_name Hexisting_key.
      iExact "Hexisting". }
    wp_apply
      (wp_createPersistentVolumeClaim_stability_without_claim_templates
        γ model_l set_l pod_l claimTemplate_ptr set pod claim_template
        ordinal existing_claim dq_set dq_pod 1 dq_set dq_pvc
        set_phy claim_template_phy
        with "[$Hset $Hpod $claimTemplate
          $Hclaim_template $Hexisting]").
    { iFrame "# %". iPureIntro.
      rewrite new_persistent_volume_claim_key_eq
        Hclaim_template_name. exact Hexisting_key'. }
    iIntros
      "(Hset & Hpod & Hclaim_template_ptr & Hclaim_template &
        Hexisting)".
    iAssert (own_meta_frag γ (PersistentVolumeClaimV.key existing_claim)
        existing_claim.(PersistentVolumeClaimV.ObjectMeta').(
          ObjectMetaV.UID') dq_pvc
        existing_claim.(PersistentVolumeClaimV.ObjectMeta'))
      with "[Hexisting]" as "Hexisting".
    { rewrite new_persistent_volume_claim_key_eq
        Hclaim_template_name Hexisting_key.
      iExact "Hexisting". }
    iSpecialize ("Hown_pvcs_restore" with "Hexisting").
    iSpecialize ("Hclaim_templates_restore" with "Hclaim_template").
    wp_auto. iRight. iSplit; first done.
    iExists claim_template_phy.
    iFrame "set pod Hset Hpod Hclaim_template_ptr
      Hclaim_templates_slice Hclaim_templates_restore Hown_pvcs_restore".
  }
  iIntros "Hclaim_templates_map HP".
  iDestruct "HP" as (last_claim_template) "HP". iNamed "HP".
  iNamed "Hset".
  iAssert (StatefulSetV.deepown_l set_l set dq_set)
    with "[Hset_ptr Hdeepown_objectmeta
      Hset_spec_Hdeepown_replicas_some
      Hset_spec_Hdeepown_selector_some
      Hset_spec_Hdeepown_template Hclaim_templates_slice
      Hclaim_templates_deepown Hdeepown_status]" as "Hset".
  { iExists set_phy.
    rewrite /StatefulSetV.deepown /StatefulSetSpecV.deepown.
    iFrame "Hset_ptr Hdeepown_objectmeta
      Hset_spec_Hdeepown_replicas_some
      Hset_spec_Hdeepown_selector_some
      Hset_spec_Hdeepown_template Hdeepown_status".
    iFrame "%". iExists claim_templates_list.
    rewrite /deepown_list. iFrame. }
  wp_auto. iApply "HΦ". iFrame.
Qed.

Lemma wp_reconcileDesiredPods_stability γ model_l set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc)
    (pods : list PodV.t) (pvcs : list PersistentVolumeClaimV.t)
    dq_set dq_pods dq_pod_frag dq_pvc :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq_pod_frag
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq_pod_frag
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')
          dq_pvc pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      "%Hset_valid" ∷ ⌜ StatefulSetV.valid set ⌝ ∗
      "%Hpods_valid" ∷ ⌜ Forall PodV.valid pods ⌝ ∗
      "%Hmatch" ∷ ⌜ current_state_matches set pods pvcs ⌝
  }}}
    @! statefulset.reconcileDesiredPods #set_l #pods_sl
  {{{ RET (#true, #interface.nil);
      StatefulSetV.deepown_l set_l set dq_set ∗
      pods_sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq_pod_frag
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq_pod_frag
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')
          dq_pvc pvc.(PersistentVolumeClaimV.ObjectMeta'))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  destruct Hset_valid as
    (Hset_typemeta_valid & Hset_rv_valid & Hset_meta_valid &
      Hset_spec_valid & Hset_status_valid).
  assert (StatefulSetV.valid set) as Hset_valid.
  { split_and!; done. }
  destruct Hmatch as [Hpods_match Hpvcs_match].
  pose proof (pods_match_members set pods Hpods_match) as Hpods_members.
  destruct Hpods_match as (Hpod_keys & Hpods_alive & Hpods_match).
  assert (∀ pod, pod ∈ pods →
      Z.of_nat
        (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max)
    as Hpod_name_len.
  { intros pod Hpod. rewrite Forall_forall in Hpods_valid.
    apply pod_name_length_le_go_int_max_of_valid.
    apply Hpods_valid. by rewrite -list_elem_of_In. }
  pose proof (statefulset_replicas_le_go_int32_max set)
    as Hreplicas_bound.
  wp_apply (wp_endOrdinalOf set_l set dq_set with "[$Hset //]").
  iIntros (end_ordinal) "[%Hend_ordinal Hset]". wp_auto.
  set I := (∃ (ordinal : w64),
    "Hordinal_ptr" ∷ ordinal_ptr ↦ ordinal ∗
    "Hend_ptr" ∷ end_ptr ↦ end_ordinal ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hpods_ptr" ∷ pods_ptr ↦ pods_sl ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
    "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
      PodV.deepown_l ptr pod dq_pods) ∗
    "Hown_pods" ∷ ([∗ list] pod ∈ pods,
      own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq_pod_frag
        pod.(PodV.ObjectMeta') ∗
      own_spec_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq_pod_frag
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
    "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
      own_meta_frag γ (PersistentVolumeClaimV.key pvc)
        pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')
        dq_pvc pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
    "%Hordinal_range" ∷ ⌜ 0 ≤ sint.Z ordinal ∧
      sint.Z ordinal ≤ Z.of_nat (statefulset_replicas set) ⌝)%I.
  iAssert I with
    "[Hset Hpods_sl Hpods Hown_pods Hown_pvcs ordinal end set pods]"
    as "Hloop".
  { iExists (W64 0). iFrame. iPureIntro. split; word. }
  wp_for "Hloop". wp_if_destruct.
  - match goal with
    | H : (sint.Z ordinal ≤ sint.Z end_ordinal)%Z |- _ =>
        rename H into Hordinal_end
    end.
    assert (0 ≤ sint.Z ordinal) as Hordinal_nonnegative.
    { exact (proj1 Hordinal_range). }
    assert ((sint.nat ordinal < statefulset_replicas set)%nat)
      as Hordinal_lt.
    { eapply reconcile_loop_ordinal_lt; done. }
    assert ((sint.nat ordinal ≤ go_int32_max_nat)%nat)
      as Hordinal_int32.
    { eapply reconcile_loop_ordinal_int32; done. }
    wp_apply (wp_findPodByOrdinal set_l pods_sl set ptrs pods ordinal
      dq_set dq_pods with "[$Hset $Hpods_sl $Hpods]").
    { iPureIntro. split_and!.
      - exact Hordinal_nonnegative.
      - exact Hordinal_int32.
      - exact Hpod_name_len.
      - eapply Forall_impl; last exact Hpods_members.
        intros pod Hmember. exact (proj2 Hmember). }
    iIntros (pod_l) "(Hset & Hpods_sl & Hpods & %Hfind)".
    destruct (find_pod_by_ordinal
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      (sint.nat ordinal) pods) as [[pod_idx local_pod]|]
      eqn:Hfind_pod.
    + simpl in Hfind.
      apply list_find_Some in Hfind_pod as
        (Hlocal_lookup & Hlocal_name & Hlocal_first).
      assert (PodV.valid local_pod) as Hlocal_valid.
      { rewrite Forall_forall in Hpods_valid. apply Hpods_valid.
        rewrite -list_elem_of_In.
        by apply list_elem_of_lookup_2 in Hlocal_lookup. }
      assert (is_pod_alive local_pod) as Hlocal_alive.
      { rewrite Forall_forall in Hpods_alive. apply Hpods_alive.
        rewrite -list_elem_of_In.
        by apply list_elem_of_lookup_2 in Hlocal_lookup. }
      assert (pod_match set local_pod) as Hlocal_match.
      { rewrite Forall_forall in Hpods_match. apply Hpods_match.
        rewrite -list_elem_of_In.
        by apply list_elem_of_lookup_2 in Hlocal_lookup. }
      iDestruct (big_sepL2_lookup_acc with "Hpods") as
        "[Hlocal_pod Hlocal_pod_restore]";
        [exact Hfind|exact Hlocal_lookup|].
      iPoseProof (PodV.deepown_l_split with "Hlocal_pod") as
        "(%Hpod_l_not_null & Hlocal_typemeta & Hlocal_meta &
          Hlocal_spec & Hlocal_status)".
      iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
        with "[$Hlocal_typemeta $Hlocal_meta $Hlocal_spec
          $Hlocal_status]") as "Hlocal_pod".
      wp_auto. wp_if_destruct; first contradiction.
      wp_apply (wp_isTerminating pod_l local_pod dq_pods
        with "Hlocal_pod").
      iIntros (terminating) "[%Hterminating Hlocal_pod]".
      destruct terminating.
      { exfalso. apply (proj1 Hterminating eq_refl). exact Hlocal_alive. }
      wp_auto.
      wp_apply (wp_createPersistentVolumeClaims_stability
        γ model_l set_l pod_l set local_pod (sint.nat ordinal)
        pvcs dq_set dq_pods dq_pvc
        with "[$Hset $Hlocal_pod $Hown_pvcs]").
      { iFrame "#". iPureIntro. split_and!; try done.
        apply Hpod_name_len.
        by apply list_elem_of_lookup_2 in Hlocal_lookup. }
      iIntros "(Hset & Hlocal_pod & Hown_pvcs)". wp_auto.
      wp_apply (wp_updateStatefulPod_stability
        set_l pod_l set local_pod dq_set dq_pods
        with "[$Hpkg $Hset $Hlocal_pod]").
      { iPureIntro. split.
        - apply Hpod_name_len.
          by apply list_elem_of_lookup_2 in Hlocal_lookup.
        - exact (proj1 Hlocal_match). }
      iIntros "(Hset & Hlocal_pod)".
      iSpecialize ("Hlocal_pod_restore" with "Hlocal_pod").
      iRename "Hlocal_pod_restore" into "Hpods".
      pose proof (reconcile_loop_ordinal_next ordinal
        (statefulset_replicas set) Hordinal_nonnegative Hordinal_lt
        Hreplicas_bound) as
        (Hnext_nonnegative & Hnext_upper & Hnext_nat).
      wp_auto. iApply wp_for_post_do. wp_auto. iFrame "HΦ".
      iExists (word.add ordinal (W64 1)). iFrame.
      iPureIntro. split; done.
    + simpl in Hfind. subst pod_l.
      exfalso.
      assert (desired_pod_key set (sint.nat ordinal) ∈
          PodV.key <$> pods) as Hdesired_present.
      { rewrite Hpod_keys. unfold desired_pod_keys.
        apply list_elem_of_fmap_2. unfold desired_ordinals.
        apply elem_of_seq. lia. }
      apply list_elem_of_fmap_1 in Hdesired_present as
        (desired_pod & Hdesired_key & Hdesired_in).
      apply list_find_None in Hfind_pod.
      rewrite Forall_forall in Hfind_pod.
      apply (Hfind_pod desired_pod).
      * by rewrite -list_elem_of_In.
      * pose proof (f_equal KKey.Name' Hdesired_key) as Hname.
        simpl in Hname. symmetry. exact Hname.
  - iApply "HΦ". iFrame.
Qed.

Lemma wp_reconcileCondemnedPod_stability set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc) (pods : list PodV.t)
    dq_set dq_pods :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "%Hset_valid" ∷ ⌜ StatefulSetV.valid set ⌝ ∗
      "%Hpods_valid" ∷ ⌜ Forall PodV.valid pods ⌝ ∗
      "%Hpods_match" ∷ ⌜ pods_match set pods ⌝
  }}}
    @! statefulset.reconcileCondemnedPod #set_l #pods_sl
  {{{ RET (#true, #interface.nil);
      StatefulSetV.deepown_l set_l set dq_set ∗
      pods_sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  destruct Hset_valid as (_ & _ & _ & Hset_spec_valid & _).
  pose proof (pods_match_members set pods Hpods_match) as Hmembers.
  pose proof (pods_match_no_condemned set pods Hpods_match)
    as Hno_condemned.
  assert (∀ pod, pod ∈ pods →
      Z.of_nat
        (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max)
    as Hpod_name_len.
  { intros pod Hpod. rewrite Forall_forall in Hpods_valid.
    apply pod_name_length_le_go_int_max_of_valid.
    apply Hpods_valid. by rewrite -list_elem_of_In. }
  wp_apply (wp_firstCondemnedPod set_l pods_sl set ptrs pods
    dq_set dq_pods with "[$Hset $Hpods_sl $Hpods]").
  { iPureIntro. split_and!.
    - exact Hset_spec_valid.
    - exact Hpod_name_len.
    - eapply Forall_impl; last exact Hmembers.
      intros pod Hmember. exact (proj2 Hmember). }
  iIntros (condemned_l) "(Hset & Hpods_sl & Hpods & %Hcondemned)".
  destruct Hcondemned as
    [[Hcondemned_null Hnone]|(idx & pod & Hptr & Hlookup & Hcondemned)].
  - subst condemned_l. wp_auto. iApply "HΦ". iFrame.
  - rewrite Forall_forall in Hno_condemned.
    exfalso. apply (Hno_condemned pod); last exact Hcondemned.
    rewrite -list_elem_of_In. by apply list_elem_of_lookup_2 in Hlookup.
Qed.

Lemma wp_reconcileOutdatedPod_stability set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc) (pods : list PodV.t)
    dq_set dq_pods :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "%Hset_valid" ∷ ⌜ StatefulSetV.valid set ⌝ ∗
      "%Hpods_valid" ∷ ⌜ Forall PodV.valid pods ⌝ ∗
      "%Hpods_match" ∷ ⌜ pods_match set pods ⌝
  }}}
    @! statefulset.reconcileOutdatedPod #set_l #pods_sl
  {{{ RET #interface.nil;
      StatefulSetV.deepown_l set_l set dq_set ∗
      pods_sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  destruct Hset_valid as (_ & _ & _ & Hset_spec_valid & _).
  pose proof (pods_match_members set pods Hpods_match) as Hmembers.
  pose proof (pods_match_no_outdated set pods Hpods_match)
    as Hno_outdated.
  assert (Forall (λ pod,
      Z.of_nat
        (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max)
      pods) as Hpod_name_len.
  { eapply Forall_impl; last exact Hpods_valid.
    intros pod Hvalid.
    by apply pod_name_length_le_go_int_max_of_valid. }
  assert (NoDup (PodV.key <$> pods)) as Hkeys_nodup.
  { destruct Hpods_match as (Hkeys & _).
    rewrite Hkeys. apply desired_pod_keys_nodup. }
  pose proof (pod_names_nodup_of_key_nodup
    set pods Hmembers Hkeys_nodup) as Hnames_nodup.
  wp_apply (wp_largestOutdatedPod set_l pods_sl set ptrs pods
    dq_set dq_pods with "[$Hset $Hpods_sl $Hpods]").
  { iPureIntro. split_and!.
    - exact Hset_spec_valid.
    - exact Hpod_name_len.
    - eapply Forall_impl; last exact Hmembers.
      intros pod Hmember. exact (proj2 Hmember).
    - exact Hnames_nodup. }
  iIntros (outdated_l) "(Hset & Hpods_sl & Hpods & %Houtdated)".
  destruct Houtdated as
    [[Houtdated_null Hnone]|(idx & pod & Hptr & Hlookup & Houtdated)].
  - subst outdated_l. wp_auto. iApply "HΦ". iFrame.
  - rewrite Forall_forall in Hno_outdated.
    exfalso. apply (Hno_outdated pod); last exact Houtdated.
    rewrite -list_elem_of_In. by apply list_elem_of_lookup_2 in Hlookup.
Qed.

Lemma wp_reconcileReplicas_stability γ model_l set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc)
    (pods : list PodV.t) (pvcs : list PersistentVolumeClaimV.t)
    dq_set dq_pods dq_pod_frag dq_pvc dq_children :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_pods" ∷ ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq_pod_frag
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq_pod_frag
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_pvcs" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')
          dq_pvc pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq_children
        (list_to_set (PodV.key <$> pods)) ∗
      "%Hset_valid" ∷ ⌜ StatefulSetV.valid set ⌝ ∗
      "%Hpods_valid" ∷ ⌜ Forall PodV.valid pods ⌝ ∗
      "%Hmatch" ∷ ⌜ current_state_matches set pods pvcs ⌝
  }}}
    @! statefulset.reconcileReplicas #set_l #pods_sl
  {{{ RET #interface.nil;
      StatefulSetV.deepown_l set_l set dq_set ∗
      pods_sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq_pod_frag
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq_pod_frag
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc)
          pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')
          dq_pvc pvc.(PersistentVolumeClaimV.ObjectMeta')) ∗
      own_children_frag γ (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq_children
        (list_to_set (PodV.key <$> pods))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  destruct Hmatch as [Hpods_match Hpvcs_match].
  assert (current_state_matches set pods pvcs) as Hmatch.
  { split; done. }
  wp_apply (wp_reconcileDesiredPods_stability
    γ model_l set_l pods_sl set ptrs pods pvcs
    dq_set dq_pods dq_pod_frag dq_pvc
    with "[$Hset $Hpods_sl $Hpods $Hown_pods $Hown_pvcs]").
  { iFrame "# %". }
  iIntros
    "(Hset & Hpods_sl & Hpods & Hown_pods & Hown_pvcs)".
  wp_auto.
  wp_apply (wp_reconcileCondemnedPod_stability
    set_l pods_sl set ptrs pods dq_set dq_pods
    with "[$Hset $Hpods_sl $Hpods]").
  { iFrame "%". }
  iIntros "(Hset & Hpods_sl & Hpods)". wp_auto.
  wp_apply (wp_reconcileOutdatedPod_stability
    set_l pods_sl set ptrs pods dq_set dq_pods
    with "[$Hset $Hpods_sl $Hpods]").
  { iFrame "%". }
  iIntros "(Hset & Hpods_sl & Hpods)". wp_auto.
  iApply "HΦ". iFrame.
Qed.

End proof.
