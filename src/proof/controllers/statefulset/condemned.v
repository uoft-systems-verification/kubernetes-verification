From New.proof.controllers.statefulset Require Export pod_predicates.
From New.proof.controllers.statefulset Require Export ordinal.

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

Lemma wp_firstCondemnedPod set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc) (pods : list PodV.t)
    dq_set dq_pods :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "%Hspec_valid" ∷ ⌜ StatefulSetSpecV.valid set.(StatefulSetV.Spec') ⌝ ∗
      "%Hpod_name_len" ∷ ⌜ ∀ pod, pod ∈ pods →
        Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤
          go_int_max ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall (λ pod,
        pod_has_int32_member_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) pods ⌝
  }}}
    @! statefulset.firstCondemnedPod #set_l #pods_sl
  {{{ condemned_l, RET #condemned_l;
      StatefulSetV.deepown_l set_l set dq_set ∗
      pods_sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      ⌜ (condemned_l = null ∧
          Forall (λ pod, ¬ pod_is_condemned set pod) pods) ∨
        (∃ idx pod,
          ptrs !! idx = Some condemned_l ∧
          pods !! idx = Some pod ∧
          pod_is_condemned set pod) ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  iDestruct (own_slice_len with "Hpods_sl") as
    %(Hpods_sl_len1 & Hpods_sl_len2).
  iDestruct (own_slice_wf with "Hpods_sl") as %Hpods_sl_cap.
  iDestruct (big_sepL2_length with "Hpods") as %Hptrs_pods_len.
  set C := pod_is_condemned set.
  set I := (∃ (i : w64) (pod_ptr_value condemned_l : loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Hpod_ptr" ∷ pod_ptr ↦ pod_ptr_value ∗
    "Hcondemned_ptr" ∷ condemned_ptr ↦ condemned_l ∗
    "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
      PodV.deepown_l ptr pod dq_pods) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len pods_sl) ⌝ ∗
    "%Hselected" ∷ ⌜
      (condemned_l = null ∧
        Forall (λ pod, ¬ C pod) (take (sint.nat i) pods)) ∨
      (∃ idx pod,
        ptrs !! idx = Some condemned_l ∧
        pods !! idx = Some pod ∧ C pod) ⌝
  )%I.
  iAssert I with "[i set Hset pod condemned Hpods]" as "Hloop_inv".
  { iExists (W64 0), null, null. iFrame.
    iPureIntro. split; [word|].
    left. split; [done|]. rewrite take_0. constructor. }
  wp_for "Hloop_inv". wp_if_destruct.
  - list_elem ptrs (sint.Z i) as this_ptr.
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len pods_sl)))
      as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hpods_sl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hpods_sl". wp_auto.
    assert (∃ this_pod, pods !! sint.nat i = Some this_pod) as
      [this_pod Hthis_pod_lookup].
    { apply lookup_lt_is_Some_2.
      rewrite -Hptrs_pods_len Hpods_sl_len1. word. }
    assert (pod_has_int32_member_name
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        this_pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) as Hthis_member.
    { rewrite Forall_forall in Hpods_members.
      apply Hpods_members.
      rewrite -list_elem_of_In.
      eapply list_elem_of_lookup_2. exact Hthis_pod_lookup. }
    destruct Hthis_member as
      (this_ordinal & Hthis_ordinal_bound & Hthis_name).
    iDestruct (big_sepL2_lookup_acc with "Hpods") as
      "[Hthis Hpods_restore]";
      [exact Hthis_ptr_lookup|exact Hthis_pod_lookup|].
    iPoseProof (PodV.deepown_l_split with "Hthis") as
      "(%Hthis_not_null & Hthis_typemeta & Hthis_objectmeta_l & Hthis_spec_l & Hthis_status_l)".
    iDestruct "Hthis_objectmeta_l" as
      (this_meta_c) "[Hthis_objectmeta_field Hthis_objectmeta]".
    iNamedPrefix "Hthis_objectmeta" "Hthis_meta_".
    wp_auto.
    rewrite Hthis_meta_Hdeepown_name.
    wp_apply (wp_ordinalOf
      this_pod.(PodV.ObjectMeta').(ObjectMetaV.Name') this_ordinal
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') with "[]").
    { iPureIntro. split.
      - apply Hpod_name_len.
        by apply list_elem_of_lookup_2 in Hthis_pod_lookup.
      - split; done. }
    iIntros (ordinal) "%Hordinal".
    wp_auto.
    replace (bool_decide (sint.Z ordinal < sint.Z (W64 0))) with false by
      (symmetry; apply bool_decide_eq_false_2; rewrite Hordinal; word).
    wp_auto.
    rewrite Hthis_meta_Hdeepown_name.
    wp_apply (wp_podInOrdinalRange set_l set
      this_pod.(PodV.ObjectMeta').(ObjectMetaV.Name') this_ordinal
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') dq_set
      with "[$Hset]").
    { iPureIntro. split; [exact Hspec_valid|].
      split.
      - apply Hpod_name_len.
        by apply list_elem_of_lookup_2 in Hthis_pod_lookup.
      - split; done. }
    iIntros (in_range) "[%Hin_range Hset]".
    iCombineNamed "Hthis_meta_*" as "Hthis_objectmeta".
    iAssert (ObjectMetaV.deepown this_meta_c
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta]" as "Hthis_objectmeta".
    { iNamed "Hthis_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr this_ptr)
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta_field Hthis_objectmeta]" as
        "Hthis_objectmeta_l".
    { iExists this_meta_c. iFrame. }
    iPoseProof (PodV.deepown_l_restore _ _ _ Hthis_not_null
      with "[$Hthis_typemeta $Hthis_objectmeta_l $Hthis_spec_l $Hthis_status_l]")
      as "Hthis".
    iSpecialize ("Hpods_restore" with "Hthis").
    iRename "Hpods_restore" into "Hpods".
    destruct in_range eqn:Hin_range_value.
    + wp_auto.
      assert (¬ C this_pod) as Hthis_not_condemned.
      { intros (other_ordinal & _ & Hother_name & Hother_condemned).
        assert (other_ordinal = this_ordinal) as ->.
        { apply (desired_pod_name_inj
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')).
          rewrite -Hother_name. exact Hthis_name. }
        pose proof (proj1 Hin_range eq_refl). lia. }
      iApply wp_for_post_continue. wp_auto.
      iFrame "Hpods_sl HΦ".
      iExists (word.add i (W64 1)), this_ptr, condemned_l.
      iFrame.
      iPureIntro. split; [word|].
      destruct Hselected as [[Hnull Hnone]|Hsome].
      * left. split; [exact Hnull|].
        assert (sint.nat (word.add i (W64 1)) = S (sint.nat i))
          as -> by word.
        rewrite (take_S_r _ _ this_pod).
        -- exact Hthis_pod_lookup.
        -- apply Forall_app. split; [exact Hnone|].
           constructor; [exact Hthis_not_condemned|constructor].
      * right. exact Hsome.
    + wp_auto.
      assert (C this_pod) as Hthis_condemned.
      { exists this_ordinal. split; [exact Hthis_ordinal_bound|].
        split; [exact Hthis_name|].
        assert (¬ (this_ordinal < statefulset_replicas set)%nat).
        { intros Hlt.
          pose proof (proj2 Hin_range Hlt) as Htrue.
          congruence. }
        lia. }
      destruct Hselected as [[Hnull Hnone]|Hsome].
      * subst condemned_l. wp_auto.
        replace (bool_decide (null = null)) with true by
          (symmetry; apply bool_decide_eq_true_2; done).
        iApply wp_for_post_do. wp_auto.
        iFrame "Hpods_sl HΦ".
        iExists (word.add i (W64 1)), this_ptr, this_ptr.
        iFrame.
        iPureIntro. split; [word|].
        right. exists (sint.nat i), this_pod. repeat split; done.
      * destruct Hsome as
          (selected_idx & selected_pod & Hselected_ptr_lookup &
            Hselected_pod_lookup & Hselected_condemned).
        iDestruct (big_sepL2_lookup_acc with "Hpods") as
          "[Hselected Hpods_restore]";
          [exact Hselected_ptr_lookup|exact Hselected_pod_lookup|].
        iPoseProof (PodV.deepown_l_split with "Hselected") as
          "(%Hselected_not_null & Hselected_typemeta & Hselected_objectmeta_l & Hselected_spec_l & Hselected_status_l)".
        iDestruct "Hselected_objectmeta_l" as
          (selected_meta_c) "[Hselected_objectmeta_field Hselected_objectmeta]".
        iNamedPrefix "Hselected_objectmeta" "Hselected_meta_".
        assert (pod_has_int32_member_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            selected_pod.(PodV.ObjectMeta').(ObjectMetaV.Name'))
          as Hselected_member.
        { rewrite Forall_forall in Hpods_members.
          apply Hpods_members.
          rewrite -list_elem_of_In.
          eapply list_elem_of_lookup_2. exact Hselected_pod_lookup. }
        destruct Hselected_member as
          (selected_ordinal & Hselected_ordinal_bound & Hselected_name).
        replace (bool_decide (condemned_l = null)) with false by
          (symmetry; apply bool_decide_eq_false_2; exact Hselected_not_null).
        wp_auto.
        rewrite Hselected_meta_Hdeepown_name.
        wp_apply (wp_ordinalOf
          selected_pod.(PodV.ObjectMeta').(ObjectMetaV.Name')
          selected_ordinal
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') with "[]").
        { iPureIntro. split.
          - apply Hpod_name_len.
            by apply list_elem_of_lookup_2 in Hselected_pod_lookup.
          - split; done. }
        iIntros (selected_ordinal_ret) "%Hselected_ordinal_ret".
        iCombineNamed "Hselected_meta_*" as "Hselected_objectmeta".
        iAssert (ObjectMetaV.deepown selected_meta_c
            selected_pod.(PodV.ObjectMeta') dq_pods)
          with "[Hselected_objectmeta]" as "Hselected_objectmeta".
        { iNamed "Hselected_objectmeta". iFrame. done. }
        iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr condemned_l)
            selected_pod.(PodV.ObjectMeta') dq_pods)
          with "[Hselected_objectmeta_field Hselected_objectmeta]" as
            "Hselected_objectmeta_l".
        { iExists selected_meta_c. iFrame. }
        iPoseProof (PodV.deepown_l_restore _ _ _ Hselected_not_null
          with "[$Hselected_typemeta $Hselected_objectmeta_l $Hselected_spec_l $Hselected_status_l]")
          as "Hselected".
        iSpecialize ("Hpods_restore" with "Hselected").
        iRename "Hpods_restore" into "Hpods".
        wp_auto. wp_if_destruct.
        -- iApply wp_for_post_do. wp_auto.
           iFrame "Hpods_sl HΦ".
           iExists (word.add i (W64 1)), this_ptr, this_ptr.
           iFrame.
           iPureIntro. split; [word|].
           right. exists (sint.nat i), this_pod. repeat split; done.
        -- iApply wp_for_post_do. wp_auto.
           iFrame "Hpods_sl HΦ".
           iExists (word.add i (W64 1)), this_ptr, condemned_l.
           iFrame.
           iPureIntro. split; [word|].
           right. exists selected_idx, selected_pod. repeat split; done.
  - assert (take (sint.nat i) pods = pods) as Htake.
    { assert (sint.nat i = length ptrs) as Hi_len.
      { rewrite Hpods_sl_len1. word. }
      rewrite Hptrs_pods_len in Hi_len. rewrite Hi_len.
      apply take_ge. lia. }
    iApply "HΦ". iFrame.
    iPureIntro.
    rewrite Htake in Hselected.
    exact Hselected.
Qed.

End proof.
