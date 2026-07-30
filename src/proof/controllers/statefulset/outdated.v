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

Lemma wp_withoutStatefulSetFields
    (spec_c : v1.PodSpec.t) (spec : PodSpecV.t) dq :
  {{{ PodSpecV.deepown spec_c spec dq }}}
    @! statefulset.withoutStatefulSetFields #spec_c
  {{{ result_c, RET #result_c;
      PodSpecV.deepown spec_c spec dq ∗
      PodSpecV.deepown result_c (without_statefulset_fields spec) dq
  }}}.
Proof.
  wp_start as "Hspec".
  iNamed "Hspec".
  wp_auto.
  iApply "HΦ".
  iSplitL "Hdeepown_volumes".
  - rewrite /PodSpecV.deepown. iFrame. done.
  - rewrite /PodSpecV.deepown /without_statefulset_fields /=.
    iSplitL.
    + iExists []. rewrite /deepown_list big_sepL2_nil.
      iSplit; [iApply own_slice_nil|done].
    + done.
Qed.

Lemma wp_podSpecMatches set_l pod_l
    (set : StatefulSetV.t) (pod : PodV.t) dq_set dq_pod :
  {{{ StatefulSetV.deepown_l set_l set dq_set ∗
      PodV.deepown_l pod_l pod dq_pod
  }}}
    @! statefulset.podSpecMatches #set_l #pod_l
  {{{ (ret : bool), RET #ret;
      ⌜ ret = true ↔ pod_immutable_matches set pod ⌝ ∗
      StatefulSetV.deepown_l set_l set dq_set ∗
      PodV.deepown_l pod_l pod dq_pod
  }}}.
Proof. Admitted.

Lemma wp_largestOutdatedPod set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc) (pods : list PodV.t)
    dq_set dq_pods :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "%Hspec_valid" ∷ ⌜ StatefulSetSpecV.valid set.(StatefulSetV.Spec') ⌝ ∗
      "%Hpod_name_len" ∷ ⌜ Forall (λ pod,
        Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤
          go_int_max) pods ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall (λ pod,
        pod_has_int32_member_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) pods ⌝ ∗
      "%Hpod_names_nodup" ∷ ⌜ NoDup
        ((λ pod, pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <$> pods) ⌝
  }}}
    @! statefulset.largestOutdatedPod #set_l #pods_sl
  {{{ outdated_l, RET #outdated_l;
      StatefulSetV.deepown_l set_l set dq_set ∗
      pods_sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      ⌜ (outdated_l = null ∧
          Forall (λ pod, ¬ pod_is_outdated set pod) pods) ∨
        (∃ idx pod,
          ptrs !! idx = Some outdated_l ∧
          pods !! idx = Some pod ∧
          pod_is_outdated set pod) ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  assert (∀ pod, pod ∈ pods →
      Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤
        go_int_max) as Hpod_name_len_lookup.
  { rewrite Forall_forall in Hpod_name_len.
    intros pod' Hpod'. apply Hpod_name_len.
    by rewrite -list_elem_of_In. }
  wp_auto.
  wp_apply (wp_endOrdinalOf with "[$Hset //]").
  iIntros (end_ordinal) "[%Hend_ordinal Hset]".
  wp_auto.
  pose proof (StatefulSetSpecV.valid_replicas _ Hspec_valid) as
    (replicas32 & Hreplicas & Hreplicas_nonnegative).
  assert ((statefulset_replicas set ≤ go_int32_max_nat)%nat) as
    Hreplicas_bound.
  { rewrite /statefulset_replicas Hreplicas /go_int32_max_nat.
    apply Z2Nat.inj_le.
    - exact Hreplicas_nonnegative.
    - unfold go_int32_max.
      assert (0 < (2 : Z) ^ 31) by
        (apply Z.pow_pos_nonneg; lia).
      lia.
    - unfold go_int32_max.
      pose proof (word.signed_range replicas32).
      lia. }
  set I := (∃ (i : w64),
    "Hi_ptr" ∷ ordinal_ptr ↦ i ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
      PodV.deepown_l ptr pod dq_pods) ∗
    "%Hi_upper" ∷ ⌜ sint.Z i ≤
      Z.of_nat (statefulset_replicas set) - 1 ⌝ ∗
    "%Hremaining" ∷ ⌜ ∀ pod ordinal,
      pod ∈ pods →
      (ordinal ≤ go_int32_max_nat)%nat →
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
        desired_pod_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal →
      (ordinal < statefulset_replicas set)%nat →
      ¬ pod_immutable_matches set pod →
      Z.of_nat ordinal ≤ sint.Z i ⌝
  )%I.
  iAssert I with "[ordinal set Hset Hpods]" as "Hloop_inv".
  { iExists end_ordinal. iFrame.
    iPureIntro. split; [lia|].
    intros pod' ordinal' Hpod' _ _ Hordinal' _.
    lia. }
  wp_for "Hloop_inv". wp_if_destruct.
  - assert (0 ≤ sint.Z i) as Hi_nonnegative by word.
    assert ((sint.nat i ≤ statefulset_replicas set)%nat) as
      Hi_replicas_bound.
    { rewrite -(Nat2Z.id (statefulset_replicas set)).
      apply (proj1 (Z2Nat.inj_le
        (sint.Z i) (Z.of_nat (statefulset_replicas set))
        Hi_nonnegative ltac:(lia))).
      lia. }
    assert ((sint.nat i ≤ go_int32_max_nat)%nat) as
      Hi_int32_bound by lia.
    wp_apply (wp_findPodByOrdinal with
      "[$Hset $Hpods_sl $Hpods]").
    { iPureIntro. split.
      - split.
        + exact Hi_nonnegative.
        + exact Hi_int32_bound.
      - split; [exact Hpod_name_len_lookup|exact Hpods_members]. }
    iIntros (found_l) "(Hset & Hpods_sl & Hpods & %Hfound)".
    wp_auto.
    destruct (find_pod_by_ordinal
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      (sint.nat i) pods) as [[found_idx found_pod]|] eqn:Hfind.
    + apply list_find_Some in Hfind as
        (Hfound_pod_lookup & Hfound_name & _).
      iDestruct (big_sepL2_lookup_acc with "Hpods") as
        "[Hfound_pod Hpods_restore]";
        [exact Hfound|exact Hfound_pod_lookup|].
      iPoseProof (PodV.deepown_l_split with "Hfound_pod") as
        "(%Hfound_l_not_null & Hfound_typemeta & Hfound_objectmeta & Hfound_spec & Hfound_status)".
      iPoseProof (PodV.deepown_l_restore _ _ _ Hfound_l_not_null with
        "[$Hfound_typemeta $Hfound_objectmeta $Hfound_spec $Hfound_status]")
        as "Hfound_pod".
      replace (bool_decide (found_l = null)) with false by
        (symmetry; apply bool_decide_eq_false_2; done).
      wp_auto.
      wp_apply (wp_podSpecMatches with "[$Hset $Hfound_pod]").
      iIntros (matches) "(%Hmatches & Hset & Hfound_pod)".
      iSpecialize ("Hpods_restore" with "Hfound_pod").
      iRename "Hpods_restore" into "Hpods".
      destruct matches.
      * wp_auto.
        replace (bool_decide true) with true by done.
        iApply wp_for_post_do. wp_auto.
        iFrame "pods Hpods_sl HΦ".
        iExists (word.sub i (W64 1)).
        iFrame.
        iPureIntro. split; [word|].
        intros pod' ordinal' Hpod' Hordinal_bound Hpod_name
          Hordinal_range Hnot_matches.
        specialize (Hremaining pod' ordinal' Hpod' Hordinal_bound
          Hpod_name Hordinal_range Hnot_matches).
        destruct (decide (Z.of_nat ordinal' = sint.Z i)) as
          [Hordinal_eq|Hordinal_ne].
        -- assert (ordinal' = sint.nat i) as ->.
           { apply Nat2Z.inj. rewrite Hordinal_eq. word. }
           assert (∃ pod_idx, pods !! pod_idx = Some pod') as
             [pod_idx Hpod_lookup].
           { apply list_elem_of_lookup_1. exact Hpod'. }
           assert (pod_idx = found_idx) as ->.
	           { apply (NoDup_lookup
               ((λ pod,
                 pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <$> pods)
               pod_idx found_idx
               (desired_pod_name
                 set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
                 (sint.nat i)) Hpod_names_nodup).
             - rewrite list_lookup_fmap Hpod_lookup /=.
               f_equal. exact Hpod_name.
	             - rewrite list_lookup_fmap Hfound_pod_lookup /=.
	               f_equal. exact Hfound_name. }
	           rewrite Hfound_pod_lookup in Hpod_lookup. simplify_eq/=.
	           exfalso. apply Hnot_matches. apply Hmatches. done.
	        -- word.
      * wp_auto.
        replace (bool_decide false) with false by done.
        iApply wp_for_post_return. wp_auto.
        iApply ("HΦ" $! found_l). iFrame.
        iPureIntro. right.
        exists found_idx, found_pod. repeat split; try done.
        exists (sint.nat i). split.
        -- exact Hi_int32_bound.
        -- split; [exact Hfound_name|].
           split.
           ++ replace (Z.of_nat (sint.nat i)) with (sint.Z i) by word.
              lia.
           ++ intros Himmutable.
              pose proof (proj2 Hmatches Himmutable).
              done.
    + subst found_l.
      wp_auto.
      replace (bool_decide (null = null)) with true by
        (symmetry; apply bool_decide_eq_true_2; done).
      iApply wp_for_post_do. wp_auto.
      iFrame "pods Hpods_sl HΦ".
      iExists (word.sub i (W64 1)).
      iFrame.
      iPureIntro. split; [word|].
      intros pod' ordinal' Hpod' Hordinal_bound Hpod_name
        Hordinal_range Hnot_matches.
      specialize (Hremaining pod' ordinal' Hpod' Hordinal_bound
        Hpod_name Hordinal_range Hnot_matches).
      destruct (decide (Z.of_nat ordinal' = sint.Z i)) as
        [Hordinal_eq|Hordinal_ne].
      * assert (ordinal' = sint.nat i) as ->.
        { apply Nat2Z.inj. rewrite Hordinal_eq. word. }
        apply list_find_None in Hfind.
        rewrite Forall_forall in Hfind.
        exfalso. apply (Hfind pod').
        { by rewrite -list_elem_of_In. }
        exact Hpod_name.
      * word.
  - iApply ("HΦ" $! null). iFrame.
    iPureIntro. left. split; [done|].
    apply Forall_forall. intros pod' Hpod' Houtdated.
    destruct Houtdated as
      (ordinal' & Hordinal_bound & Hpod_name &
        Hordinal_range & Hnot_matches).
    rewrite -list_elem_of_In in Hpod'.
    specialize (Hremaining pod' ordinal' Hpod' Hordinal_bound
      Hpod_name Hordinal_range Hnot_matches).
    word.
Qed.

End proof.
