From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.replicaset Require Export get_replica_sets_with_same_controller.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export
  v1_label_selector_as_selector.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.replicaset.replicaset.import_controller_Assumption.
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

Lemma wp_getIndirectlyRelatedPods γ l rs_l rs dq :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "Hisk" ∷ is_kubernetes γ l ∗
      "Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hrs" ∷ ReplicaSetV.deepown_l rs_l rs dq
  }}}
    @! replicaset.getIndirectlyRelatedPods #rs_l
  {{{ sl ptrs pods dq', RET (#sl, #interface.nil);
      sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq') ∗
      ReplicaSetV.deepown_l rs_l rs dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iDestruct "Hisk" as "#Hisk".
  iDestruct "Hglobal_l" as "#Hglobal_l".
  iAssert (is_pkg_init v1) as "#Hmeta_init".
  { iPkgInit. }
  iAssert (is_pkg_init apimodel) as "#Hapimodel_init".
  { iPkgInit. }
  wp_auto.
  wp_apply (wp_getReplicaSetsWithSameController γ l rs_l rs dq with
    "[$Hrs $Hisk $Hglobal_l]").
  iIntros (related_sets_sl related_set_ptrs related_sets related_dq)
    "(Hrelated_sets_sl & Hrelated_sets & %Hrelated_sets_valid &
      %Hrelated_sets_extra_valid & Hrs)".
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done.
  iIntros (result_backing_l) "[Hresult_sl Hresult_cap]". wp_auto.
  wp_apply wp_map_make1 as (seen_l) "Hseen".
  iDestruct (own_slice_len with "Hrelated_sets_sl") as
    %(Hrelated_sets_len1 & Hrelated_sets_len2).
  iDestruct (big_sepL2_length with "Hrelated_sets") as
    %Hrelated_sets_len.
  set I := (∃ (i : w64) (related_rs_l : loc) (result_sl' : slice.t)
      (result_ptrs : list loc) (result_pods : list PodV.t)
      (seen : gmap types.UID.t loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hrelated_rs_ptr" ∷ relatedRS_ptr ↦ related_rs_l ∗
    "Hresult_ptr" ∷ relatedPods_ptr ↦ result_sl' ∗
    "Hseen_ptr" ∷ seen_ptr ↦ seen_l ∗
    "Hresult_sl" ∷ result_sl' ↦* result_ptrs ∗
    "Hresult_cap" ∷ own_slice_cap loc result_sl' (DfracOwn 1) ∗
    "Hresult_pods" ∷
      ([∗ list] ptr;pod ∈ result_ptrs;result_pods,
        PodV.deepown_l ptr pod 1) ∗
    "Hseen" ∷ seen_l ↦$ seen ∗
    "Hrelated_sets" ∷
      ([∗ list] ptr;related_rs ∈ related_set_ptrs;related_sets,
        ReplicaSetV.deepown_l ptr related_rs related_dq) ∗
    "%Hi" ∷
      ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len related_sets_sl) ⌝)%I.
  iAssert I with
    "[i relatedRS relatedPods seen Hresult_sl Hresult_cap Hseen
      Hrelated_sets]" as "Houter".
  { iExists (W64 0), null,
      (slice.mk result_backing_l (W64 0) (W64 0)), [], [], ∅.
    iFrame. rewrite big_sepL2_nil. iFrame. iPureIntro. word. }
  wp_for "Houter". wp_if_destruct.
  - list_elem related_set_ptrs (sint.Z i) as this_rs_l.
    destruct (decide
      (0 ≤ sint.Z i < sint.Z (slice.len related_sets_sl))) as
      [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hrelated_sets_sl]");
      [word|iPureIntro; exact Hthis_rs_l_lookup|].
    iIntros "Hrelated_sets_sl". wp_auto.
    assert (∃ this_rs, related_sets !! sint.nat i = Some this_rs) as
      [this_rs Hthis_rs_lookup].
    { apply lookup_lt_is_Some_2.
      rewrite -Hrelated_sets_len Hrelated_sets_len1. word. }
    assert (ReplicaSetV.valid this_rs) as Hthis_rs_valid.
    { rewrite Forall_forall in Hrelated_sets_valid.
      apply Hrelated_sets_valid.
      rewrite <-list_elem_of_In.
      apply list_elem_of_lookup_2 with (i:=sint.nat i).
      exact Hthis_rs_lookup. }
    assert (ReplicaSetV.extra_valid this_rs) as Hthis_rs_extra_valid.
    { rewrite Forall_forall in Hrelated_sets_extra_valid.
      apply Hrelated_sets_extra_valid.
      rewrite <-list_elem_of_In.
      apply list_elem_of_lookup_2 with (i:=sint.nat i).
      exact Hthis_rs_lookup. }
    iDestruct (big_sepL2_lookup_acc with "Hrelated_sets") as
      "[Hthis_rs Hrestore_related_sets]";
      [exact Hthis_rs_l_lookup|exact Hthis_rs_lookup|].
    destruct Hthis_rs_valid as
      (_ & _ & _ & [(_ & _ &
        (api_selector & Hapi_selector_eq & Hapi_selector_valid & _) & _) _]
        & _).
    iPoseProof (ReplicaSetV.deepown_l_split with "Hthis_rs") as
      "(%Hthis_rs_nonnull & Hthis_rs_type & Hthis_rs_meta_l &
        Hthis_rs_spec & Hthis_rs_status)".
    iDestruct "Hthis_rs_spec" as (this_rs_spec_c)
      "[Hthis_rs_spec_l Hthis_rs_spec]".
    iDestruct (struct_fields_split (V:=v1.ReplicaSetSpec.t) with
      "Hthis_rs_spec_l") as
      "[Hthis_rs_spec_fields %Hthis_rs_spec_nonnull]".
    iNamedPrefix "Hthis_rs_spec_fields" "Hthis_rs_spec_field_".
    iNamedPrefix "Hthis_rs_spec" "Hthis_rs_spec_deepown_".
    iEval (rewrite Hapi_selector_eq) in
      "Hthis_rs_spec_deepown_Hdeepown_selector_some".
    wp_auto.
    wp_apply (wp_LabelSelectorAsSelector with
      "[$Hmeta_init
        $Hthis_rs_spec_deepown_Hdeepown_selector_some]").
    { iSplit.
      - iPureIntro. exact Hapi_selector_valid.
      - iPureIntro. apply Hthis_rs_extra_valid. exact Hapi_selector_eq. }
    iIntros (selector)
      "(Hthis_rs_spec_deepown_Hdeepown_selector_some & #Hselector)".
    iCombineNamed "Hthis_rs_spec_field_*" as "Hthis_rs_spec_fields".
    iAssert (typed_pointsto_def (ReplicaSetV.spec_ptr this_rs_l)
        this_rs_spec_c related_dq) with "[Hthis_rs_spec_fields]" as
      "Hthis_rs_spec_l".
    { iNamed "Hthis_rs_spec_fields". simpl. rewrite /named. iFrame. }
    iDestruct (struct_fields_combine (V:=v1.ReplicaSetSpec.t)
      (ReplicaSetV.spec_ptr this_rs_l) this_rs_spec_c related_dq
      Hthis_rs_spec_nonnull with "Hthis_rs_spec_l") as
      "Hthis_rs_spec_l".
    iAssert (ReplicaSetSpecV.deepown this_rs_spec_c
        this_rs.(ReplicaSetV.Spec') related_dq)
      with "[Hthis_rs_spec_deepown_Hdeepown_replicas_some
        Hthis_rs_spec_deepown_Hdeepown_selector_some
        Hthis_rs_spec_deepown_Hdeepown_template]" as "Hthis_rs_spec".
    { rewrite /ReplicaSetSpecV.deepown /named Hapi_selector_eq.
      iFrame. iFrame "%". iPureIntro.
      rewrite Hapi_selector_eq in
        Hthis_rs_spec_deepown_Hdeepown_selector_none.
      exact Hthis_rs_spec_deepown_Hdeepown_selector_none. }
    iAssert (ReplicaSetSpecV.deepown_l (ReplicaSetV.spec_ptr this_rs_l)
        this_rs.(ReplicaSetV.Spec') related_dq)
      with "[Hthis_rs_spec_l Hthis_rs_spec]" as "Hthis_rs_spec".
    { iExists this_rs_spec_c. iFrame. }
    iDestruct "Hthis_rs_meta_l" as (this_rs_meta_c)
      "[Hthis_rs_meta_l Hthis_rs_meta]".
    iDestruct (struct_fields_split (V:=v1.ObjectMeta.t) with
      "Hthis_rs_meta_l") as
      "[Hthis_rs_meta_fields %Hthis_rs_meta_nonnull]".
    iNamedPrefix "Hthis_rs_meta_fields" "Hthis_rs_meta_field_".
    iNamedPrefix "Hthis_rs_meta" "Hthis_rs_meta_deepown_".
    wp_auto.
    rewrite Hthis_rs_meta_deepown_Hdeepown_namespace.
    wp_apply (wp_State__PodList_weak γ l
      this_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') selector
      (LabelSelectorV.matches api_selector)
      (H:=λ labels : option (gmap go_string go_string),
        LabelSelectorV.matches_dec api_selector labels)
      with "[$Hapimodel_init $Hselector $Hisk]").
    iIntros (pods_sl pod_ptrs pods)
      "(Hpods_sl & Hpods & %Hpods_valid)".
    iCombineNamed "Hthis_rs_meta_field_*" as "Hthis_rs_meta_fields".
    iAssert (typed_pointsto_def (ReplicaSetV.objectmeta_ptr this_rs_l)
        this_rs_meta_c related_dq) with "[Hthis_rs_meta_fields]" as
      "Hthis_rs_meta_l".
    { iNamed "Hthis_rs_meta_fields". simpl. rewrite /named.
      rewrite Hthis_rs_meta_deepown_Hdeepown_namespace. iFrame. }
    iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
      (ReplicaSetV.objectmeta_ptr this_rs_l) this_rs_meta_c related_dq
      Hthis_rs_meta_nonnull with "Hthis_rs_meta_l") as
      "Hthis_rs_meta_l".
    iCombineNamed "Hthis_rs_meta_deepown_*" as
      "Hthis_rs_meta_deepown".
    iAssert (ObjectMetaV.deepown this_rs_meta_c
        this_rs.(ReplicaSetV.ObjectMeta') related_dq)
      with "[Hthis_rs_meta_deepown]" as "Hthis_rs_meta".
    { iNamed "Hthis_rs_meta_deepown".
      rewrite /ObjectMetaV.deepown /named. iFrame. iFrame "%". }
    iAssert (ObjectMetaV.deepown_l
        (ReplicaSetV.objectmeta_ptr this_rs_l)
        this_rs.(ReplicaSetV.ObjectMeta') related_dq)
      with "[Hthis_rs_meta_l Hthis_rs_meta]" as "Hthis_rs_meta_l".
    { iExists this_rs_meta_c. iFrame. }
    iPoseProof (ReplicaSetV.deepown_l_restore _ _ _ Hthis_rs_nonnull with
      "[$Hthis_rs_type $Hthis_rs_meta_l $Hthis_rs_spec
        $Hthis_rs_status]") as "Hthis_rs".
    iPoseProof ("Hrestore_related_sets" with "Hthis_rs") as
      "Hrelated_sets".
    wp_auto.
    iDestruct (own_slice_len with "Hpods_sl") as
      %(Hpods_len1 & Hpods_len2).
    iDestruct (big_sepL2_length with "Hpods") as %Hpods_len.
    wp_alloc j_ptr as "j".
    set J := (∃ (j : w64) (pod_l : loc) (result_sl'' : slice.t)
        (result_ptrs' : list loc) (result_pods' : list PodV.t)
        (seen' : gmap types.UID.t loc),
      "Hj_ptr" ∷ j_ptr ↦ j ∗
      "Hpod_ptr" ∷ pod_ptr ↦ pod_l ∗
      "Hrelated_rs_ptr" ∷ relatedRS_ptr ↦ this_rs_l ∗
      "Hresult_ptr" ∷ relatedPods_ptr ↦ result_sl'' ∗
      "Hseen_ptr" ∷ seen_ptr ↦ seen_l ∗
      "Hresult_sl" ∷ result_sl'' ↦* result_ptrs' ∗
      "Hresult_cap" ∷ own_slice_cap loc result_sl'' (DfracOwn 1) ∗
      "Hresult_pods" ∷
        ([∗ list] ptr;pod ∈ result_ptrs';result_pods',
          PodV.deepown_l ptr pod 1) ∗
      "Hseen" ∷ seen_l ↦$ seen' ∗
      "Hpods_post" ∷
        ([∗ list] ptr;pod ∈ drop (sint.nat j) pod_ptrs;
          drop (sint.nat j) pods, PodV.deepown_l ptr pod 1) ∗
      "Hrelated_sets" ∷
        ([∗ list] ptr;related_rs ∈ related_set_ptrs;related_sets,
          ReplicaSetV.deepown_l ptr related_rs related_dq) ∗
      "%Hj" ∷ ⌜ 0 ≤ sint.Z j ≤ sint.Z (slice.len pods_sl) ⌝)%I.
    iAssert J with
      "[j pod Hrelated_rs_ptr Hresult_ptr Hseen_ptr Hresult_sl
        Hresult_cap Hresult_pods Hseen Hpods Hrelated_sets]" as "Hinner".
    { iExists (W64 0), null, result_sl', result_ptrs, result_pods, seen.
      iFrame. iPureIntro. word. }
    wp_auto.
    wp_for "Hinner". wp_if_destruct.
    + list_elem pod_ptrs (sint.Z j) as this_pod_l.
      destruct (decide
        (0 ≤ sint.Z j < sint.Z (slice.len pods_sl))) as
        [_|Hpod_bounds]; last word.
      wp_apply (wp_load_slice_index with "[$Hpods_sl]");
        [word|iPureIntro; exact Hthis_pod_l_lookup|].
      iIntros "Hpods_sl". wp_auto.
      assert (∃ this_pod, pods !! sint.nat j = Some this_pod) as
        [this_pod Hthis_pod_lookup].
      { apply lookup_lt_is_Some_2.
        rewrite -Hpods_len Hpods_len1. word. }
      iPoseProof (big_sepL2_head_tail _ _ _ this_pod_l this_pod with
        "Hpods_post") as "[Hthis_pod Hother_pods]".
      { split. all: rewrite lookup_drop Nat.add_0_r; done. }
      iPoseProof (PodV.deepown_l_split with "Hthis_pod") as
        "(%Hthis_pod_nonnull & Hthis_pod_type & Hthis_pod_meta_l &
          Hthis_pod_spec & Hthis_pod_status)".
      iDestruct "Hthis_pod_meta_l" as (this_pod_meta_c)
        "[Hthis_pod_meta_l Hthis_pod_meta]".
      iDestruct (struct_fields_split (V:=v1.ObjectMeta.t) with
        "Hthis_pod_meta_l") as
        "[Hthis_pod_meta_fields %Hthis_pod_meta_nonnull]".
      iNamedPrefix "Hthis_pod_meta_fields" "Hthis_pod_meta_field_".
      iNamedPrefix "Hthis_pod_meta" "Hthis_pod_meta_deepown_".
      wp_auto.
      rewrite Hthis_pod_meta_deepown_Hdeepown_uid.
      wp_apply (wp_map_lookup2 types.UID
        (go.PointerType api_apps_v1.ReplicaSet) with "[$Hseen]").
      iIntros "Hseen".
      destruct (seen' !!
        this_pod.(PodV.ObjectMeta').(ObjectMetaV.UID')) as
        [seen_rs_l|] eqn:Hseen_lookup; wp_auto.
      * iCombineNamed "Hthis_pod_meta_field_*" as
          "Hthis_pod_meta_fields".
        iAssert (typed_pointsto_def (PodV.objectmeta_ptr this_pod_l)
            this_pod_meta_c 1) with "[Hthis_pod_meta_fields]" as
          "Hthis_pod_meta_l".
        { iNamed "Hthis_pod_meta_fields". simpl. rewrite /named.
          rewrite Hthis_pod_meta_deepown_Hdeepown_uid. iFrame. }
        iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
          (PodV.objectmeta_ptr this_pod_l) this_pod_meta_c 1
          Hthis_pod_meta_nonnull with "Hthis_pod_meta_l") as
          "Hthis_pod_meta_l".
        iCombineNamed "Hthis_pod_meta_deepown_*" as
          "Hthis_pod_meta_deepown".
        iAssert (ObjectMetaV.deepown this_pod_meta_c
            this_pod.(PodV.ObjectMeta') 1)
          with "[Hthis_pod_meta_deepown]" as "Hthis_pod_meta".
        { iNamed "Hthis_pod_meta_deepown".
          rewrite /ObjectMetaV.deepown /named. iFrame. iFrame "%". }
        iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr this_pod_l)
            this_pod.(PodV.ObjectMeta') 1)
          with "[Hthis_pod_meta_l Hthis_pod_meta]" as
          "Hthis_pod_meta_l".
        { iExists this_pod_meta_c. iFrame. }
        iPoseProof (PodV.deepown_l_restore _ _ _ Hthis_pod_nonnull with
          "[$Hthis_pod_type $Hthis_pod_meta_l $Hthis_pod_spec
            $Hthis_pod_status]") as "Hthis_pod".
        iApply wp_for_post_continue. wp_auto.
        iFrame "Hpods_sl Hrelated_sets_sl HΦ Hrs".
        iFrame "Hi_ptr".
        iExists (word.add j (W64 1)), this_pod_l, result_sl'',
          result_ptrs', result_pods', seen'.
        assert (sint.nat (word.add j (W64 1)) = S (sint.nat j)) as
          -> by word.
        rewrite !drop_drop Nat.add_1_r. iFrame. iPureIntro. word.
      * iCombineNamed "Hthis_pod_meta_field_*" as
          "Hthis_pod_meta_fields".
        iAssert (typed_pointsto_def (PodV.objectmeta_ptr this_pod_l)
            this_pod_meta_c 1) with "[Hthis_pod_meta_fields]" as
          "Hthis_pod_meta_l".
        { iNamed "Hthis_pod_meta_fields". simpl. rewrite /named.
          rewrite Hthis_pod_meta_deepown_Hdeepown_uid. iFrame. }
        iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
          (PodV.objectmeta_ptr this_pod_l) this_pod_meta_c 1
          Hthis_pod_meta_nonnull with "Hthis_pod_meta_l") as
          "Hthis_pod_meta_l".
        iCombineNamed "Hthis_pod_meta_deepown_*" as
          "Hthis_pod_meta_deepown".
        iAssert (ObjectMetaV.deepown this_pod_meta_c
            this_pod.(PodV.ObjectMeta') 1)
          with "[Hthis_pod_meta_deepown]" as "Hthis_pod_meta".
        { iNamed "Hthis_pod_meta_deepown".
          rewrite /ObjectMetaV.deepown /named. iFrame. iFrame "%". }
        iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr this_pod_l)
            this_pod.(PodV.ObjectMeta') 1)
          with "[Hthis_pod_meta_l Hthis_pod_meta]" as
          "Hthis_pod_meta_l".
        { iExists this_pod_meta_c. iFrame. }
        iPoseProof (PodV.deepown_l_restore _ _ _ Hthis_pod_nonnull with
          "[$Hthis_pod_type $Hthis_pod_meta_l $Hthis_pod_spec
            $Hthis_pod_status]") as "Hthis_pod".
        wp_apply (wp_map_insert types.UID with "[$Hseen]") as "Hseen".
        wp_apply wp_slice_literal. iSplitR; first done.
        iIntros (one_sl) "[Hone_sl _]". wp_auto.
        wp_apply (wp_slice_append with
          "[$Hresult_sl $Hresult_cap $Hone_sl]").
        iIntros (result_sl''')
          "(Hresult_sl & Hresult_cap & Hone_sl)". wp_auto.
        iAssert (([∗ list] ptr;pod ∈
            result_ptrs' ++ [this_pod_l];result_pods' ++ [this_pod],
            PodV.deepown_l ptr pod 1))%I
          with "[Hresult_pods Hthis_pod]" as "Hresult_pods".
        { iApply (big_sepL2_app with "[$Hresult_pods]").
          simpl. iFrame. }
        iApply wp_for_post_do. wp_auto.
        iFrame "Hpods_sl Hrelated_sets_sl HΦ Hrs".
        iFrame "Hi_ptr".
        iExists (word.add j (W64 1)), this_pod_l, result_sl''',
          (result_ptrs' ++ [this_pod_l]),
          (result_pods' ++ [this_pod]),
          (<[this_pod.(PodV.ObjectMeta').(ObjectMetaV.UID'):=this_rs_l]>
            seen').
        assert (sint.nat (word.add j (W64 1)) = S (sint.nat j)) as
          -> by word.
        rewrite !drop_drop Nat.add_1_r. iFrame. iPureIntro. word.
    + clear J.
      iApply wp_for_post_do. wp_auto.
      iFrame "Hrelated_sets_sl HΦ Hrs".
      iExists (word.add i (W64 1)), this_rs_l, result_sl'',
        result_ptrs', result_pods', seen'.
      iFrame.
      iPureIntro. word.
  - clear I. wp_auto.
    iApply ("HΦ" $! result_sl' result_ptrs result_pods (DfracOwn 1)).
    iFrame.

Unshelve. all: try tc_solve.
(* [wp_apply] leaves a proof-irrelevant label-map argument unconstrained. *)
all: exact (None : option (gmap go_string go_string)).
Qed.

End proof.
