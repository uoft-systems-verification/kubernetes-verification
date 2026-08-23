From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.replicaset Require Export replicaset_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.kubernetes_model Require Export list_weak.

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

Lemma wp_getReplicaSetsWithSameController γ model_l rs_l rs dq :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hrs" ∷ ReplicaSetV.deepown_l rs_l rs dq
  }}}
    @! replicaset.getReplicaSetsWithSameController #rs_l
  {{{ sl ptrs replica_sets dq', RET (#sl, #interface.nil);
      sl ↦* ptrs ∗
      ([∗ list] ptr;replica_set ∈ ptrs;replica_sets, ReplicaSetV.deepown_l ptr replica_set dq') ∗
      ⌜ Forall ReplicaSetV.valid replica_sets ⌝ ∗
      ReplicaSetV.deepown_l rs_l rs dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iAssert (is_pkg_init v1) as "#Hmeta_init".
  { iPkgInit. }
  iAssert (is_pkg_init labels) as "#Hlabels_init".
  { iPkgInit. }
  iAssert (is_pkg_init apimodel) as "#Hapimodel_init".
  { iPkgInit. }
  wp_auto.
  wp_bind (@! v1.GetControllerOf
    #(interface.mk_ok (go.PointerType api_apps_v1.ReplicaSet) #rs_l))%E.
  wp_apply (wp_GetControllerOf_ReplicaSet with
    "[$Hmeta_init $Hrs //]").
  iIntros (controller_ref_l) "(Hrs & Hcontroller_ref)".
  iDestruct "Hcontroller_ref" as
    "[%Hcontroller_ref_null|Hcontroller_ref]".
  - subst controller_ref_l. wp_auto.
    iApply ("HΦ" $! slice.nil [] [] (DfracOwn 1)).
    iPoseProof (own_slice_nil (V:=loc) (DfracOwn 1)) as "Hnil".
    simpl. iFrame "Hnil Hrs". done.
  - iDestruct "Hcontroller_ref" as (controller_ref)
      "(%Hcontroller_ref & Hcontroller_ref)".
    destruct Hcontroller_ref as
      [Hcontroller_ref_nonnull Hcontroller_ref_of].
    wp_auto.
    rewrite -> bool_decide_false by exact Hcontroller_ref_nonnull.
    wp_auto.
    iDestruct "Hcontroller_ref" as (controller_ref_c)
      "[Hcontroller_ref_l Hcontroller_ref]".
    iDestruct (struct_fields_split (V:=v1.OwnerReference.t) with
      "Hcontroller_ref_l") as
      "[Hcontroller_ref_fields %Hcontroller_ref_l_nonnull]".
    iNamedPrefix "Hcontroller_ref_fields" "Hcontroller_ref_field_".
    iNamedPrefix "Hcontroller_ref" "Hcontroller_ref_deepown_".
    iRename "controllerRef" into "Hcontroller_var".
    iRename "Hcontroller_ref_field_UID" into "Hcontroller_uid".
    iCombineNamed "Hcontroller_ref_*" as "Hcontroller_rest".
    iPoseProof (ReplicaSetV.deepown_l_split with "Hrs") as
      "(%Hrs_l_nonnull & Hrs_typemeta & Hrs_meta_l & Hrs_spec & Hrs_status)".
    iDestruct "Hrs_meta_l" as (rs_meta_c) "[Hrs_meta_l Hrs_meta]".
    iDestruct (struct_fields_split (V:=v1.ObjectMeta.t) with
      "Hrs_meta_l") as "[Hrs_meta_fields %Hrs_meta_l_nonnull]".
    iNamedPrefix "Hrs_meta_fields" "Hrs_meta_field_".
    iNamedPrefix "Hrs_meta" "Hrs_meta_deepown_".
    wp_auto.
    rewrite Hrs_meta_deepown_Hdeepown_namespace.
    wp_bind (@! labels.Everything #())%E.
    wp_apply (wp_Everything with "[$Hlabels_init]").
    iIntros (selector) "#Hselector". wp_auto.
    wp_apply (wp_State__ReplicaSetList_weak γ model_l
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') selector
      everything_matches with "[$Hapimodel_init $Hselector $Hisk]").
    iIntros (replica_sets_sl replica_set_ptrs replica_sets)
      "(Hreplica_sets_sl & Hreplica_sets & %Hreplica_sets_valid)".
    wp_auto.
    iCombineNamed "Hrs_meta_field_*" as "Hrs_meta_fields".
    iAssert (typed_pointsto_def (ReplicaSetV.objectmeta_ptr rs_l)
        rs_meta_c dq) with "[Hrs_meta_fields]" as "Hrs_meta_l".
    { iNamed "Hrs_meta_fields". simpl. rewrite /named.
      rewrite Hrs_meta_deepown_Hdeepown_namespace. iFrame. }
    iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
      (ReplicaSetV.objectmeta_ptr rs_l) rs_meta_c dq
      Hrs_meta_l_nonnull with "Hrs_meta_l") as "Hrs_meta_l".
    iCombineNamed "Hrs_meta_deepown_*" as "Hrs_meta_deepown".
    iAssert (ObjectMetaV.deepown rs_meta_c
        rs.(ReplicaSetV.ObjectMeta') dq)
      with "[Hrs_meta_deepown]" as "Hrs_meta".
    { iNamed "Hrs_meta_deepown". rewrite /ObjectMetaV.deepown /named.
      iFrame. iFrame "%". }
    iAssert (ObjectMetaV.deepown_l (ReplicaSetV.objectmeta_ptr rs_l)
        rs.(ReplicaSetV.ObjectMeta') dq) with
      "[Hrs_meta_l Hrs_meta]" as "Hrs_meta_l".
    { iExists rs_meta_c. iFrame. }
    iPoseProof (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_nonnull with
      "[$Hrs_typemeta $Hrs_meta_l $Hrs_spec $Hrs_status]") as "Hrs".
    iDestruct (own_slice_len with "Hreplica_sets_sl") as
      %(Hreplica_sets_len1 & Hreplica_sets_len2).
    iDestruct (big_sepL2_length with "Hreplica_sets") as
      %Hreplica_sets_len.
    iDestruct (own_slice_wf with "Hreplica_sets_sl") as
      %Hreplica_sets_cap.
    wp_apply (wp_slice_make3 (V:=loc)
      (t:=go.PointerType api_apps_v1.ReplicaSet)); first word.
    iIntros (related_sl) "(Hrelated_sl & Hrelated_cap & %Hrelated_cap_eq)".
    wp_auto.
    set I := (∃ (i : w64) (related_rs_l : loc) (result_sl : slice.t)
        (result_ptrs : list loc) (result_replica_sets : list ReplicaSetV.t),
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hrelated_rs_ptr" ∷ relatedRS_ptr ↦ related_rs_l ∗
      "Hresult_ptr" ∷ relatedReplicaSets_ptr ↦ result_sl ∗
      "Hresult_sl" ∷ result_sl ↦* result_ptrs ∗
      "Hresult_replica_sets" ∷
        ([∗ list] ptr;replica_set ∈ result_ptrs;result_replica_sets,
          ReplicaSetV.deepown_l ptr replica_set 1) ∗
      "Hreplica_sets_post" ∷
        ([∗ list] ptr;replica_set ∈
          drop (sint.nat i) replica_set_ptrs;
          drop (sint.nat i) replica_sets,
          ReplicaSetV.deepown_l ptr replica_set 1) ∗
      "Hrelated_cap" ∷ own_slice_cap loc result_sl (DfracOwn 1) ∗
      "%Hresult_valid" ∷ ⌜ Forall ReplicaSetV.valid result_replica_sets ⌝ ∗
      "%Hi_bound" ∷
        ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len replica_sets_sl) ⌝)%I.
    iAssert I with
      "[i relatedRS relatedReplicaSets Hrelated_sl Hrelated_cap
        Hreplica_sets]" as "Hloop".
    { iExists (W64 0), null, related_sl, [], [].
      iFrame. rewrite !big_sepL2_nil. iFrame.
      iPureIntro. split; [done|]. split; [constructor|word]. }
    wp_for "Hloop". wp_if_destruct.
    + list_elem replica_set_ptrs (sint.Z i) as this_ptr.
      destruct (decide
        (0 ≤ sint.Z i < sint.Z (slice.len replica_sets_sl))) as
        [_|Hbounds]; last word.
      wp_apply (wp_load_slice_index with "[$Hreplica_sets_sl]");
        [word|iPureIntro; exact Hthis_ptr_lookup|].
      iIntros "Hreplica_sets_sl". wp_auto.
      assert (∃ this_rs, replica_sets !! sint.nat i = Some this_rs) as
        [this_rs Hthis_rs_lookup].
      { apply lookup_lt_is_Some_2.
        rewrite -Hreplica_sets_len Hreplica_sets_len1. word. }
      assert (ReplicaSetV.valid this_rs) as Hthis_valid.
      { rewrite Forall_forall in Hreplica_sets_valid.
        apply Hreplica_sets_valid.
        rewrite <-list_elem_of_In.
        apply list_elem_of_lookup_2 with (i:=sint.nat i).
        exact Hthis_rs_lookup. }
      iPoseProof (big_sepL2_head_tail _ _ _ this_ptr this_rs with
        "Hreplica_sets_post") as "[Hthis Hother]".
      { split. all: rewrite lookup_drop Nat.add_0_r; done. }
      wp_bind (@! v1.GetControllerOf
        #(interface.mk_ok (go.PointerType api_apps_v1.ReplicaSet)
          #this_ptr))%E.
      wp_apply (wp_GetControllerOf_ReplicaSet with
        "[$Hmeta_init $Hthis //]").
      iIntros (related_controller_ref_l)
        "(Hthis & Hrelated_controller_ref)".
      iDestruct "Hrelated_controller_ref" as
        "[%Hrelated_controller_ref_null|Hrelated_controller_ref]".
      * subst related_controller_ref_l. wp_auto.
        iApply wp_for_post_do. wp_auto.
        iFrame "Hreplica_sets_sl HΦ Hrs Hcontroller_var Hcontroller_uid
          Hcontroller_rest".
        iExists (word.add i (W64 1)), this_ptr, result_sl,
          result_ptrs, result_replica_sets.
        assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as
          -> by word.
        rewrite !drop_drop Nat.add_1_r. iFrame. iPureIntro.
        split; [done|word].
      * iDestruct "Hrelated_controller_ref" as (related_controller_ref)
          "(%Hrelated_controller_ref & Hrelated_controller_ref)".
        destruct Hrelated_controller_ref as
          [Hrelated_controller_ref_nonnull Hrelated_controller_ref_of].
        wp_auto.
        rewrite -> bool_decide_false by
          exact Hrelated_controller_ref_nonnull.
        wp_auto.
        iDestruct "Hrelated_controller_ref" as
          (related_controller_ref_c)
          "[Hrelated_controller_ref_l Hrelated_controller_ref]".
        iDestruct (struct_fields_split (V:=v1.OwnerReference.t) with
          "Hrelated_controller_ref_l") as
          "[Hrelated_controller_ref_fields %Hrelated_controller_ref_l_nonnull]".
        iNamedPrefix "Hrelated_controller_ref_fields"
          "Hrelated_controller_ref_field_".
        iNamedPrefix "Hrelated_controller_ref"
          "Hrelated_controller_ref_deepown_".
        wp_auto.
        rewrite Hrelated_controller_ref_deepown_Hdeepown_uid
          Hcontroller_ref_deepown_Hdeepown_uid.
        wp_if_destruct.
        -- wp_apply wp_slice_literal. iSplitR; first done.
           iIntros (one_sl) "[Hone_sl _]". wp_auto.
           wp_apply (wp_slice_append with
             "[$Hresult_sl $Hrelated_cap $Hone_sl]").
           iIntros (result_sl')
             "(Hresult_sl & Hrelated_cap & Hone_sl)". wp_auto.
           iAssert (([∗ list] ptr;replica_set ∈
               result_ptrs ++ [this_ptr];
               result_replica_sets ++ [this_rs],
               ReplicaSetV.deepown_l ptr replica_set 1))%I
             with "[Hresult_replica_sets Hthis]" as
             "Hresult_replica_sets".
           { iApply (big_sepL2_app with "[$Hresult_replica_sets]").
             simpl. iFrame. }
           iApply wp_for_post_do. wp_auto.
           iFrame "Hreplica_sets_sl HΦ Hrs Hcontroller_var Hcontroller_uid
             Hcontroller_rest".
           iExists (word.add i (W64 1)), this_ptr, result_sl',
             (result_ptrs ++ [this_ptr]),
             (result_replica_sets ++ [this_rs]).
           assert (sint.nat (word.add i (W64 1)) = S (sint.nat i))
             as -> by word.
           rewrite !drop_drop Nat.add_1_r.
           iFrame. iPureIntro. split.
           ++ rewrite Forall_app. split; [done|]. constructor; done.
           ++ word.
        -- iApply wp_for_post_do. wp_auto.
           iFrame "Hreplica_sets_sl HΦ Hrs Hcontroller_var Hcontroller_uid
             Hcontroller_rest".
           iExists (word.add i (W64 1)), this_ptr, result_sl,
             result_ptrs, result_replica_sets.
           assert (sint.nat (word.add i (W64 1)) = S (sint.nat i))
             as -> by word.
           rewrite !drop_drop Nat.add_1_r. iFrame. iPureIntro.
           split; [done|word].
    + clear I.
      iApply ("HΦ" $! result_sl result_ptrs result_replica_sets
        (DfracOwn 1)).
      iFrame. done.
Qed.

End proof.
