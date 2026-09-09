From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.replicaset Require Export replicaset_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.kubernetes_model Require Export by_index_controller_uid.

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
  {{{ sl ptrs replica_sets dq', RET #sl;
      sl ↦* ptrs ∗
      ([∗ list] ptr;replica_set ∈ ptrs;replica_sets, ReplicaSetV.deepown_l ptr replica_set dq') ∗
      ⌜ Forall ReplicaSetV.valid replica_sets ⌝ ∗
      ⌜ Forall ReplicaSetV.extra_valid replica_sets ⌝ ∗
      ReplicaSetV.deepown_l rs_l rs dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iAssert (is_pkg_init v1) as "#Hmeta_init".
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
    wp_auto.
    rewrite Hcontroller_ref_deepown_Hdeepown_uid.
    wp_apply (wp_State__ByIndex_controllerUID γ model_l
      controller_ref.(OwnerReferenceV.UID') with
      "[$Hapimodel_init $Hisk]").
    iIntros (objects_sl interfaces replica_sets)
      "(Hobjects_sl & Hreplica_sets & %Hreplica_sets_valid &
        %Hreplica_sets_extra_valid & %Hcontroller_uid & %Hnodup)".
    wp_auto.
    iDestruct (replica_set_interfaces_to_ptrs with "Hreplica_sets") as
      (replica_set_ptrs) "[%Hinterfaces Hreplica_sets]".
    subst interfaces.
    iDestruct (own_slice_len with "Hobjects_sl") as
      %(Hobjects_len1 & Hobjects_len2).
    rewrite !map_length in Hobjects_len1.
    iDestruct (big_sepL2_length with "Hreplica_sets") as
      %Hptrs_len.
    wp_apply (wp_slice_make3 (V:=loc)
      (t:=go.PointerType api_apps_v1.ReplicaSet)); first word.
    iIntros (related_sl)
      "(Hrelated_sl & Hrelated_cap & %Hrelated_cap_eq)".
    wp_auto.
    set I := (∃ (i : w64) (obj : interface.t) (result_sl : slice.t)
        (result_ptrs : list loc),
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hobj_ptr" ∷ obj_ptr ↦ obj ∗
      "Hresult_ptr" ∷ relatedReplicaSets_ptr ↦ result_sl ∗
      "Hresult_sl" ∷ result_sl ↦* result_ptrs ∗
      "Hrelated_cap" ∷ own_slice_cap loc result_sl (DfracOwn 1) ∗
      "%Hresult_ptrs" ∷
        ⌜ result_ptrs = take (sint.nat i) replica_set_ptrs ⌝ ∗
      "%Hi_bound" ∷
        ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len objects_sl) ⌝)%I.
    iAssert I with
      "[i obj relatedReplicaSets Hrelated_sl Hrelated_cap]" as "Hloop".
    { iExists (W64 0), (zero_val interface.t), related_sl, [].
      iFrame. iPureIntro. split; [done|word]. }
    wp_for "Hloop". wp_if_destruct.
    + destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len objects_sl)))
        as [_|Hbounds]; last word.
      assert (∃ this_ptr, replica_set_ptrs !! sint.nat i = Some this_ptr)
        as [this_ptr Hthis_ptr_lookup].
      { apply lookup_lt_is_Some_2. rewrite Hobjects_len1. word. }
      assert ((interface.ok <$> ((λ ptr, interface.mk
          (go.PointerType v1.ReplicaSet) #ptr) <$> replica_set_ptrs)) !!
          sint.nat i = Some (interface.ok (interface.mk
            (go.PointerType v1.ReplicaSet) #this_ptr)))
        as Hinterface_lookup.
      { rewrite !list_lookup_fmap Hthis_ptr_lookup. done. }
      wp_apply (wp_load_slice_index (V:=interface.t)
        (t:=go.InterfaceType []) objects_sl (sint.Z i)
        (interface.ok <$> ((λ ptr, interface.mk
          (go.PointerType v1.ReplicaSet) #ptr) <$> replica_set_ptrs))
        (DfracOwn 1)
        (interface.ok (interface.mk
          (go.PointerType v1.ReplicaSet) #this_ptr)) with
        "[$Hobjects_sl]"); [word|iPureIntro; exact Hinterface_lookup|].
      iIntros "Hobjects_sl". wp_auto.
      rewrite decide_True;
        [change (go.PointerType api_apps_v1.ReplicaSet) with
          (go.PointerType v1.ReplicaSet); reflexivity|].
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done.
      iIntros "%one_ptr [Hone _]". wp_auto.
      wp_apply (wp_slice_append with
        "[$Hresult_sl $Hrelated_cap $Hone]").
      iIntros (result_sl')
        "(Hresult_sl & Hrelated_cap & Hone)". wp_auto.
      iApply wp_for_post_do. wp_auto.
      iAssert I with
        "[Hi_ptr Hobj_ptr Hresult_ptr Hresult_sl Hrelated_cap]" as
        "Hloop".
      { iExists (word.add i (W64 1)),
          (interface.ok (interface.mk
            (go.PointerType v1.ReplicaSet) #this_ptr)),
          result_sl', (take (sint.nat i) replica_set_ptrs ++ [this_ptr]).
        iFrame.
        iPureIntro. split.
        * assert (sint.nat (word.add i (W64 1)) = S (sint.nat i))
            as -> by word.
          rewrite (take_S_r _ _ this_ptr Hthis_ptr_lookup). done.
        * word. }
      iFrame.
    + clear I.
      assert (sint.nat i = length replica_set_ptrs) as Hi_len.
      { rewrite Hobjects_len1. word. }
      assert (take (sint.nat i) replica_set_ptrs = replica_set_ptrs)
        as Htake by (apply take_ge; lia).
      iApply ("HΦ" $! result_sl replica_set_ptrs replica_sets
        (DfracOwn 1)).
      iEval (rewrite Htake) in "Hresult_sl".
      iFrame. done.
Qed.

End proof.
