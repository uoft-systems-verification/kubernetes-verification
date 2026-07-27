From New.proof Require Import prelude empty_ffi.
From New.proof.string Require Export prefix_suffix.
From New.proof.kubernetes_model Require Export get index create delete.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.controllers Require Export common.
From New.proof.controllers.statefulset Require Export ordinal.
From New.proof.controllers.statefulset Require Export pvc.
From New.proof.controllers.statefulset Require Export pod_identity.
From New.proof.controllers.statefulset Require Export pod_storage.
From New.proof.controllers.statefulset Require Export statefulset_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

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

Lemma wp_isTerminating pod_l (pod : PodV.t) dq :
  {{{ PodV.deepown_l pod_l pod dq }}}
    @! statefulset.isTerminating #pod_l
  {{{ (ret : bool), RET #ret;
      ⌜ ret = true ↔ ¬ is_pod_alive pod ⌝ ∗
      PodV.deepown_l pod_l pod dq
  }}}.
Proof.
  wp_start as "Hpod".
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l & Hpod_spec_l & Hpod_status_l)".
  iDestruct "Hpod_objectmeta_l" as (pod_meta_c) "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  wp_auto.
  iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta".
  iAssert (ObjectMetaV.deepown pod_meta_c pod.(PodV.ObjectMeta') dq)
    with "[Hpod_objectmeta]" as "Hpod_objectmeta".
  { iNamed "Hpod_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
      pod.(PodV.ObjectMeta') dq)
    with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l".
  { iExists pod_meta_c. iFrame. }
  iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
    with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]") as "Hpod".
  iApply "HΦ".
  iFrame.
  iPureIntro.
  unfold is_pod_alive.
  split.
  - intros Hnot_null Hdeletion_timestamp_none.
    apply negb_true_iff in Hnot_null.
    apply bool_decide_eq_false in Hnot_null.
    apply Hnot_null.
    by apply Hpod_meta_Hdeepown_deletiontimestamp_none.
  - intros Hnot_alive.
    apply negb_true_iff.
    apply bool_decide_eq_false.
    intros Hnull.
    apply Hnot_alive.
    by apply Hpod_meta_Hdeepown_deletiontimestamp_none.
Qed.

(* The pure result of [newStatefulSetPod].  [controller_ref] is exposed because
   [NewControllerRef] specifies it relationally, and [claim_template_names]
   records the unspecified map-iteration order used by [initStorage]. *)
Definition new_statefulset_pod (set : StatefulSetV.t) (ordinal : nat)
    (controller_ref : OwnerReferenceV.t)
    (claim_template_names : list go_string) : PodV.t :=
  let pod := controller.generated_pod
    set.(StatefulSetV.Spec').(StatefulSetSpecV.Template')
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    (Some [controller_ref]) in
  let pod := PodV.update_objectmeta pod
    (pod.(PodV.ObjectMeta') <| ObjectMetaV.Name' :=
      desired_pod_name set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        ordinal |>) in
  init_storage set (init_identity set pod ordinal) ordinal
    claim_template_names.

Lemma wp_newStatefulSetPod set_l (set : StatefulSetV.t) (ordinal : w64) dq :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq ∗
      "%Hset_meta_valid" ∷ ⌜ ObjectMetaV.valid StatefulSetV.kind set.(StatefulSetV.ObjectMeta') ⌝ ∗
      "%Hordinal_nonnegative" ∷ ⌜ 0 <= sint.Z ordinal ⌝ ∗
      "%Hordinal_int32" ∷ ⌜ (sint.nat ordinal <= go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name_len" ∷
        ⌜ Z.of_nat (length (desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal))) <= go_int_max ⌝
  }}}
    @! statefulset.newStatefulSetPod #set_l #ordinal
  {{{ pod_l controller_ref claim_template_names,
      RET (#pod_l, #interface.nil);
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq ∗
      "Hpod" ∷ PodV.deepown_l pod_l
        (new_statefulset_pod set (sint.nat ordinal) controller_ref
          claim_template_names) 1 ∗
      "%Hcontroller_ref" ∷
        ⌜ OwnerReferenceV.refers_to_controller controller_ref
            StatefulSetV.kind
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "%Hcontroller_ref_valid" ∷ ⌜ OwnerReferenceV.valid controller_ref ⌝ ∗
      "%Hclaim_template_names" ∷
        ⌜ NoDup claim_template_names ∧
          list_to_set (C:=gset go_string) claim_template_names =
            list_to_set (pvc_claim_template_names set) ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_bind ((global_addr apps_v1.SchemeGroupVersion) @!
    (go.PointerType schema.GroupVersion) @! "WithKind" #"StatefulSet"%go)%E.
  iDestruct (is_pkg_init_unfold_deps with "Hpkg") as
    "(_ & _ & _ & _ & _ & #Happs_v1_init & _)".
  wp_apply (New.proof.k8s_io.api.apps.v1.wp_SchemeGroupVersion__WithKind
    (schema_sem := @code.k8s_io.api.apps.v1.v1.import_schema_Assumption
      _ _ _ _ object_apps_v1_sem) "StatefulSet"%go with
    "[$Happs_v1_init]").
  iIntros (gvk) "%Hgvk".
  destruct Hgvk as (Hgvk_group & Hgvk_version & Hgvk_kind).
  wp_auto.
  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
  wp_bind (@! statefulset.meta_v1.NewControllerRef
    #(interface.mk_ok (go.PointerType apps_v1.StatefulSet) (#set_l)) #gvk)%E.
  change (statefulset.meta_v1.NewControllerRef) with meta_v1.NewControllerRef.
  wp_apply (v1.wp_NewControllerRef_StatefulSet with "[Hset_objectmeta_l]").
  { iFrame "# Hset_objectmeta_l".
    iPureIntro.
    rewrite Hgvk_group Hgvk_version Hgvk_kind.
    split; done. }
  iIntros (controller_ref_l controller_ref)
    "(Hcontroller_ref & %Hcontroller_ref_parent &
      %Hcontroller_ref_valid & Hset_objectmeta_l)".
  rewrite Hgvk_kind in Hcontroller_ref_parent.
  wp_auto.
  iDestruct "Hset_spec_l" as (set_spec_c)
    "[Hset_spec_field Hset_spec_deepown]".
  iNamedPrefix "Hset_spec_deepown" "Hset_spec_deepown_".
  iDestruct (struct_fields_split with "Hset_spec_field") as
    "[Hset_spec_fields %Hset_spec_l_not_null]".
  iNamedPrefix "Hset_spec_fields" "Hset_spec_fields_".
  change ((set_l.[apps_v1.StatefulSet.t, "Spec"])
      .[apps_v1.StatefulSetSpec.t, "Template"]) with
    ((StatefulSetV.spec_ptr set_l).[v1.StatefulSetSpec.t, "Template"]).
  assert (Hset_name_valid : valid_dns1123_subdomain
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')).
  { unfold ObjectMetaV.valid in Hset_meta_valid.
    destruct Hset_meta_valid as
      (_ & _ & Hset_name_valid & _).
    unfold valid_name, StatefulSetV.kind in Hset_name_valid.
    destruct Hset_name_valid as
      [[_ Hset_name_valid]|[[Hkind|[Hkind|Hkind]] _]];
      try discriminate.
    unfold valid_dns1123_label in Hset_name_valid.
    destruct Hset_name_valid as [Hsyntax Hlength].
    unfold valid_dns1123_subdomain.
    split; last lia.
    unfold dns1123_label_syntax in Hsyntax.
    unfold dns1123_subdomain_syntax.
    destruct set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') as
      [|first suffix]; first done.
    destruct Hsyntax as [Hfirst Htail].
    split; first exact Hfirst.
    assert (Hnot_dot : ∀ b, dns1123_label_byte b → b ≠ byte_dot).
    { intros b [Halphanumeric|Hdash].
      - destruct Halphanumeric as [Hdigit|Hlower];
          unfold byte_dot, dns1123_lower_alphanumeric in *; word.
      - subst b. unfold byte_dot, byte_dash. word. }
    assert (Htail_subdomain : ∀ previous suffix,
        dns1123_label_byte previous →
        dns1123_label_tail previous suffix →
        dns1123_subdomain_tail previous suffix).
    { intros previous suffix' Hprevious.
      revert previous Hprevious.
      induction suffix' as [|b suffix' IH];
        intros previous Hprevious Hlabel_tail; simpl in *; first done.
      destruct Hlabel_tail as [Hb Hlabel_tail].
      split_and!.
      - left. exact Hb.
      - intros Hprevious_dot. exfalso.
        exact (Hnot_dot previous Hprevious Hprevious_dot).
      - intros Hb_dot. exfalso. exact (Hnot_dot b Hb Hb_dot).
      - exact (IH b Hb Hlabel_tail). }
    apply (Htail_subdomain first suffix); last exact Htail.
    left. exact Hfirst. }
  wp_apply (controller.wp_GetPodFromTemplate
    ((StatefulSetV.spec_ptr set_l).[v1.StatefulSetSpec.t, "Template"])
    (interface.mk (go.PointerType apps_v1.StatefulSet) #set_l)
    controller_ref_l dq dq
    set.(StatefulSetV.Spec').(StatefulSetSpecV.Template') set_l
    (KObjectV.StatefulSet set) (Some controller_ref) with
    "[Hset_spec_fields_Template Hset_spec_deepown_Hdeepown_template
      Hset_objectmeta_l Hcontroller_ref]").
  { iFrame "# Hset_objectmeta_l Hcontroller_ref".
    iSplitL "Hset_spec_fields_Template
      Hset_spec_deepown_Hdeepown_template".
    { iExists set_spec_c.(v1.StatefulSetSpec.Template').
      iFrame. }
    iPureIntro. split; done. }
  iIntros (pod_l) "(Hpod & Htemplate & Hset_objectmeta_l)".
  wp_auto.
  iDestruct "Htemplate" as (template_c)
    "[Hset_spec_fields_Template
      Hset_spec_deepown_Hdeepown_template]".
  set set_spec_c' :=
    set_spec_c <| v1.StatefulSetSpec.Template' := template_c |>.
  iAssert (((StatefulSetV.spec_ptr set_l) ↦{dq} set_spec_c')%I)
    with "[Hset_spec_fields_Replicas Hset_spec_fields_Selector
      Hset_spec_fields_Template Hset_spec_fields_VolumeClaimTemplates
      Hset_spec_fields_ServiceName Hset_spec_fields_PodManagementPolicy
      Hset_spec_fields_UpdateStrategy Hset_spec_fields_RevisionHistoryLimit
      Hset_spec_fields_MinReadySeconds
      Hset_spec_fields_PersistentVolumeClaimRetentionPolicy
      Hset_spec_fields_Ordinals]" as "Hset_spec_field".
  { iApply (struct_fields_combine (V:=v1.StatefulSetSpec.t) _ _ _
      Hset_spec_l_not_null).
    unfold set_spec_c'. simpl. iFrame. }
  iAssert (StatefulSetSpecV.deepown set_spec_c'
      set.(StatefulSetV.Spec') dq)
    with "[Hset_spec_deepown_Hdeepown_replicas_some
      Hset_spec_deepown_Hdeepown_selector_some
      Hset_spec_deepown_Hdeepown_template
      Hset_spec_deepown_Hdeepown_volumeclaimtemplates]" as
      "Hset_spec_deepown".
  { rewrite /StatefulSetSpecV.deepown /set_spec_c'. simpl. iFrame.
    iPureIntro. done. }
  iAssert (StatefulSetSpecV.deepown_l (StatefulSetV.spec_ptr set_l)
      set.(StatefulSetV.Spec') dq)
    with "[Hset_spec_field Hset_spec_deepown]" as "Hset_spec_l".
  { iExists set_spec_c'. iFrame. }
  iDestruct "Hset_objectmeta_l" as (set_meta_c)
    "[Hset_objectmeta_field Hset_objectmeta]".
  iNamedPrefix "Hset_objectmeta" "Hset_meta_".
  set pod := controller.generated_pod
    set.(StatefulSetV.Spec').(StatefulSetSpecV.Template')
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    (Some [controller_ref]).
  iAssert (PodV.deepown_l pod_l pod 1) with "[Hpod]" as "Hpod".
  { unfold pod. iExact "Hpod". }
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l &
      Hpod_spec_l & Hpod_status_l)".
  iDestruct "Hpod_objectmeta_l" as (pod_meta_c)
    "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  wp_auto.
  rewrite Hset_meta_Hdeepown_name.
  wp_apply (wp_podName
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal with "[]").
  { iPureIntro. exact Hordinal_nonnegative. }
  iDestruct (struct_fields_split with "Hpod_objectmeta_field") as
    "[Hpod_meta_fields %Hpod_meta_l_not_null]".
  iNamedPrefix "Hpod_meta_fields" "Hpod_meta_fields_".
  set pod_name := desired_pod_name
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') (sint.nat ordinal).
  set pod_meta := pod.(PodV.ObjectMeta')
    <| ObjectMetaV.Name' := pod_name |>.
  set pod_named := PodV.update_objectmeta pod pod_meta.
  iCombineNamed "Hpod_meta_fields_*" as "Hpod_meta_fields".
  iAssert (((PodV.objectmeta_ptr pod_l) ↦
      (pod_meta_c <| v1.ObjectMeta.Name' := pod_name |>))%I)
    with "[Hpod_meta_fields]" as "Hpod_objectmeta_field".
  { iApply (struct_fields_combine (V:=v1.ObjectMeta.t) _ _ _
      Hpod_meta_l_not_null).
    simpl. iNamed "Hpod_meta_fields". iFrame. }
  iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta".
  iAssert (ObjectMetaV.deepown
      (pod_meta_c <| v1.ObjectMeta.Name' := pod_name |>) pod_meta 1)
    with "[Hpod_objectmeta]" as "Hpod_objectmeta".
  { rewrite /ObjectMetaV.deepown /pod_meta.
    iNamed "Hpod_objectmeta". iFrame. iPureIntro. done. }
  iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l) pod_meta 1)
    with "[Hpod_objectmeta_field Hpod_objectmeta]" as
      "Hpod_objectmeta_l".
  { iExists (pod_meta_c <| v1.ObjectMeta.Name' := pod_name |>).
    iFrame. }
  iPoseProof (PodV.deepown_l_merge pod_l pod pod_meta 1 Hpod_l_not_null
    with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l
      $Hpod_status_l]") as "Hpod".
  iAssert (PodV.deepown_l pod_l pod_named 1) with "[Hpod]" as "Hpod".
  { unfold pod_named. iExact "Hpod". }
  iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
  iAssert (ObjectMetaV.deepown set_meta_c
      set.(StatefulSetV.ObjectMeta') dq)
    with "[Hset_objectmeta]" as "Hset_objectmeta".
  { iNamed "Hset_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
      set.(StatefulSetV.ObjectMeta') dq)
    with "[Hset_objectmeta_field Hset_objectmeta]" as
      "Hset_objectmeta_l".
  { iExists set_meta_c. iFrame. }
  iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
    with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l
      $Hset_status_l]") as "Hset".
  wp_apply (wp_initIdentity set_l pod_l set pod_named
    (sint.nat ordinal) dq with "[$Hset $Hpod]").
  { iSplit.
    { iPureIntro. unfold pod_named, pod_meta, pod_name. done. }
    iSplit; by iPureIntro. }
  iIntros "(Hset & Hpod & %Hidentity_matches)".
  wp_auto.
  assert (Hpod_identity_name :
      (init_identity set pod_named (sint.nat ordinal)).(PodV.ObjectMeta').(ObjectMetaV.Name') =
      desired_pod_name set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        (sint.nat ordinal)).
  { unfold init_identity, update_identity. done. }
  wp_apply (wp_initStorage set_l pod_l set
    (init_identity set pod_named (sint.nat ordinal))
    (sint.nat ordinal) dq with "[$Hset $Hpod]").
  { iSplit; first by iPureIntro.
    iSplit; first by iPureIntro.
    iPureIntro. rewrite Hpod_identity_name. exact Hpod_name_len. }
  iIntros (claim_template_names)
    "(Hset & Hpod & %Hclaim_template_names & %Hstorage_matches)".
  wp_auto.
  iApply ("HΦ" $! pod_l controller_ref claim_template_names).
  iFrame "Hset".
  iSplitL "Hpod".
  { unfold new_statefulset_pod, pod_named, pod_meta, pod_name, pod.
    iExact "Hpod". }
  iSplit; first by iPureIntro.
  iSplit; first by iPureIntro.
  iPureIntro. exact Hclaim_template_names.
Qed.

Lemma wp_filterPodsForStatefulSet set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc) (pods : list PodV.t) dq_set dq_pods :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq_pods) ∗
      "%Hpod_name_len" ∷ ⌜ ∀ pod, pod ∈ pods → Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <= go_int_max ⌝
  }}}
    @! statefulset.filterPodsForStatefulSet #set_l #pods_sl
  {{{ result_sl ptrs', RET #result_sl;
      StatefulSetV.deepown_l set_l set dq_set ∗
      pods_sl ↦* ptrs ∗
      result_sl ↦* ptrs' ∗
      ([∗ list] ptr;pod ∈ ptrs';
        filter (λ pod, pod_has_int32_member_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) pods,
        PodV.deepown_l ptr pod dq_pods)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done.
  iIntros (result_sl0) "[Hresult0 Hown_result_cap]".
  set result0 := {|
    slice.ptr := result_sl0;
    slice.len := W64 (go.array_literal_size []);
    slice.cap := W64 (go.array_literal_size []);
  |}.
  wp_auto.
  iDestruct (own_slice_len with "Hpods_sl") as %(Hpods_sl_len1 & Hpods_sl_len2).
  iDestruct (own_slice_wf with "Hpods_sl") as %Hpods_sl_cap.
  iDestruct (big_sepL2_length with "Hpods") as %Hlen.
  set set_name := set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name').
  set P := (λ pod, pod_has_int32_member_name set_name
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
  set I := (∃ (i: w64) (pod_ptr_value: loc) (result: slice.t) (ptrs': list loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Hpod_ptr" ∷ pod_ptr ↦ pod_ptr_value ∗
    "Hresult_ptr" ∷ result_ptr ↦ result ∗
    "Hresult" ∷ result ↦* ptrs' ∗
    "Hlist_pre" ∷ ([∗ list] ptr;pod ∈ ptrs';filter P (take (sint.nat i) pods),
      PodV.deepown_l ptr pod dq_pods) ∗
    "Hlist_post" ∷ ([∗ list] ptr;pod ∈ (drop (sint.nat i) ptrs);(drop (sint.nat i) pods),
      PodV.deepown_l ptr pod dq_pods) ∗
    "Hown_result_cap" ∷ own_slice_cap loc result (DfracOwn 1) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len pods_sl) ⌝
  )%I.
  iAssert (I) with "[i set Hset pod result Hpods Hresult0 Hown_result_cap]" as "Hloop_inv".
  { iExists (W64 0), (zero_val loc), result0, [].
    rewrite !take_0 !filter_nil !big_sepL2_nil.
    iFrame.
    iPureIntro. word. }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - list_elem ptrs (sint.Z i) as this_ptr.
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len pods_sl))) as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hpods_sl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hpods_sl". wp_auto.
    assert (∃ this_pod, pods !! sint.nat i = Some this_pod) as [this_pod Hthis_pod_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hlen Hpods_sl_len1. word. }
    iPoseProof (big_sepL2_head_tail _ _ _ this_ptr this_pod with "Hlist_post") as "[Hthis Hother]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    iPoseProof (PodV.deepown_l_split with "Hthis") as
      "(%Hthis_not_null & Hthis_typemeta & Hthis_objectmeta_l & Hthis_spec_l & Hthis_status_l)".
    iDestruct "Hthis_objectmeta_l" as (this_meta_c) "[Hthis_objectmeta_field Hthis_objectmeta]".
    iNamedPrefix "Hthis_objectmeta" "Hthis_meta_".
    iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
      "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
    iDestruct "Hset_objectmeta_l" as (set_meta_c) "[Hset_objectmeta_field Hset_objectmeta]".
    iNamedPrefix "Hset_objectmeta" "Hset_meta_".
    wp_auto.
    rewrite Hset_meta_Hdeepown_name Hthis_meta_Hdeepown_name.
    wp_apply (wp_isMemberOf with "[]").
    { iPureIntro.
      apply Hpod_name_len.
      apply list_elem_of_lookup_2 in Hthis_pod_lookup.
      exact Hthis_pod_lookup. }
    iIntros (member) "%Hmember".
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
    iAssert (ObjectMetaV.deepown set_meta_c set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta".
    { iNamed "Hset_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l".
    { iExists set_meta_c. iFrame. }
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]") as "Hset".
    iCombineNamed "Hthis_meta_*" as "Hthis_objectmeta".
    iAssert (ObjectMetaV.deepown this_meta_c this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta]" as "Hthis_objectmeta".
    { iNamed "Hthis_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr this_ptr)
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta_field Hthis_objectmeta]" as "Hthis_objectmeta_l".
    { iExists this_meta_c. iFrame. }
    iPoseProof (PodV.deepown_l_restore _ _ _ Hthis_not_null
      with "[$Hthis_typemeta $Hthis_objectmeta_l $Hthis_spec_l $Hthis_status_l]") as "Hthis".
    wp_if_destruct.
    + wp_apply wp_slice_literal. iSplitR; first done.
      iIntros (sl0) "[Hsl0 _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hresult $Hown_result_cap $Hsl0]").
      iIntros (result') "(Hresult & Hown_result_cap & Hsl0)". wp_auto.
      iApply wp_for_post_do. wp_auto.
      iFrame "Hpods_sl HΦ".
      iExists (word.add i (W64 1)), this_ptr, result', (ptrs' ++ [this_ptr]).
      assert (P this_pod) as Hthis_member.
      { unfold P.
        apply (proj1 Hmember). done. }
      assert (filter P (take (sint.nat i) pods) ++ [this_pod] =
              filter P (take (sint.nat (word.add i (W64 1))) pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pod); [done|].
        rewrite list.filter_app filter_singleton_True; [done|done|done]. }
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite !drop_drop Nat.add_1_r.
      iFrame.
      iSplitR; [done|]. iPureIntro. word.
    + 
      iApply wp_for_post_do. wp_auto.
      iFrame "Hpods_sl HΦ".
      iExists (word.add i (W64 1)), this_ptr, result, ptrs'.
      assert (¬ P this_pod) as Hthis_not_member.
      { unfold P.
        intros Hthis_member.
        pose proof (proj2 Hmember Hthis_member) as Hfalse.
        done. }
      assert (filter P (take (sint.nat i) pods) =
              filter P (take (sint.nat (word.add i (W64 1))) pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pod); [done|].
        rewrite list.filter_app filter_singleton_False; [done|done|rewrite app_nil_r; done]. }
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite !drop_drop Nat.add_1_r.
      iFrame. iPureIntro. word.
  - assert (take (sint.nat i) pods = pods) as ->.
    { assert (sint.nat i = length ptrs) as Hi_len.
      { rewrite Hpods_sl_len1. word. }
      rewrite Hlen in Hi_len. rewrite Hi_len.
      apply take_ge. lia. }
    iApply "HΦ". iFrame.
Qed.

End proof.
