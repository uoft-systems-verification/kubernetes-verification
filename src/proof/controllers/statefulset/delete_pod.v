From New.proof.controllers.statefulset Require Export pod_predicates.
From New.proof.controllers.statefulset Require Export ordinal.
From New.proof.kubernetes_model Require Export delete_reserved.

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

(* StatefulSet Pod names are reserved.  Deletion consumes the occupied
   reservation and returns it in the deleting state. *)
Lemma wp_deletePod γ model_l pod_l
    (local_pod stored_pod : PodV.t)
    parent_key parent_uid (children : gset KKey.t) phase dq_pod :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hpod" ∷ PodV.deepown_l pod_l local_pod dq_pod ∗
      "%Hkey" ∷ ⌜ PodV.key local_pod = PodV.key stored_pod ⌝ ∗
      "%Huid" ∷ ⌜
        local_pod.(PodV.ObjectMeta').(ObjectMetaV.UID') =
          stored_pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "%Hkey_in" ∷ ⌜ PodV.key stored_pod ∈ children ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ (PodV.key stored_pod)
        stored_pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        stored_pod.(PodV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (PodV.key stored_pod)
        stored_pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.PodSpec stored_pod.(PodV.Spec')) ∗
      "Hreservation" ∷ own_occupied_reserved_frag γ (PodV.key stored_pod)
        stored_pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ∗
      "Hown_children" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ parent_key parent_uid phase
  }}}
    @! statefulset.deletePod #pod_l
  {{{ RET #interface.nil;
      "Hpod" ∷ PodV.deepown_l pod_l local_pod dq_pod ∗
      "Hreservation" ∷ own_deleting_reserved_frag γ (PodV.key stored_pod)
        stored_pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ∗
      "Hown_children" ∷ own_children_frag γ parent_key parent_uid 1
        (children ∖ {[PodV.key stored_pod]}) ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ parent_key parent_uid Mutable
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l &
      Hpod_spec_l & Hpod_status_l)".
  wp_apply (v1.wp_GetUID_deepown with "[$Hpod_objectmeta_l]").
  iIntros "Hpod_objectmeta_l".
  wp_auto.
  iDestruct "Hpod_objectmeta_l" as
    (pod_meta_c) "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  wp_auto.
  rewrite Hpod_meta_Hdeepown_namespace Hpod_meta_Hdeepown_name.
  wp_apply (common.wp_NewDeleteOptionsWithUID).
  iIntros (options_c) "[Hoptions %Hvalid_options]".
  wp_auto.
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  wp_apply (wp_State__PodDelete_reserved γ model_l
    (PodV.key stored_pod)
    local_pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace')
    local_pod.(PodV.ObjectMeta').(ObjectMetaV.Name')
    options_c
    (delete_options_with_uid
      local_pod.(PodV.ObjectMeta').(ObjectMetaV.UID'))
    stored_pod.(PodV.ObjectMeta').(ObjectMetaV.UID')
    stored_pod.(PodV.ObjectMeta') (ObjectSpecV.PodSpec stored_pod.(PodV.Spec'))
    parent_key parent_uid children phase
    with "[Hoptions Hown_meta Hown_spec Hreservation Hown_children
      Hown_terminating_children_frag]").
  { iFrame "#".
    iSplitL "Hoptions"; [iExact "Hoptions"|].
    iSplit; [iPureIntro; exact Hvalid_options|].
    iSplit.
    { iPureIntro. rewrite -Hkey /PodV.key /PodV.meta_key /=. done. }
    iSplit; [iPureIntro; exact Hkey_in|].
    iSplit.
    { iPureIntro.
      rewrite /delete_preconditions_match /delete_options_with_uid /=.
      split; [exact Huid|done]. }
    iSplit.
    { iPureIntro.
      rewrite /delete_options_preconditions_resource_version_none
        /delete_options_with_uid /=.
      done. }
    iFrame. }
  iIntros "Hdelete".
  iNamed "Hdelete".
  wp_auto.
  iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta".
  iAssert (ObjectMetaV.deepown pod_meta_c
      local_pod.(PodV.ObjectMeta') dq_pod)
    with "[Hpod_objectmeta]" as "Hpod_objectmeta".
  { iNamed "Hpod_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
      local_pod.(PodV.ObjectMeta') dq_pod)
    with "[Hpod_objectmeta_field Hpod_objectmeta]" as
      "Hpod_objectmeta_l".
  { iExists pod_meta_c. iFrame. }
  iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
    with "[$Hpod_typemeta $Hpod_objectmeta_l
      $Hpod_spec_l $Hpod_status_l]") as "Hpod".
  iApply "HΦ".
  iFrame.
Qed.

End proof.
