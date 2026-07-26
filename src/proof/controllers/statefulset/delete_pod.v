From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.statefulset Require Export create_pod.
From New.proof.kubernetes_model Require Export delete.

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

(* The Pod is known to exist through its metadata fragment.  Kubernetes may
   implement deletion either by first setting deletionTimestamp or by removing
   the Pod immediately.  In both cases [deletePod] treats the request as
   successful and leaves the caller's local Pod unchanged. *)
Lemma wp_deletePod γ model_l pod_l (pod : PodV.t)
    parent_key parent_uid (children : gset KKey.t) dq_pod :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hkey_in" ∷ ⌜ PodV.key pod ∈ children ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod.(PodV.ObjectMeta') ∗
      "Hown_children" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    @! statefulset.deletePod #pod_l
  {{{ (pod_meta' : ObjectMetaV.t), RET #interface.nil;
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      ( ("%Hdeletion_timestamp" ∷
            ⌜ pod_meta'.(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
          "Hown_meta" ∷ own_meta_frag γ (PodV.key pod)
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod_meta' ∗
          "Hown_children" ∷
            own_children_frag γ parent_key parent_uid 1 children)
        ∨
        ("Hown_tombstone" ∷ own_tombstone_frag γ
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ∗
         "Hown_children" ∷ own_children_frag γ parent_key parent_uid 1
            (children ∖ {[PodV.key pod]})))
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
  wp_apply (wp_State__PodDelete γ model_l
    (PodV.key pod)
    pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace')
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name')
    options_c
    (delete_options_with_uid
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID'))
    pod.(PodV.ObjectMeta').(ObjectMetaV.UID')
    pod.(PodV.ObjectMeta') parent_key parent_uid children
    with "[Hoptions Hown_meta Hown_children]").
  { iFrame "#".
    iSplitL "Hoptions"; [iExact "Hoptions"|].
    iSplit; [iPureIntro; exact Hvalid_options|].
    iSplit.
    { iPureIntro. rewrite /PodV.key /PodV.meta_key /=. done. }
    iSplit; [iPureIntro; exact Hkey_in|].
    iSplit.
    { iPureIntro.
      rewrite /delete_preconditions_match /delete_options_with_uid /=.
      done. }
    iSplit.
    { iPureIntro.
      rewrite /delete_options_preconditions_resource_version_none
        /delete_options_with_uid /=.
      done. }
    iFrame. }
  iIntros (pod_meta') "Hdelete".
  wp_auto.
  iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta".
  iAssert (ObjectMetaV.deepown pod_meta_c
      pod.(PodV.ObjectMeta') dq_pod)
    with "[Hpod_objectmeta]" as "Hpod_objectmeta".
  { iNamed "Hpod_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
      pod.(PodV.ObjectMeta') dq_pod)
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
