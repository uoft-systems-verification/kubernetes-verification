From New.proof.controllers Require Import client_tactics.
From New.proof Require Import wp_keep.
From New.proof.controllers.statefulset Require Export pod_predicates.
From New.proof.controllers.statefulset Require Export ordinal.
From New.proof.kubernetes_model Require Export delete_reserved.


Local Transparent ObjectMetaV.deepown ObjectMetaView.ObjectMetaV.deepown.
Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Context {model_sem : apimodel.Assumptions}.
Context {client_ctx : code.context.context.Context.t} {kube_client : loc}.
Collection W := sem + package_sem + model_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.statefulset.statefulset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.statefulset.statefulset.import_controller_Assumption.
#[local] Instance runtime_sem :
    code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
  controller.import_runtime_Assumption.
#[local] Instance runtime_object_underlying_eq :
    runtime.Object ≤u runtime.Objectⁱᵐᵖˡ.
Proof using package_sem model_sem. apply _. Qed.
#[local] Instance meta_object_underlying_eq :
    meta_v1.Object ≤u meta_v1.Objectⁱᵐᵖˡ.
Proof using package_sem model_sem. apply _. Qed.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  model_sem.
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
Proof using package_sem model_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
#[local] Instance common_sem : common.Assumptions | 0.
Proof using package_sem model_sem.
  constructor; try exact apimodel_sem; try apply _.
Defined.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All - client_ctx - kube_client".

(* StatefulSet Pod names are reserved.  Deletion consumes the occupied
   reservation and returns it in the deleting state. *)
Lemma wp_deletePod γ model_l pod_l
    (local_pod stored_pod : PodV.t)
    parent_key parent_uid (children : gset KKey.t) terminating_bound dq_pod :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "#Hmodel_init" ∷ is_pkg_init apimodel ∗
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
      "Hreservation" ∷ own_occupied_reserved_frag γ 1 (PodV.key stored_pod)
        stored_pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ∗
      "Hown_children" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ parent_key parent_uid terminating_bound
  }}}
    @! statefulset.deletePod #client_ctx #kube_client #pod_l
  {{{ RET #interface.nil;
      "Hpod" ∷ PodV.deepown_l pod_l local_pod dq_pod ∗
      "Hreservation" ∷ own_deleting_reserved_frag γ 1 (PodV.key stored_pod)
        stored_pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ∗
      "Hown_children" ∷ own_children_frag γ parent_key parent_uid 1
        (children ∖ {[PodV.key stored_pod]}) ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ parent_key parent_uid (S terminating_bound)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto_keep.
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l &
      Hpod_spec_l & Hpod_status_l)".
  iDestruct "Hpod_objectmeta_l" as
    (pod_meta_c) "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  wp_auto_keep.
  rewrite Hpod_meta_Hdeepown_namespace Hpod_meta_Hdeepown_name.
  iPoseProof (DeleteOptionsV.deepown_zero (DfracOwn 1)) as "Hoptions".
  assert (DeleteOptionsV.valid DeleteOptionsV.zero) as Hvalid_options by done.
  assert (PodV.key stored_pod = {| KKey.Kind' := "Pod"%go;
      KKey.Namespace' := local_pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace');
      KKey.Name' := local_pod.(PodV.ObjectMeta').(ObjectMetaV.Name') |}) as Hkey_def.
  { rewrite -Hkey /PodV.key /PodV.meta_key /=. done. }
  assert (delete_preconditions_match DeleteOptionsV.zero stored_pod.(PodV.ObjectMeta')) as Hpreconditions.
  { rewrite /delete_preconditions_match /DeleteOptionsV.zero /=. done. }
  assert (delete_options_preconditions_resource_version_none DeleteOptionsV.zero) as Hrv_none.
  { rewrite /delete_options_preconditions_resource_version_none /DeleteOptionsV.zero /=. done. }
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  wp_client_model.
  wp_apply (wp_State__PodDelete_reserved γ model_l
    (PodV.key stored_pod)
    local_pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace')
    local_pod.(PodV.ObjectMeta').(ObjectMetaV.Name')
    (zero_val meta_v1.DeleteOptions.t) DeleteOptionsV.zero
    stored_pod.(PodV.ObjectMeta').(ObjectMetaV.UID')
    stored_pod.(PodV.ObjectMeta') (ObjectSpecV.PodSpec stored_pod.(PodV.Spec'))
    parent_key parent_uid children terminating_bound
    with "[Hoptions Hown_meta Hown_spec Hreservation Hown_children
      Hown_terminating_children_frag]").
  { iNamedPrefix "Hoptions" "Hoptions_". iFrame "% # ∗". }
  iIntros "Hdelete".
  iNamed "Hdelete".
  wp_controller_auto.
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
