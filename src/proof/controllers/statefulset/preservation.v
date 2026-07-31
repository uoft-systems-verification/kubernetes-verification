From New.proof.controllers.statefulset Require Export progress.

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

(* These are precisely the Pods that pass [filterPodsForStatefulSet] and cause
   [reconcileReplicas] to return when it observes their deletion timestamp. *)
Definition pending_pod sts (pod : PodV.t) : Prop :=
  ¬ is_pod_alive pod ∧
  pod_has_int32_member_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name').

Definition pending_pods sts pods : list PodV.t :=
  filter (pending_pod sts) pods.

Definition other_pods sts pods : list PodV.t :=
  filter (λ pod, ¬ pending_pod sts pod) pods.

Definition pending_pods_preserved sts pods pods' : Prop :=
  Forall (λ pod, pod ∈ pending_pods sts pods')
    (pending_pods sts pods).

Lemma wp_syncStatefulSet_preservation γ l namespace name sts dq pending_dq pods pvcs :
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hown_sts_meta_frag" ∷ own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq sts.(StatefulSetV.ObjectMeta') ∗
      "Hown_sts_spec_frag" ∷ own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      "Hown_terminating_pod_frags" ∷
        ([∗ list] pod ∈ pending_pods sts pods,
          own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') pending_dq pod.(PodV.ObjectMeta') ∗
          own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') pending_dq (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_other_pod_frags" ∷
        ([∗ list] pod ∈ other_pods sts pods,
          own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
          own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_pvc_frags" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
        own_spec_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PersistentVolumeClaimSpec pvc.(PersistentVolumeClaimV.Spec'))) ∗
      "Hown_children_frag" ∷ own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods)) ∗
      "Hown_reserved_missing_pod_keys" ∷ ([∗ list] key ∈ missing_pod_keys sts pods, own_reserved_frag γ key) ∗
      "Hown_reserved_missing_pvc_keys" ∷ ([∗ list] key ∈ missing_pvc_keys sts pvcs, own_reserved_frag γ key) ∗
      "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hdeletion_timestamp_eq" ∷ ⌜ sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ (pods' : list PodV.t) (pvcs' : list PersistentVolumeClaimV.t)
      (err : interface.t), RET #err;
      ⌜ match_distance sts pods' pvcs' ≤ match_distance sts pods pvcs ⌝ ∗
      ⌜ pending_pods_preserved sts pods pods' ⌝ ∗
      own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq sts.(StatefulSetV.ObjectMeta') ∗
      own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      ([∗ list] pod ∈ pending_pods sts pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') pending_dq pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') pending_dq (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      ([∗ list] pod ∈ filter (λ pod,
          PodV.key pod ∉ PodV.key <$> pending_pods sts pods) pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      ([∗ list] pvc ∈ pvcs',
        own_meta_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
        own_spec_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PersistentVolumeClaimSpec pvc.(PersistentVolumeClaimV.Spec'))) ∗
      own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods'))
  }}}.
Proof.
Admitted.

End proof.
