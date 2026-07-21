From New.proof Require Import prelude empty_ffi.
From New.proof.string Require Export prefix_suffix.
From New.proof.kubernetes_model Require Export get index create delete.
From New.proof Require Export util.
From New.proof.controllers Require Export common.
From New.proof.controllers.statefulset Require Export progress.
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

Lemma wp_syncStatefulSet_stability γ l namespace name sts dq pods pvcs :
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hown_sts_meta_frag" ∷ own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq sts.(StatefulSetV.ObjectMeta') ∗
      "Hown_sts_spec_frag" ∷ own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      "Hown_pod_frags" ∷ ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_pvc_frags" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') dq pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
        own_spec_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.PersistentVolumeClaimSpec pvc.(PersistentVolumeClaimV.Spec'))) ∗
      "Hown_children_frag" ∷ own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq (list_to_set (PodV.key <$> pods)) ∗
	    "%Hnamespace_eq" ∷ ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
	    "%Hname_eq" ∷ ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
	    "%Hdeletion_timestamp_eq" ∷ ⌜ sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
	    "%Hmatch" ∷ ⌜ current_state_matches sts pods pvcs ⌝ ∗
	    "%Hpods_no_dup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
	    "%Hpvcs_no_dup" ∷ ⌜ NoDup (PersistentVolumeClaimV.key <$> pvcs) ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ (err : interface.t), RET #err;
      own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq sts.(StatefulSetV.ObjectMeta') ∗
      own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') dq pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
        own_spec_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.PersistentVolumeClaimSpec pvc.(PersistentVolumeClaimV.Spec'))) ∗
      own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq (list_to_set (PodV.key <$> pods))
  }}}.
Proof.
Admitted.

End proof.
