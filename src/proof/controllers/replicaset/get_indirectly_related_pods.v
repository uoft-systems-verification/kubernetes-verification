From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.replicaset Require Export get_replica_sets_with_same_controller.
From New.proof.kubernetes_model Require Export inv.

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
Proof. Admitted.

End proof.
