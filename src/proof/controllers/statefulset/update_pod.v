From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.statefulset Require Export delete_pod.
From New.proof.controllers.statefulset Require Export pod_identity pod_storage.
From New.proof.kubernetes_model.tx Require Export update.

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

(* The value submitted to PodUpdateTx.  Identity is repaired first.  Storage is
   then repaired using the unspecified iteration order of the claim-template
   map. *)
Definition prepare_stateful_pod_update (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) (claim_template_names : list go_string) : PodV.t :=
  let pod :=
    if decide (pod_identity_matches set pod)
    then pod
    else update_identity set pod ordinal in
  if decide (pod_storage_matches set pod)
  then pod
  else update_storage set pod ordinal claim_template_names.

Definition stateful_pod_update_input (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) (update_input : PodV.t) : Prop :=
  ∃ claim_template_names,
    NoDup claim_template_names ∧
    list_to_set (C := gset go_string) claim_template_names =
      list_to_set (pvc_claim_template_names set) ∧
    update_input =
      prepare_stateful_pod_update set pod ordinal claim_template_names.

(* The first disjunct covers the early no-op return.  Otherwise every possible
   map iteration order must produce an input accepted by Kubernetes update
   validation. *)
Definition stateful_pod_update_admissible
    (set : StatefulSetV.t) (pod : PodV.t) (ordinal : nat) : Prop :=
  (pod_identity_matches set pod ∧ pod_storage_matches set pod) ∨
  ∀ update_input,
    stateful_pod_update_input set pod ordinal update_input →
    PodV.valid update_input ∧
    ObjectMetaV.valid_simple_update
      pod.(PodV.ObjectMeta') update_input.(PodV.ObjectMeta') ∧
    ObjectSpecV.valid_update
      (ObjectSpecV.PodSpec pod.(PodV.Spec'))
      (ObjectSpecV.PodSpec update_input.(PodV.Spec')).

Lemma wp_updateStatefulPod γ model_l set_l pod_l
    (set : StatefulSetV.t) (pod : PodV.t) (ordinal : nat)
    dq_set dq_pod :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hpod_valid" ∷ ⌜ PodV.valid pod ⌝ ∗
      "%Hpod_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
            desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              ordinal ⌝ ∗
      "%Hordinal_bound" ∷
        ⌜ (ordinal ≤ go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name_len" ∷
        ⌜ Z.of_nat
            (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤
          go_int_max ⌝ ∗
      "%Hpod_not_deleting" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "%Hupdate_admissible" ∷
        ⌜ stateful_pod_update_admissible set pod ordinal ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod.(PodV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))
  }}}
    @! statefulset.updateStatefulPod #set_l #pod_l
  {{{ (pod' : PodV.t), RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hpod_valid" ∷ ⌜ PodV.valid pod' ⌝ ∗
      "%Hpod_key" ∷ ⌜ PodV.key pod' = PodV.key pod ⌝ ∗
      "%Hpod_uid" ∷
        ⌜ pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') =
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod'.(PodV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ∗
      ( ("%Hnoop" ∷
            ⌜ pod_identity_matches set pod ∧
              pod_storage_matches set pod ∧ pod' = pod ⌝)
        ∨
        (∃ update_input,
          "%Hnot_ready" ∷
            ⌜ ¬ (pod_identity_matches set pod ∧
                  pod_storage_matches set pod) ⌝ ∗
          "%Hupdate_input" ∷
            ⌜ stateful_pod_update_input
                set pod ordinal update_input ⌝ ∗
          "%Hmeta_updated" ∷
            ⌜ ObjectMetaV.updated
                update_input.(PodV.ObjectMeta')
                pod'.(PodV.ObjectMeta') ⌝ ∗
          "%Hspec_updated" ∷
            ⌜ ObjectSpecV.updated
                (ObjectSpecV.PodSpec update_input.(PodV.Spec'))
                (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ⌝))
  }}}.
Proof.
Admitted.

End proof.
