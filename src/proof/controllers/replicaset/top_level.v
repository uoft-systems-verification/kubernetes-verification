From New.proof.controllers.replicaset Require Export replicaset_init.

Definition current_state_matches (rs : ReplicaSetV.t) (pods : list PodV.t) : Prop :=
  match rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') with
  | Some replicas => length (filter is_pod_alive pods) = sint.nat replicas
  | None => False
  end.

Definition match_distance (rs : ReplicaSetV.t) (pods : list PodV.t) : nat :=
  match rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') with
  | Some replicas =>
      let actual := length (filter is_pod_alive pods) in
      let desired := sint.nat replicas in
      (* Natural-number subtraction truncates at zero, so exactly one of these
         differences can be positive. Their sum is |actual - desired|. *)
      ((actual - desired) + (desired - actual))%nat
  (* A valid ReplicaSet spec always has [Some replicas]. Keep this unreachable
     branch nonzero so distance zero cannot represent a non-matching state. *)
  | None => 1%nat
  end.

Definition pod_meta_except_resource_version_changed
    (pods pods' : list PodV.t) : Prop :=
  ∃ pod pod',
    pod ∈ pods ∧
    pod' ∈ pods' ∧
    PodV.key pod = PodV.key pod' ∧
    ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta') ≠
      ObjectMetaV.without_resource_version pod'.(PodV.ObjectMeta').

Definition pod_spec_changed (pods pods' : list PodV.t) : Prop :=
  ∃ pod pod',
    pod ∈ pods ∧
    pod' ∈ pods' ∧
    PodV.key pod = PodV.key pod' ∧
    pod.(PodV.Spec') ≠ pod'.(PodV.Spec').

Definition pods_progress_observed (pods pods' : list PodV.t) : Prop :=
  list_to_set (C:=gset KKey.t) (PodV.key <$> pods) ≠
    list_to_set (C:=gset KKey.t) (PodV.key <$> pods') ∨
  pod_meta_except_resource_version_changed pods pods' ∨
  pod_spec_changed pods pods'.

Definition input_requirement (rs : ReplicaSetV.t) : Prop :=
  (* ReplicaSet-generated Pod names append a hyphen and five-character suffix. *)
  length rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58.

Section specs.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.replicaset.replicaset.import_controller_Assumption.
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

Record all_fractions := {
  rs_dq : dfrac;
  pod_dq : dfrac;
  children_dq : dfrac;
}.

Definition mutating_fractions dq : all_fractions :=
  {| rs_dq := dq; pod_dq := 1; children_dq := 1 |}.

Definition stability_fractions dq : all_fractions :=
  {| rs_dq := dq; pod_dq := dq; children_dq := dq |}.

Definition owned_resources γ rs pods fractions (ready : bool) : iProp Σ :=
  "Hown_rs_meta_frag" ∷ own_meta_frag γ (ReplicaSetV.key rs)
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(rs_dq) rs.(ReplicaSetV.ObjectMeta') ∗
  "Hown_rs_spec_frag" ∷ own_spec_frag γ (ReplicaSetV.key rs)
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(rs_dq)
      (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
  "Hown_pod_meta_frags" ∷ ([∗ list] pod ∈ pods,
    own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') fractions.(pod_dq)
      pod.(PodV.ObjectMeta')) ∗
  "#Hown_pod_unreserved_key_frags" ∷
    ([∗ list] pod ∈ pods, own_unreserved_key_frag γ (PodV.key pod)) ∗
  "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs)
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(children_dq) (list_to_set (PodV.key <$> pods)) ∗
  "Hown_terminating_children_frag" ∷
    (if ready then
      own_terminating_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') Quiescent
    else
      ∃ phase, own_terminating_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') phase)%I ∗
  "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝.

(* Progress spec states that the controller either makes progress toward the desired state or has already reached the
  desired state, assuming that the cluster state is *ready* for the controller to make progress.
  Here, ready means none of the controller's children objects (Pods) are terminating. *)
Definition progress_spec γ l namespace name rs dq pods : iProp Σ :=
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hresources" ∷ owned_resources γ rs pods (mutating_fractions dq) true ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement rs ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝
  }}}
    @! replicaset.syncReplicaSet #namespace #name
  {{{ (pods' : list PodV.t), RET #interface.nil;
      owned_resources γ rs pods' (mutating_fractions dq) false ∗
      ⌜ current_state_matches rs pods' ∨
        (pods_progress_observed pods pods' ∧ match_distance rs pods' < match_distance rs pods) ⌝
  }}}.

(* Preservation spec states that the controller does not increase the distance between the current cluster state and its
  desired state (or, does not cancel its previous progress) when the cluster state is *unready* for the controller to
  make progress. Here, unready means the controller has some terminating children objects, so the controller might need
  to wait for termination before making progress. *)
Definition preservation_spec γ l namespace name rs dq pods : iProp Σ :=
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hresources" ∷ owned_resources γ rs pods (mutating_fractions dq) false ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement rs ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝
  }}}
    @! replicaset.syncReplicaSet #namespace #name
  {{{ (pods' : list PodV.t), RET #interface.nil;
      owned_resources γ rs pods' (mutating_fractions dq) false ∗
      ⌜ match_distance rs pods' ≤ match_distance rs pods ⌝
  }}}.

(* Stability spec states that the controller does not modify the cluster state if the state already matches the desired
  state. We use fractional ownerships owned_resources so the controller has no permission to modify the state. *)
Definition stability_spec γ l namespace name rs dq pods : iProp Σ :=
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hresources" ∷ owned_resources γ rs pods (stability_fractions dq) true ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hmatch" ∷ ⌜ current_state_matches rs pods ⌝
  }}}
    @! replicaset.syncReplicaSet #namespace #name
  {{{ (err : interface.t), RET #err;
      owned_resources γ rs pods (stability_fractions dq) true
  }}}.

End specs.
