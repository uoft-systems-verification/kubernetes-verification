From New.proof.controllers.replicaset Require Export replicaset_init.
From New.proof Require Export util.

Module app_listers := code.k8s_io.client_go.listers.apps.v1.v1.

Definition replica_set_lister {ext : ffi_syntax} {go_gctx : GoGlobalContext} : interface.t :=
  interface.mk_ok (go.PointerType app_listers.replicaSetLister) (#null).

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
  (* ReplicaSet-generated Pod names append a hyphen and five-character suffix;
     copied template finalizers must also be valid on the generated Pod. *)
  length rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ∧
  valid_finalizers
    rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') ∧
  (* Status calculation builds a selector from the template labels, whose
     size must fit in a Go int. *)
  Z.of_nat (size (default ∅
    rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')))
    ≤ 2 ^ 63 - 1 ∧
  (* Assumption: the generation is non-negative. updateReplicaSetStatus copies
     it into Status.ObservedGeneration, which status validation
     (ReplicaSetStatusV.valid) requires to be non-negative; otherwise the status
     write fails and the sync returns an error. The API server starts
     generations at 1 and only increments them, but ObjectMetaV.valid
     deliberately does not constrain the generation (see objectmeta.v), so the
     bound is required of the input here. *)
  0 ≤ sint.Z rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Generation').

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

(* The injected clock may read private clock state, but cannot consume or alter
   any of the caller's framed Kubernetes resources. *)
Definition clock_now_spec (rsc_clock : interface.t) : iProp Σ :=
  {{{ True }}}
    (MethodResolve code.k8s_io.utils.clock.clock.PassiveClock "Now" #rsc_clock) #()
  {{{ (now : time.Time.t), RET #now; True }}}.

(* [rs_dq] covers ReplicaSet metadata and spec, which the controller only reads.
   Status is exclusive in both instances because every sync may write it. *)
Record all_fractions := {
  rs_dq : dfrac;
  rs_status_dq : dfrac;
  pod_dq : dfrac;
  children_dq : dfrac;
}.

Definition mutating_fractions dq : all_fractions :=
  {| rs_dq := dq; rs_status_dq := 1; pod_dq := 1; children_dq := 1 |}.

Definition stability_fractions dq : all_fractions :=
  {| rs_dq := dq; rs_status_dq := 1; pod_dq := dq; children_dq := dq |}.

Definition owned_resources γ rs pods fractions (ready : bool) : iProp Σ :=
  "Hown_rs_meta_frag" ∷ own_meta_frag γ (ReplicaSetV.key rs)
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(rs_dq) 
      rs.(ReplicaSetV.ObjectMeta') ∗
  "Hown_rs_spec_frag" ∷ own_spec_frag γ (ReplicaSetV.key rs)
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(rs_dq)
      (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
  "Hown_rs_status_frag" ∷ own_status_frag γ (ReplicaSetV.key rs)
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(rs_status_dq)
      (ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status')) ∗
  "Hown_pod_meta_frags" ∷ ([∗ list] pod ∈ pods, own_meta_frag γ (PodV.key pod) 
    pod.(PodV.ObjectMeta').(ObjectMetaV.UID') fractions.(pod_dq)
      pod.(PodV.ObjectMeta')) ∗
  "#Hown_pod_unreserved_key_frags" ∷
    ([∗ list] pod ∈ pods, own_unreserved_key_frag γ (PodV.key pod)) ∗
  "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs)
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(children_dq) 
      (list_to_set (PodV.key <$> pods)) ∗
  "Hown_terminating_children_frag" ∷
    (if ready then
      own_terminating_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') terminating_children.No
    else
      ∃ has_terminating_children, own_terminating_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') has_terminating_children)%I ∗
  "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝.

(* [burst] is the burst cap (upstream's [burstReplicas]): one sync creates or deletes
  at most [burst] pods. *)
(* Progress spec states that the controller either makes progress toward the desired state or has already reached the
  desired state, assuming that the cluster state is *ready* for the controller to make progress.
  Here, ready means none of the controller's children objects (Pods) are terminating. *)
Definition progress_spec γ l (ctx : context.Context.t) (kube_client : loc) (burst : w64)
    (rsc_clock : interface.t) (controller_features : replicaset.ReplicaSetControllerFeatures.t)
    namespace name rs dq pods
    : iProp Σ :=
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hclock" ∷ clock_now_spec rsc_clock ∗
      "Hresources" ∷ owned_resources γ rs pods (mutating_fractions dq) true ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement rs ⌝ ∗
      (* - > 0: otherwise [manageReplicas] clamps this sync to zero pods, and
           neither disjunct below holds.
         - < 2^31: [burst] bounds the delta [manageReplicas] passes to [wg.Add].
           Perennial packs the WaitGroup counter into the top 32 bits of the state
           word as Go does, so [own_WaitGroup] holds a [w32] and
           [wp_WaitGroup__Add] truncates its [w64] delta to [w32], requiring
           [0 ≤ oldc + delta < 2^31]. Past 2^31 the truncation turns the delta
           negative and that obligation is unprovable. *)
      "%Hburst" ∷ ⌜ 0 < sint.Z burst < 2^31 ⌝ ∗
      (* Assumption: the ReplicaSet owns fewer than 2^31 pods. calculateStatus
         converts the counts of its active and terminating pods (both drawn
         from [pods]) to int32; a count of 2^31 or more wraps to a negative
         value, the status write is rejected, and the sync returns an error.
         Real clusters are far below this bound. *)
      "%Hpods_bound" ∷ ⌜ Z.of_nat (length pods) < 2 ^ 31 ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝
  }}}
    @! replicaset.syncReplicaSet #ctx #kube_client #replica_set_lister #burst
      #rsc_clock #controller_features #namespace #name
  (* The sync succeeds: [manageReplicas] succeeds under these preconditions, and
     the status write fails only for an invalid status (the trusted UpdateStatus
     shim retries resource-version conflicts), which the bounds above rule out. *)
  {{{ (rs' : ReplicaSetV.t) (pods' : list PodV.t), RET #interface.nil;
      owned_resources γ rs' pods' (mutating_fractions dq) false ∗
      ⌜ ReplicaSetV.status_only_changed rs rs' ⌝ ∗
      ⌜ current_state_matches rs pods' ∨
        (pods_progress_observed pods pods' ∧ match_distance rs pods' < match_distance rs pods) ⌝
  }}}.

(* Preservation spec states that the controller does not increase the distance between the current cluster state and its
  desired state (or, does not cancel its previous progress) when the cluster state is *unready* for the controller to
  make progress. Here, unready means the controller has some terminating children objects, so the controller might need
  to wait for termination before making progress. *)
Definition preservation_spec γ l (ctx : context.Context.t) (kube_client : loc) (burst : w64)
    (rsc_clock : interface.t) (controller_features : replicaset.ReplicaSetControllerFeatures.t)
    namespace name rs dq pods
    : iProp Σ :=
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hclock" ∷ clock_now_spec rsc_clock ∗
      "Hresources" ∷ owned_resources γ rs pods (mutating_fractions dq) false ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement rs ⌝ ∗
      "%Hburst" ∷ ⌜ 0 < sint.Z burst < 2^31 ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝
  }}}
    @! replicaset.syncReplicaSet #ctx #kube_client #replica_set_lister #burst
      #rsc_clock #controller_features #namespace #name
  (* Unlike [progress_spec], the sync may return an error. [manageReplicas]
     succeeds, but the status write fails if the computed status is invalid,
     and here that cannot be ruled out: the ReplicaSet may own terminating
     pods, which [owned_resources ... false] does not count, and with 2^31 or
     more of them the terminating-replicas count wraps negative when converted
     to int32. The distance claim below holds either way. *)
  {{{ (rs' : ReplicaSetV.t) (pods' : list PodV.t) (err : interface.t), RET #err;
      owned_resources γ rs' pods' (mutating_fractions dq) false ∗
      ⌜ ReplicaSetV.status_only_changed rs rs' ⌝ ∗
      ⌜ match_distance rs pods' ≤ match_distance rs pods ⌝
  }}}.

(* Stability preserves the represented pod resources and ReplicaSet spec when
   the observed pod count matches the desired count. Status may be updated and
   the sync may return an error. Status correctness is left to helper specs. *)
Definition stability_spec γ l (ctx : context.Context.t) (kube_client : loc) (burst : w64)
    (rsc_clock : interface.t) (controller_features : replicaset.ReplicaSetControllerFeatures.t)
    namespace name rs dq pods
    : iProp Σ :=
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      (* Require input parameter "rsc_clock" satisfies "clock_now_spec" specfication,
      instead of taking "clock_now_spec" as an axiom, which is a stronger requirement
      than the choice we used here. *)
      "#Hclock" ∷ clock_now_spec rsc_clock ∗
      "Hresources" ∷ owned_resources γ rs pods (stability_fractions dq) true ∗
      (* Assumption, as in [input_requirement]: the status calculation builds a
         selector from the template labels, whose count must fit in a Go int. *)
      "%Hlabels_bound" ∷ ⌜ Z.of_nat (size (default ∅
        rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')))
        ≤ 2 ^ 63 - 1 ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hmatch" ∷ ⌜ current_state_matches rs pods ⌝
  }}}
    @! replicaset.syncReplicaSet #ctx #kube_client #replica_set_lister #burst
      #rsc_clock #controller_features #namespace #name
  {{{ (rs' : ReplicaSetV.t) (err : interface.t), RET #err;
      owned_resources γ rs' pods (stability_fractions dq) true ∗
      ⌜ ReplicaSetV.status_only_changed rs rs' ⌝
  }}}.

End specs.
