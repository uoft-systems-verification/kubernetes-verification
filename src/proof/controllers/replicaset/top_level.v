From New.proof.controllers.replicaset Require Export replicaset_init.
From New.proof Require Export util.
From New.proof.k8s_io.utils Require Export clock.

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

(* The ReplicaSet's selector matches the labels in [meta]. A valid ReplicaSet
   always has a selector (ReplicaSetSpecV.valid_create). *)
Definition rs_selects_meta (rs : ReplicaSetV.t) (meta : ObjectMetaV.t) : Prop :=
  match rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Selector') with
  | Some selector => LabelSelectorV.matches selector meta.(ObjectMetaV.Labels')
  | None => False
  end.

#[global] Instance rs_selects_meta_dec rs meta : Decision (rs_selects_meta rs meta).
Proof.
  unfold rs_selects_meta.
  destruct rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Selector'); apply _.
Defined.

Definition rs_selects (rs : ReplicaSetV.t) (pod : PodV.t) : Prop :=
  rs_selects_meta rs pod.(PodV.ObjectMeta').

#[global] Instance rs_selects_dec rs pod : Decision (rs_selects rs pod).
Proof. unfold rs_selects. apply _. Defined.

(* [match_distance] after the claim: the sync releases the pods the selector does
   not match and adopts every selected orphan, which becomes an alive pod of the
   ReplicaSet. *)
Definition claim_distance (rs : ReplicaSetV.t) (pods orphan_pods : list PodV.t) : nat :=
  match rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') with
  | Some replicas =>
      let actual := (length (filter (rs_selects rs) (filter is_pod_alive pods)) +
        length (filter (rs_selects rs) orphan_pods))%nat in
      let desired := sint.nat replicas in
      ((actual - desired) + (desired - actual))%nat
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
     (ReplicaSetStatusV.valid_request) requires to be non-negative, and the
     status write is only specified for a valid status. The API server starts
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

(* [rs_dq] covers ReplicaSet metadata and spec, which the controller only reads.
   Status is exclusive in both instances because every sync may write it.
   [orphans_dq] covers the namespace's orphan Pods; adopting one needs 1. *)
Record all_fractions := {
  rs_dq        : dfrac;
  rs_status_dq : dfrac;
  pod_dq       : dfrac;
  children_dq  : dfrac;
  orphans_dq   : dfrac;
}.

Definition mutating_fractions dq : all_fractions :=
  {| rs_dq := dq; rs_status_dq := 1; pod_dq := 1; children_dq := 1; orphans_dq := 1 |}.

Definition stability_fractions dq : all_fractions :=
  {| rs_dq := dq; rs_status_dq := 1; pod_dq := dq; children_dq := dq; orphans_dq := dq |}.

(* [orphan_pods] are the living orphan Pods in the ReplicaSet's namespace. *)
Definition owned_resources γ rs pods orphan_pods fractions (ready : bool) : iProp Σ :=
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
  (* Releasing a pod writes it back with its spec, which needs the spec fragment. *)
  "Hown_pod_spec_frags" ∷ ([∗ list] pod ∈ pods, own_spec_frag γ (PodV.key pod)
    pod.(PodV.ObjectMeta').(ObjectMetaV.UID') fractions.(pod_dq)
      (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
  "#Hown_pod_unreserved_key_frags" ∷
    ([∗ list] pod ∈ pods, own_unreserved_key_frag γ (PodV.key pod)) ∗
  "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs)
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(children_dq) 
      (list_to_set (PodV.key <$> pods)) ∗
  "Hown_terminating_children_frag" ∷
    (if ready then
      own_terminating_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 0%nat
    else
      ∃ terminating_bound, own_terminating_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') terminating_bound)%I ∗
  "%Hpods_nodup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
  (* calculateStatus converts the count of the claimed pods to int32: the pods
     the selector matches and the selected orphans it adopts. With a
     terminating bound of 0 the listing returns exactly [pods]. A sync keeps the
     bound: it releases the other pods, adopts every selected orphan and moves
     the count toward the int32 [spec.replicas]. *)
  "%Hpods_bound" ∷ ⌜ Z.of_nat (length pods + length (filter (rs_selects rs) orphan_pods)) < 2 ^ 31 ⌝ ∗
  (* The namespace's Pod bucket pins the orphans' keys, and their fragments pin
     their metadata and spec. *)
  "Hown_orphan_pod_frags" ∷ ([∗ list] pod ∈ orphan_pods,
    own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') fractions.(orphans_dq)
      pod.(PodV.ObjectMeta') ∗
    own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') fractions.(orphans_dq)
      (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
  (* Selected orphans join [pods] when adopted, so their keys must be unreserved. *)
  "#Hown_orphan_unreserved_key_frags" ∷
    ([∗ list] pod ∈ filter (rs_selects rs) orphan_pods, own_unreserved_key_frag γ (PodV.key pod)) ∗
  "Hown_pod_orphans" ∷ own_orphans_frag γ (PodV.kind, rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace'))
    fractions.(orphans_dq) (list_to_set (PodV.key <$> orphan_pods)) ∗
  "%Horphans_nodup" ∷ ⌜ NoDup (PodV.key <$> orphan_pods) ⌝.

(* [burst] is the burst cap (upstream's [burstReplicas]): one sync creates or deletes
  at most [burst] pods. *)
(* Progress spec states that the controller either makes progress toward the desired state or has already reached the
  desired state, assuming that the cluster state is *ready* for the controller to make progress.
  Here, ready means none of the controller's children objects (Pods) are terminating. *)
Definition progress_spec γ l (ctx : context.Context.t) (kube_client : loc) (burst : w64)
    (rsc_clock : interface.t) (controller_features : upstreamrs.ReplicaSetControllerFeatures.t)
    namespace name rs dq pods orphan_pods
    : iProp Σ :=
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "%Hclock" ∷ ⌜ rsc_clock = real_clock ⌝ ∗
      "Hresources" ∷ owned_resources γ rs pods orphan_pods (mutating_fractions dq) true ∗
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
      "%Hnamespace_eq" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝
  }}}
    @! replicaset.syncReplicaSet #ctx #kube_client #replica_set_lister #burst
      #rsc_clock #controller_features #namespace #name
  (* The sync succeeds: [manageReplicas] succeeds under these preconditions, and
     the computed status is valid under the bounds above, so the status write
     succeeds (the trusted UpdateStatus shim retries resource-version
     conflicts). *)
  (* The sync releases the pods the selector does not match, which become
     orphans [released], adopts every selected orphan and leaves the other
     orphans alone. Adopting is itself observable, even when [manageReplicas]
     then deletes exactly the adopted pods. *)
  {{{ (rs' : ReplicaSetV.t) (pods' released : list PodV.t), RET #interface.nil;
      owned_resources γ rs' pods' (filter (λ pod, ¬ rs_selects rs pod)%type orphan_pods ++ released)
        (mutating_fractions dq) false ∗
      ⌜ PodV.key <$> released ≡ₚ PodV.key <$> filter (λ pod, ¬ rs_selects rs pod) pods ⌝ ∗
      ⌜ Forall (λ pod, meta_parent_ref pod.(PodV.ObjectMeta') = None ∧ ¬ rs_selects rs pod) released ⌝ ∗
      ⌜ current_state_matches rs pods' ∨
        ((pods_progress_observed pods pods' ∨ Exists (rs_selects rs) orphan_pods) ∧
          match_distance rs pods' < claim_distance rs pods orphan_pods) ⌝
  }}}.

(* Preservation spec states that the controller does not increase the distance between the current cluster state and its
  desired state (or, does not cancel its previous progress) when the cluster state is *unready* for the controller to
  make progress. Here, unready means the controller has some terminating children objects, so the controller might need
  to wait for termination before making progress. *)
Definition preservation_spec γ l (ctx : context.Context.t) (kube_client : loc) (burst : w64)
    (rsc_clock : interface.t) (controller_features : upstreamrs.ReplicaSetControllerFeatures.t)
    namespace name rs dq pods orphan_pods
    : iProp Σ :=
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "%Hclock" ∷ ⌜ rsc_clock = real_clock ⌝ ∗
      "Hresources" ∷ owned_resources γ rs pods orphan_pods (mutating_fractions dq) false ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement rs ⌝ ∗
      "%Hburst" ∷ ⌜ 0 < sint.Z burst < 2^31 ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝
  }}}
    @! replicaset.syncReplicaSet #ctx #kube_client #replica_set_lister #burst
      #rsc_clock #controller_features #namespace #name
  (* The status write may be rejected, for example when a pod count overflows
     int32 in calculateStatus; the sync then returns that error. Pods are not
     written after it, so the distance claim holds either way. *)
  {{{ (rs' : ReplicaSetV.t) (pods' released : list PodV.t) (err : interface.t), RET #err;
      owned_resources γ rs' pods' (filter (λ pod, ¬ rs_selects rs pod)%type orphan_pods ++ released)
        (mutating_fractions dq) false ∗
      ⌜ PodV.key <$> released ≡ₚ PodV.key <$> filter (λ pod, ¬ rs_selects rs pod) pods ⌝ ∗
      ⌜ Forall (λ pod, meta_parent_ref pod.(PodV.ObjectMeta') = None ∧ ¬ rs_selects rs pod) released ⌝ ∗
      ⌜ match_distance rs pods' ≤ claim_distance rs pods orphan_pods ⌝
  }}}.

(* Stability preserves the represented pod resources when the observed pod
   count matches the desired count: the sync returns the same [pods]. Status
   may be updated and the sync may return an error. Status correctness is left
   to helper specs. *)
Definition stability_spec γ l (ctx : context.Context.t) (kube_client : loc) (burst : w64)
    (rsc_clock : interface.t) (controller_features : upstreamrs.ReplicaSetControllerFeatures.t)
    namespace name rs dq pods orphan_pods
    : iProp Σ :=
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "%Hclock" ∷ ⌜ rsc_clock = real_clock ⌝ ∗
      "Hresources" ∷ owned_resources γ rs pods orphan_pods (stability_fractions dq) true ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement rs ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hmatch" ∷ ⌜ current_state_matches rs pods ⌝ ∗
      (* Nothing to release or adopt. *)
      "%Hpods_selected" ∷ ⌜ Forall (rs_selects rs) pods ⌝ ∗
      "%Hno_selected_orphans" ∷ ⌜ Forall (λ pod, ¬ rs_selects rs pod) orphan_pods ⌝
  }}}
    @! replicaset.syncReplicaSet #ctx #kube_client #replica_set_lister #burst
      #rsc_clock #controller_features #namespace #name
  {{{ (rs' : ReplicaSetV.t) (err : interface.t), RET #err;
      owned_resources γ rs' pods orphan_pods (stability_fractions dq) true
  }}}.

End specs.
