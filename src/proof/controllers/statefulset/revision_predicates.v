From New.object_specs Require Export prelude controllerrevision.

(* These definitions separate editable revision membership from the historical
   construction evidence required to reason about the Pod's body. *)
Definition statefulset_revision_label : go_string := "controller-revision-hash"%go.
Definition pod_revision (pod : PodV.t) : go_string :=
  default ""%go ((default ∅ pod.(PodV.ObjectMeta').(ObjectMetaV.Labels')) !! statefulset_revision_label).
Definition with_pod_revision (pod : PodV.t) (revision : go_string) : PodV.t :=
  pod <| PodV.ObjectMeta' := pod.(PodV.ObjectMeta') <| ObjectMetaV.Labels' :=
    Some (<[statefulset_revision_label := revision]>
      (default ∅ pod.(PodV.ObjectMeta').(ObjectMetaV.Labels'))) |> |>.
Definition pod_revision_member revision pod : Prop := pod_revision pod = revision.

Lemma with_pod_revision_member pod revision :
  pod_revision_member revision (with_pod_revision pod revision).
Proof. unfold pod_revision_member, pod_revision, with_pod_revision. simpl. by rewrite lookup_insert. Qed.
Lemma with_pod_revision_body pod revision :
  (with_pod_revision pod revision).(PodV.Spec') = pod.(PodV.Spec') ∧
  (with_pod_revision pod revision).(PodV.Status') = pod.(PodV.Status').
Proof. split; reflexivity. Qed.
(* The modeled API defaults and admission preserve the submitted metadata
   labels. This fact does not extend to arbitrary label-editing webhooks. *)
Lemma pod_revision_api_created namespace input stored :
  PodV.created namespace input stored → pod_revision stored = pod_revision input.
Proof.
  intros (_ & Hmeta & _).
  unfold ObjectMetaV.created in Hmeta.
  assert (stored.(PodV.ObjectMeta').(ObjectMetaV.Labels') =
    input.(PodV.ObjectMeta').(ObjectMetaV.Labels')) as Hlabels by tauto.
  unfold pod_revision. by rewrite Hlabels.
Qed.
Lemma pod_revision_body_update pod spec status :
  pod_revision (pod <| PodV.Spec' := spec |> <| PodV.Status' := status |>) = pod_revision pod.
Proof. reflexivity. Qed.
Lemma pod_revision_other_label pod key value :
  key ≠ statefulset_revision_label →
  pod_revision (pod <| PodV.ObjectMeta' := pod.(PodV.ObjectMeta') <| ObjectMetaV.Labels' :=
    Some (<[key := value]> (default ∅ pod.(PodV.ObjectMeta').(ObjectMetaV.Labels'))) |> |>) = pod_revision pod.
Proof. intros Hne. unfold pod_revision. simpl. by rewrite lookup_insert_ne. Qed.

Definition revision_owned_by (set : StatefulSetV.t) (revision : ControllerRevisionV.t) : Prop :=
  revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Namespace') =
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ∧
  meta_parent_ref_is revision.(ControllerRevisionV.ObjectMeta') "StatefulSet"%go
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID').

(* The encoding relation is the imported runtime/JSON/strategic-patch contract.
   It must describe the restored/defaulted template, rather than assert hash
   injectivity or infer a template from the revision's name. *)
Parameter revision_payload_encodes : list w8 → PodTemplateSpecV.t → Prop.
Definition revision_represents (revision : ControllerRevisionV.t) template : Prop :=
  revision.(ControllerRevisionV.Data').(RawExtensionV.Object') = interface.nil ∧
  ∃ raw, revision.(ControllerRevisionV.Data').(RawExtensionV.Raw') = Some raw ∧
    revision_payload_encodes raw template.

Record revision_snapshot := {
  snapshot_key : KKey.t;
  snapshot_uid : types.UID.t;
  snapshot_owner_uid : types.UID.t;
  snapshot_raw : list w8;
  snapshot_template : PodTemplateSpecV.t;
}.
Definition snapshot_interpreted (snapshot : revision_snapshot) : Prop :=
  revision_payload_encodes snapshot.(snapshot_raw) snapshot.(snapshot_template).
Definition snapshot_live (snapshot : revision_snapshot) (revision : ControllerRevisionV.t) : Prop :=
  ControllerRevisionV.key revision = snapshot.(snapshot_key) ∧
  revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.UID') = snapshot.(snapshot_uid) ∧
  revision.(ControllerRevisionV.Data').(RawExtensionV.Raw') = Some snapshot.(snapshot_raw).

(* A provenance witness is captured at successful API creation and retained
   across history cleanup. Editable labels alone supply no such witness.
   [constructed_from] records the modeled construction/defaulting/admission
   relation; allowed interference must preserve it or a weaker stated property. *)
Definition pod_revision_provenance
    (constructed_from : PodTemplateSpecV.t → PodV.t → Prop)
    (set : StatefulSetV.t) (snapshot : revision_snapshot) (pod : PodV.t) : Prop :=
  snapshot_interpreted snapshot ∧
  snapshot.(snapshot_owner_uid) = set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') ∧
  snapshot.(snapshot_key).(KKey.Namespace') = set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ∧
  pod_revision_member snapshot.(snapshot_key).(KKey.Name') pod ∧
  constructed_from snapshot.(snapshot_template) pod.

Definition rolling_partition (set : StatefulSetV.t) : nat :=
  match set.(StatefulSetV.Spec').(StatefulSetSpecV.UpdateStrategy').(StatefulSetView.StatefulSetUpdateStrategyV.RollingUpdate') with
  | Some rolling => match rolling.(StatefulSetView.RollingUpdateStatefulSetStrategyV.Partition') with Some n => sint.nat n | None => 0%nat end
  | None => 0%nat
  end.
Definition on_delete (set : StatefulSetV.t) : Prop :=
  set.(StatefulSetV.Spec').(StatefulSetSpecV.UpdateStrategy').(StatefulSetView.StatefulSetUpdateStrategyV.Type') = "OnDelete"%go.
(* OnDelete and below-partition existing Pods are intentionally retained.
   Creation's current/update choice is a separate rule. *)
Definition ordinal_rollout_complete set update_revision (ordinal : nat) pod : Prop :=
  on_delete set ∨ (ordinal < rolling_partition set)%nat ∨ pod_revision_member update_revision pod.
Definition history_entry_live current update (pods : list PodV.t) (revision : ControllerRevisionV.t) : Prop :=
  revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Name') = current ∨
  revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Name') = update ∨
  ∃ pod, pod ∈ pods ∧ pod_revision pod = revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Name').
Lemma terminating_reference_is_live current update pods revision pod :
  pod ∈ pods →
  pod_revision pod = revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Name') →
  history_entry_live current update pods revision.
Proof. intros Hin Hlabel. right. right. eauto. Qed.

Inductive reconciliation_wait := AwaitReadiness | AwaitAvailability | AwaitDeletion.
Inductive reconciliation_outcome :=
| ReconciliationComplete
| ReconciliationAdvanced
| ReconciliationWaiting (reason : reconciliation_wait)
| ReconciliationRetry.
(* History/status setup precedes Pod/PVC work. This abstract ordering alone
   does not establish a controller transition theorem. Each concrete helper
   still needs to prove either decrease, completion, or an explicit wait/error. *)
Record revision_progress_measure := {
  history_pending : nat;
  status_pending : nat;
  pod_pvc_distance : nat;
}.
Definition revision_progress_lt (after before : revision_progress_measure) : Prop :=
  (after.(history_pending) < before.(history_pending))%nat ∨
  after.(history_pending) = before.(history_pending) ∧
    ((after.(status_pending) < before.(status_pending))%nat ∨
     after.(status_pending) = before.(status_pending) ∧
       (after.(pod_pvc_distance) < before.(pod_pvc_distance))%nat).
Definition staged_progress outcome before after : Prop :=
  match outcome with
  | ReconciliationAdvanced => revision_progress_lt after before
  | ReconciliationComplete => after.(history_pending) = 0%nat ∧ after.(status_pending) = 0%nat ∧ after.(pod_pvc_distance) = 0%nat
  | ReconciliationWaiting _ | ReconciliationRetry => True
  end.
Lemma readiness_wait_allows_stuttering measure :
  staged_progress (ReconciliationWaiting AwaitReadiness) measure measure.
Proof. exact I. Qed.
