From New.proof.controllers.statefulset Require Export statefulset_init.
From New.object_specs Require Export controllerrevision.

(* Membership uses canonical names, as in upstream PR #141094: web-1 is a
   member, web-01 is not. A desired Pod matches by identity and revision label;
   its live PodSpec may differ from the template because of API defaulting.
   This file contains the contracts and their definitions, without importing
   StatefulSet program proofs. Construction and supporting lemmas live in common.v. *)

Definition statefulset_replicas (sts : StatefulSetV.t) : nat :=
  match sts.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') with
  | Some replicas => sint.nat replicas | None => 1%nat
  end.
Definition desired_ordinals sts : list nat := seq 0 (statefulset_replicas sts).
Definition desired_pod_name (set_name : go_string) ordinal : go_string :=
  set_name ++ "-"%go ++ decimal_string ordinal.
Definition desired_pod_key sts ordinal : KKey.t :=
  KKey.mk PodV.kind (desired_pod_name sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal)
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace').
Definition desired_pod_keys sts : list KKey.t := desired_pod_key sts <$> desired_ordinals sts.
Definition pvc_claim_template_names (sts : StatefulSetV.t) : list go_string :=
  (λ claim, claim.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name')) <$>
    StatefulSetSpecV.volume_claim_templates_list sts.(StatefulSetV.Spec').
Definition desired_pvc_name set_name claim_name ordinal : go_string :=
  claim_name ++ "-"%go ++ desired_pod_name set_name ordinal.
Definition desired_pvc_key sts claim_name ordinal : KKey.t :=
  KKey.mk PersistentVolumeClaimV.kind
    (desired_pvc_name sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') claim_name ordinal)
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace').
Definition desired_pvc_key_candidates sts : list KKey.t :=
  concat ((λ ordinal, (λ claim, desired_pvc_key sts claim ordinal) <$> pvc_claim_template_names sts)
    <$> desired_ordinals sts).
Definition desired_pvc_keys sts : list KKey.t :=
  elements (list_to_set (C:=gset KKey.t) (desired_pvc_key_candidates sts)).

(* TODO: connect these pure codec/defaulting/hash operations to library proofs.
   The semantic matcher includes the enabled feature gate and re-encoding.
   Payload equality is checked independently of the name hash; no injectivity
   assumption about the hash or serialization is made. *)
Parameter revision_template_patch : PodTemplateSpecV.t → list w8.
Parameter revision_template_payload_matches : PodTemplateSpecV.t → list w8 → bool.
Parameter revision_candidate_name : go_string → list w8 → w32 → go_string.
Definition revision_key sts name : KKey.t :=
  KKey.mk ControllerRevisionV.kind name sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace').
Definition revision_exact_payload sts (revision : ControllerRevisionV.t) : Prop :=
  revision.(ControllerRevisionV.Data').(RawExtensionV.Object') = interface.nil ∧
  revision.(ControllerRevisionV.Data').(RawExtensionV.Raw') =
    Some (revision_template_patch sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template')).
Definition revision_represents_desired sts (revision : ControllerRevisionV.t) : Prop :=
  revision.(ControllerRevisionV.Data').(RawExtensionV.Object') = interface.nil ∧
  match revision.(ControllerRevisionV.Data').(RawExtensionV.Raw') with
  | Some raw => raw = revision_template_patch sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template') ∨
      revision_template_payload_matches sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template') raw = true
  | None => False
  end.
#[global] Instance revision_represents_desired_decision sts revision :
    Decision (revision_represents_desired sts revision).
Proof.
  unfold revision_represents_desired.
  destruct revision.(ControllerRevisionV.Data').(RawExtensionV.Raw'); apply _.
Defined.
Definition statefulset_revision_label : go_string := "controller-revision-hash"%go.
Definition pod_revision (pod : PodV.t) : go_string :=
  default ""%go ((default ∅ pod.(PodV.ObjectMeta').(ObjectMetaV.Labels')) !! statefulset_revision_label).

(* Enumerate desired ordinals rather than specifying a parser or reasoning
   separately about malformed names and out-of-range members. *)
Definition revision_pod_matches sts revision_name (pod : PodV.t) : bool :=
  existsb (λ ordinal, bool_decide (
    PodV.key pod = desired_pod_key sts ordinal ∧
    (default ∅ pod.(PodV.ObjectMeta').(ObjectMetaV.Labels')) !! statefulset_pod_name_label =
      Some pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ∧
    (default ∅ pod.(PodV.ObjectMeta').(ObjectMetaV.Labels')) !! pod_index_label = Some (decimal_string ordinal) ∧
    pod_revision pod = revision_name)) (desired_ordinals sts).

(* Snapshots contain living objects. revision_history includes owned history
   and any foreign revision supplied for equal-payload name reuse. Only owned
   revisions belong in the StatefulSet child index. Metadata is returned
   separately because status writes can change the StatefulSet resourceVersion. *)
Record revision_state := {
  revision_metadata : ObjectMetaV.t;
  revision_status : StatefulSetStatusV.t;
  revision_pods : list PodV.t;
  revision_pvcs : list PersistentVolumeClaimV.t;
  revision_history : list ControllerRevisionV.t;
  revision_create_slot : reservation_status;
  revision_terminating_bound : nat;
}.
Definition owned_revision_history sts state : list ControllerRevisionV.t :=
  filter (λ revision, meta_parent_ref revision.(ControllerRevisionV.ObjectMeta') =
    Some (StatefulSetV.key sts, sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID'))) state.(revision_history).
Definition revision_create_name sts state : go_string :=
  revision_candidate_name sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    (revision_template_patch sts.(StatefulSetV.Spec').(StatefulSetSpecV.Template'))
    (default (W32 0) state.(revision_status).(StatefulSetStatusV.CollisionCount')).
Definition revision_child_keys sts state : gset KKey.t :=
  list_to_set (PodV.key <$> state.(revision_pods)) ∪
  list_to_set (ControllerRevisionV.key <$> owned_revision_history sts state).
Definition missing_pod_keys sts (pods : list PodV.t) : list KKey.t :=
  filter (λ key, key ∉ (PodV.key <$> pods)) (desired_pod_keys sts).
Definition missing_pvc_keys sts (pvcs : list PersistentVolumeClaimV.t) : list KKey.t :=
  filter (λ key, key ∉ (PersistentVolumeClaimV.key <$> pvcs)) (desired_pvc_keys sts).
Definition revision_available sts revision_name state : bool :=
  existsb (λ revision, bool_decide (
    revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Name') = revision_name ∧
    revision_represents_desired sts revision)) state.(revision_history).

(* One distance for the whole desired state. A missing suitable revision costs
   1, as do a missing Pod/PVC and an extra Pod. A desired Pod with incorrect
   identity or revision costs 2: deleting it leaves a missing Pod of cost 1.
   The revision target is fixed across each before/after comparison. *)
Definition match_distance sts revision_name state : nat :=
  (if revision_available sts revision_name state then 0%nat else 1%nat) +
  length (missing_pod_keys sts state.(revision_pods)) + length (missing_pvc_keys sts state.(revision_pvcs)) +
  fold_right Nat.add 0%nat ((λ pod, if decide (PodV.key pod ∈ desired_pod_keys sts)
    then if revision_pod_matches sts revision_name pod then 0%nat else 2%nat
    else 1%nat) <$> state.(revision_pods)).

Definition current_state_matches sts revision_name state : Prop :=
  revision_available sts revision_name state = true ∧
  PodV.key <$> state.(revision_pods) ≡ₚ desired_pod_keys sts ∧
  Forall (λ pod, revision_pod_matches sts revision_name pod = true) state.(revision_pods) ∧
  missing_pvc_keys sts state.(revision_pvcs) = [].

Definition revision_status_without_bookkeeping (status : StatefulSetStatusV.t) : StatefulSetStatusV.t :=
  status <| StatefulSetStatusV.CurrentRevision' := ""%go |>
    <| StatefulSetStatusV.UpdateRevision' := ""%go |> <| StatefulSetStatusV.CollisionCount' := None |>.
Definition revision_preserved sts before after : Prop :=
  revision_status_without_bookkeeping before.(revision_status) =
    revision_status_without_bookkeeping after.(revision_status) ∧
  (∀ old new, old ∈ before.(revision_history) → new ∈ after.(revision_history) →
    ControllerRevisionV.key old = ControllerRevisionV.key new →
    old.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.UID') =
      new.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.UID') →
    old.(ControllerRevisionV.Data') = new.(ControllerRevisionV.Data') ∧
    meta_parent_ref old.(ControllerRevisionV.ObjectMeta') = meta_parent_ref new.(ControllerRevisionV.ObjectMeta')) ∧
  (* History referenced by a desired Pod survives even if this call deletes the Pod. *)
  (∀ pod old, pod ∈ before.(revision_pods) → PodV.key pod ∈ desired_pod_keys sts →
    old ∈ before.(revision_history) →
    pod_revision pod = old.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Name') →
    ∃ new, new ∈ after.(revision_history) ∧ ControllerRevisionV.key new = ControllerRevisionV.key old ∧
      new.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.UID') =
        old.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.UID') ∧
      new.(ControllerRevisionV.Data') = old.(ControllerRevisionV.Data')).
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

Definition state_progress_observed before after : Prop :=
  pods_progress_observed before.(revision_pods) after.(revision_pods) ∨
  list_to_set (C:=gset KKey.t) (PersistentVolumeClaimV.key <$> before.(revision_pvcs)) ≠
    list_to_set (C:=gset KKey.t) (PersistentVolumeClaimV.key <$> after.(revision_pvcs)) ∨
  ¬ ((λ revision, (ControllerRevisionV.key revision, revision.(ControllerRevisionV.Data'))) <$>
      before.(revision_history) ≡ₚ
     (λ revision, (ControllerRevisionV.key revision, revision.(ControllerRevisionV.Data'))) <$>
      after.(revision_history)).

Definition revision_protected_names state : gset go_string :=
  {[state.(revision_status).(StatefulSetStatusV.CurrentRevision');
    state.(revision_status).(StatefulSetStatusV.UpdateRevision')]} ∪
  list_to_set (pod_revision <$> state.(revision_pods)).
Definition revision_history_within_limit sts state : Prop :=
  let unused := filter (λ revision,
    revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Name') ∉ revision_protected_names state)
    (owned_revision_history sts state) in
  match sts.(StatefulSetV.Spec').(StatefulSetSpecV.RevisionHistoryLimit') with
  | Some limit => sint.Z limit < 0 ∨ (length unused ≤ sint.nat limit)%nat
  | None => (length unused ≤ 10)%nat
  end.

(* A stable target is either the settled owned history entry or an equal-Raw
   candidate reused from outside that history. Foreign reuse does not adopt it. *)
Definition revision_target_stable sts update state : Prop :=
  (update ∈ owned_revision_history sts state ∧
    (∀ old, old ∈ owned_revision_history sts state →
      ControllerRevisionV.key old ≠ ControllerRevisionV.key update →
      sint.Z old.(ControllerRevisionV.Revision') < sint.Z update.(ControllerRevisionV.Revision')) ∧
    (revision_exact_payload sts update ∨
      (∀ old, old ∈ owned_revision_history sts state → ¬ revision_exact_payload sts old))) ∨
  (update ∉ owned_revision_history sts state ∧ revision_exact_payload sts update ∧
    update.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Name') = revision_create_name sts state ∧
    (∀ old, old ∈ owned_revision_history sts state → ¬ revision_represents_desired sts old)).
Definition revision_fixed_point sts state : Prop :=
  ∃ update, update ∈ state.(revision_history) ∧ revision_represents_desired sts update ∧
    revision_target_stable sts update state ∧
    current_state_matches sts update.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Name') state ∧
    state.(revision_status).(StatefulSetStatusV.CurrentRevision') =
      update.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Name') ∧
    state.(revision_status).(StatefulSetStatusV.UpdateRevision') =
      update.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Name') ∧
    is_Some state.(revision_status).(StatefulSetStatusV.CollisionCount') ∧
    state.(revision_terminating_bound) = 0%nat ∧ revision_history_within_limit sts state.

Definition revision_state_wf sts state : Prop :=
  ObjectMetaV.without_resource_version state.(revision_metadata) =
    ObjectMetaV.without_resource_version sts.(StatefulSetV.ObjectMeta') ∧
  NoDup (PodV.key <$> state.(revision_pods)) ∧ NoDup (PersistentVolumeClaimV.key <$> state.(revision_pvcs)) ∧
  NoDup (ControllerRevisionV.key <$> state.(revision_history)) ∧
  (∀ count, state.(revision_status).(StatefulSetStatusV.CollisionCount') = Some count → 0 ≤ sint.Z count) ∧
  Forall (λ revision,
    revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Namespace') =
      sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ∧
    ((snd <$> meta_parent_ref revision.(ControllerRevisionV.ObjectMeta')) =
       Some sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') →
      meta_parent_ref revision.(ControllerRevisionV.ObjectMeta') =
        Some (StatefulSetV.key sts, sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')) ∧
      (∃ owner, owner ∈ default [] revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.OwnerReferences') ∧
        owner.(OwnerReferenceV.Controller') = Some true ∧ owner.(OwnerReferenceV.APIVersion') = "apps/v1"%go) ∧
      (match sts.(StatefulSetV.Spec').(StatefulSetSpecV.Selector') with
       | Some selector =>
           LabelSelectorV.matches selector revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Labels')
       | None => False
       end))) state.(revision_history).

Section specs.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Collection W := sem + package_sem.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(* Each candidate is available or occupied by the exact proposed payload.
   The occupied witness belongs to revision_history, whose metadata/spec
   fragments are supplied below even when that object has a foreign owner.
   Unequal-payload collisions and deleting candidate names are excluded.
   TODO: prove the occupied-name AlreadyExists API helper; Get can use the
   metadata/spec fragments supplied here. *)
Definition own_revision_create_slot γ sts state dq : iProp Σ :=
  own_reserved_frag γ (revision_key sts (revision_create_name sts state)) dq state.(revision_create_slot).
Definition revision_create_pre γ sts state dq : iProp Σ :=
  let key := revision_key sts (revision_create_name sts state) in
  (own_available_reserved_frag γ dq key ∗ ⌜ state.(revision_create_slot) = Available ⌝) ∨
  ∃ revision, own_occupied_reserved_frag γ dq key revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.UID') ∗
    ⌜ state.(revision_create_slot) = Occupied revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.UID') ∧
      revision ∈ state.(revision_history) ∧ ControllerRevisionV.key revision = key ∧
      revision_exact_payload sts revision ⌝.

(* The desired spec may be shared. All mutable resources use one fraction:
   full ownership for progress/preservation, a shared fraction for stability.
   ready requires available missing-Pod names and no terminating children. *)
Definition owned_resources γ sts state spec_dq dq (ready : bool) : iProp Σ :=
  own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq
    state.(revision_metadata) ∗
  own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') spec_dq
    (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
  own_status_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq
    (ObjectStatusV.StatefulSetStatus state.(revision_status)) ∗
  ([∗ list] pod ∈ state.(revision_pods),
    own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq pod.(PodV.ObjectMeta') ∗
    own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq
      (ObjectSpecV.PodSpec pod.(PodV.Spec')) ∗
    own_occupied_reserved_frag γ dq (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID')) ∗
  ([∗ list] key ∈ missing_pod_keys sts state.(revision_pods),
    own_available_reserved_frag γ dq key ∨
      if ready then False else ∃ uid, own_deleting_reserved_frag γ dq key uid) ∗
  ([∗ list] revision ∈ state.(revision_history),
    own_meta_frag γ (ControllerRevisionV.key revision) revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.UID') dq
      revision.(ControllerRevisionV.ObjectMeta') ∗
    own_spec_frag γ (ControllerRevisionV.key revision) revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.UID') dq
      (ObjectSpecV.ControllerRevisionSpec (ControllerRevisionV.spec revision))) ∗
  ([∗ list] revision ∈ filter (λ revision,
      revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.Name') ≠ revision_create_name sts state)
      state.(revision_history),
    own_occupied_reserved_frag γ dq (ControllerRevisionV.key revision)
      revision.(ControllerRevisionV.ObjectMeta').(ObjectMetaV.UID')) ∗
  own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq
    (revision_child_keys sts state) ∗
  own_terminating_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
    state.(revision_terminating_bound) ∗
  ([∗ list] pvc ∈ state.(revision_pvcs),
    own_meta_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') dq
      pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
    own_occupied_reserved_frag γ dq (PersistentVolumeClaimV.key pvc)
      pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID')) ∗
  ([∗ list] key ∈ missing_pvc_keys sts state.(revision_pvcs), own_available_reserved_frag γ dq key) ∗
  ⌜ revision_state_wf sts state ∧ (ready = true → state.(revision_terminating_bound) = 0%nat) ⌝.

(* TODO: migrate the program proof and establish the input requirements for
   successful codec operations, generated requests, and revision counters.
   Like ReplicaSet progress, this contract requires success and an observed
   change with a shorter distance unless the desired state has been reached. *)
Definition progress_spec γ l namespace name sts dq state : iProp Σ :=
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      is_kubernetes γ l ∗
      (global_addr apimodel.ModelState) ↦□ l ∗
      owned_resources γ sts state dq 1 true ∗
      revision_create_pre γ sts state 1 ∗
      ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ state' revision_name, RET #interface.nil;
      owned_resources γ sts state' dq 1 false ∗
      own_revision_create_slot γ sts state' 1 ∗
      ⌜ revision_preserved sts state state' ⌝ ∗
      ⌜ revision_available sts revision_name state' = true ∧
        state'.(revision_status).(StatefulSetStatusV.UpdateRevision') = revision_name ⌝ ∗
      ⌜ current_state_matches sts revision_name state' ∨
        (state_progress_observed state state' ∧ match_distance sts revision_name state' <
          match_distance sts revision_name state)%nat ⌝
  }}}.

Definition preservation_spec γ l namespace name sts dq state : iProp Σ :=
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      is_kubernetes γ l ∗
      (global_addr apimodel.ModelState) ↦□ l ∗
      owned_resources γ sts state dq 1 false ∗
      revision_create_pre γ sts state 1 ∗
      ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ state' (err : interface.t), RET #err;
      owned_resources γ sts state' dq 1 false ∗
      own_revision_create_slot γ sts state' 1 ∗
      ⌜ revision_preserved sts state state' ⌝
  }}}.

Definition stability_spec γ l namespace name sts dq state : iProp Σ :=
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      is_kubernetes γ l ∗
      (global_addr apimodel.ModelState) ↦□ l ∗
      owned_resources γ sts state dq dq true ∗
      revision_create_pre γ sts state dq ∗
      ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      ⌜ revision_fixed_point sts state ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ (err : interface.t), RET #err;
      owned_resources γ sts state dq dq true ∗
      revision_create_pre γ sts state dq
  }}}.
End specs.
