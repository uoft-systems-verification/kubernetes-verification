Require Export New.proof.sync.
From proof.k8s_io.api.apps Require Export v1_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof Require Export time.
From proof Require Import prelude empty_ffi.

Module PureOwnerReference.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  APIVersion' : go_string;
  Kind' : go_string;
  Name' : go_string;
  UID' : types.UID.t;
  Controller' : option bool;
  BlockOwnerDeletion' : option bool;
}.
End def.
End PureOwnerReference.

Module OwnerReference.
Section def.
Context `{ffi_syntax} `{hG: !heapGS Σ}.
Definition own (c: v1.OwnerReference.t) (v: PureOwnerReference.t): iProp Σ :=
  ⌜ c.(v1.OwnerReference.APIVersion') = v.(PureOwnerReference.APIVersion') ⌝ ∗
  ⌜ c.(v1.OwnerReference.Kind') = v.(PureOwnerReference.Kind') ⌝ ∗
  ⌜ c.(v1.OwnerReference.Name') = v.(PureOwnerReference.Name') ⌝ ∗
  ⌜ c.(v1.OwnerReference.UID') = v.(PureOwnerReference.UID') ⌝ ∗
  (match v.(PureOwnerReference.Controller') with
  | None => ⌜ c.(v1.OwnerReference.Controller') = null ⌝
  | Some b => ∃ controller, c.(v1.OwnerReference.Controller') ↦ controller ∗ ⌜ controller = b ⌝
  end) ∗
  (match v.(PureOwnerReference.BlockOwnerDeletion') with
  | None => ⌜ c.(v1.OwnerReference.BlockOwnerDeletion') = null ⌝
  | Some b => ∃ block_owner_deletion,
    c.(v1.OwnerReference.BlockOwnerDeletion') ↦ block_owner_deletion ∗ ⌜ block_owner_deletion = b ⌝
  end).
End def.
End OwnerReference.

Module PureObjectMeta.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Name' : go_string;
  GenerateName' : go_string;
  Namespace' : go_string;
  SelfLink' : go_string;
  UID' : types.UID.t;
  ResourceVersion' : go_string;
  Generation' : w64;
  (* CreationTimestamp' : Time.t; *)
  (* DeletionTimestamp' : loc; *)
  DeletionGracePeriodSeconds' : option w64;
  Labels' : option (gmap go_string go_string);
  Annotations' : option (gmap go_string go_string);
  OwnerReferences' : option (list PureOwnerReference.t);
  Finalizers' : option (list go_string);
  (* ManagedFields' : slice.t; *)
}.
End def.
End PureObjectMeta.

Module ObjectMeta.
Section def.
Context `{ffi_syntax} `{hG: !heapGS Σ}.
Definition own (c: v1.ObjectMeta.t) (v: PureObjectMeta.t): iProp Σ :=
  "%Hown_name" ∷ ⌜ c.(v1.ObjectMeta.Name') = v.(PureObjectMeta.Name') ⌝ ∗
  "%Hown_generatename" ∷ ⌜ c.(v1.ObjectMeta.GenerateName') = v.(PureObjectMeta.GenerateName') ⌝ ∗
  "%Hown_namespace" ∷ ⌜ c.(v1.ObjectMeta.Namespace') = v.(PureObjectMeta.Namespace') ⌝ ∗
  "%Hown_selflink" ∷ ⌜ c.(v1.ObjectMeta.SelfLink') = v.(PureObjectMeta.SelfLink') ⌝ ∗
  "%Hown_uid" ∷ ⌜ c.(v1.ObjectMeta.UID') = v.(PureObjectMeta.UID') ⌝ ∗
  "%Hown_resourceversion" ∷ ⌜ c.(v1.ObjectMeta.ResourceVersion') = v.(PureObjectMeta.ResourceVersion') ⌝ ∗
  "%Hown_generation" ∷ ⌜ c.(v1.ObjectMeta.Generation') = v.(PureObjectMeta.Generation') ⌝ ∗
  "Hown_deletiongraceperiodseconds" ∷ (match v.(PureObjectMeta.DeletionGracePeriodSeconds') with
  | None => ⌜ c.(v1.ObjectMeta.DeletionGracePeriodSeconds') = null ⌝
  | Some i => ∃ deletion_grace_period_seconds,
    c.(v1.ObjectMeta.DeletionGracePeriodSeconds') ↦ deletion_grace_period_seconds ∗ ⌜ deletion_grace_period_seconds = i ⌝
  end) ∗
  "Hown_labels" ∷ (match v.(PureObjectMeta.Labels') with
  | None => ⌜ c.(v1.ObjectMeta.Labels') = null ⌝
  | Some m => ∃ labels, c.(v1.ObjectMeta.Labels') ↦$ labels ∗ ⌜ labels = m ⌝
  end) ∗
  "Hown_annotations" ∷ (match v.(PureObjectMeta.Annotations') with
  | None => ⌜ c.(v1.ObjectMeta.Annotations') = null ⌝
  | Some m => ∃ annotations, c.(v1.ObjectMeta.Annotations') ↦$ annotations ∗ ⌜ annotations = m ⌝
  end) ∗
  "Hown_ownerreferences" ∷ (match v.(PureObjectMeta.OwnerReferences') with
  | None => ⌜ c.(v1.ObjectMeta.OwnerReferences') = slice.nil ⌝
  | Some os => ∃ owner_references,
    c.(v1.ObjectMeta.OwnerReferences') ↦* owner_references ∗ [∗list] oc;ov ∈ owner_references;os, OwnerReference.own oc ov
  end) ∗
  "Hown_finalizers" ∷ (match v.(PureObjectMeta.Finalizers') with
  | None => ⌜ c.(v1.ObjectMeta.Finalizers') = slice.nil ⌝
  | Some fs => ∃ finalizers, c.(v1.ObjectMeta.Finalizers') ↦* finalizers ∗ ⌜ finalizers = fs ⌝
  end).
End def.
End ObjectMeta.

Module PurePodSpec.
Section def.
Context `{ffi_syntax}.
Record t := mk {}.
End def.
End PurePodSpec.

Module PodSpec.
Section def.
Context `{ffi_syntax} `{hG: !heapGS Σ}.
Definition own (c: v1.PodSpec.t) (v: PurePodSpec.t): iProp Σ := True%I.
End def.
End PodSpec.

Module PurePodStatus.
Section def.
Context `{ffi_syntax}.
Record t := mk {}.
End def.
End PurePodStatus.

Module PodStatus.
Section def.
Context `{ffi_syntax} `{hG: !heapGS Σ}.
Definition own (c: v1.PodStatus.t) (v: PurePodStatus.t): iProp Σ := True%I.
End def.
End PodStatus.

Module PurePod.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : PureObjectMeta.t;
  Spec' : PurePodSpec.t;
  Status' : PurePodStatus.t;
}.
End def.
End PurePod.

Module Pod.
Section def.
Context `{ffi_syntax} `{hG: !heapGS Σ}.
Definition own (c: v1.Pod.t) (v: PurePod.t): iProp Σ :=
  "%Hown_typemeta" ∷ ⌜ c.(v1.Pod.TypeMeta') = v.(PurePod.TypeMeta') ⌝ ∗
  "Hown_objectmeta" ∷ ObjectMeta.own c.(v1.Pod.ObjectMeta') v.(PurePod.ObjectMeta') ∗
  "Hown_podspec" ∷ PodSpec.own c.(v1.Pod.Spec') v.(PurePod.Spec') ∗
  "Hown_podstatus" ∷ PodStatus.own c.(v1.Pod.Status') v.(PurePod.Status').
End def.
End Pod.

Module PureReplicaSetSpec.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Replicas' : option w32;
  MinReadySeconds' : w32;
  (* Selector' : loc; *)
  (* Template' : v1.PodTemplateSpec.t; *)
}.
End def.
End PureReplicaSetSpec.

Module ReplicaSetSpec.
Section def.
Context `{ffi_syntax} `{hG: !heapGS Σ}.
Definition own (c: v1.ReplicaSetSpec.t) (v: PureReplicaSetSpec.t): iProp Σ :=
  match v.(PureReplicaSetSpec.Replicas') with
  | None => ⌜ c.(v1.ReplicaSetSpec.Replicas') =  null ⌝
  | Some i => ∃ replicas, c.(v1.ReplicaSetSpec.Replicas') ↦ replicas ∗ ⌜ replicas = i ⌝
  end ∗
  ⌜ c.(v1.ReplicaSetSpec.MinReadySeconds') = v.(PureReplicaSetSpec.MinReadySeconds') ⌝.
End def.
End ReplicaSetSpec.

Module PureReplicaSetStatus.
Section def.
Context `{ffi_syntax}.
Record t := mk {}.
End def.
End PureReplicaSetStatus.

Module ReplicaSetStatus.
Section def.
Context `{ffi_syntax} `{hG: !heapGS Σ}.
Definition own (c: v1.ReplicaSetStatus.t) (v: PureReplicaSetStatus.t): iProp Σ := True%I.
End def.
End ReplicaSetStatus.

Module PureReplicaSet.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : PureObjectMeta.t;
  Spec' : PureReplicaSetSpec.t;
  Status' : PureReplicaSetStatus.t;
}.
End def.
End PureReplicaSet.

Module ReplicaSet.
Section def.
Context `{ffi_syntax} `{hG: !heapGS Σ}.
Definition own (c: v1.ReplicaSet.t) (v: PureReplicaSet.t): iProp Σ :=
  ⌜ c.(v1.ReplicaSet.TypeMeta') = v.(PureReplicaSet.TypeMeta') ⌝ ∗
  ObjectMeta.own c.(v1.ReplicaSet.ObjectMeta') v.(PureReplicaSet.ObjectMeta') ∗
  ReplicaSetSpec.own c.(v1.ReplicaSet.Spec') v.(PureReplicaSet.Spec') ∗
  ReplicaSetStatus.own c.(v1.ReplicaSet.Status') v.(PureReplicaSet.Status').
End def.
End ReplicaSet.
