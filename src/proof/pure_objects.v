Require Export New.proof.sync.
From proof.k8s_io.api.apps Require Export v1_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From proof.kubernetes_model Require Export apimodel_init.
From New.proof Require Export time.
From proof Require Import prelude empty_ffi.
Export apimodel.apimodel.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L169 *)
Axiom valid_name: go_string → Prop.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L177 *)
Axiom valid_namespace: go_string → Prop.

Module PureOwnerReference.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  APIVersion' : go_string;
  Kind' : go_string;
  Name' : go_string;
  UID' : types.UID.t;
  Controller' : option bool;
  BlockOwnerDeletion' : option bool;
}.

Definition own (c: v1.OwnerReference.t) (v: t): iProp Σ :=
  ⌜ c.(v1.OwnerReference.APIVersion') = v.(APIVersion') ⌝ ∗
  ⌜ c.(v1.OwnerReference.Kind') = v.(Kind') ⌝ ∗
  ⌜ c.(v1.OwnerReference.Name') = v.(Name') ⌝ ∗
  ⌜ c.(v1.OwnerReference.UID') = v.(UID') ⌝ ∗
  (match v.(Controller') with
  | None => ⌜ c.(v1.OwnerReference.Controller') = null ⌝
  | Some b => ∃ controller, c.(v1.OwnerReference.Controller') ↦ controller ∗ ⌜ controller = b ⌝
  end) ∗
  (match v.(BlockOwnerDeletion') with
  | None => ⌜ c.(v1.OwnerReference.BlockOwnerDeletion') = null ⌝
  | Some b => ∃ block_owner_deletion,
    c.(v1.OwnerReference.BlockOwnerDeletion') ↦ block_owner_deletion ∗ ⌜ block_owner_deletion = b ⌝
  end).

Definition list_well_formed (os: list t) : Prop :=
  (* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L92 *)
  ∀ i1 o1 i2 o2,
    os !! i1 = Some o1 ∧ o1.(Controller') = Some true ∧
    os !! i2 = Some o2 ∧ o2.(Controller') = Some true →
      i1 = i2.
End def.
End PureOwnerReference.

Module PureObjectMeta.
Section def.
Context `{hG: !heapGS Σ}.
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

(* TODO: translate https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go to spec *)
Definition well_formed (m: t) : Prop :=
  (m.(GenerateName') ≠ ""%go → valid_name m.(GenerateName')) ∧
  m.(Name') ≠ ""%go ∧
  valid_name m.(Name') ∧
  m.(Namespace') ≠ ""%go ∧
  valid_namespace m.(Namespace') ∧
  match m.(OwnerReferences') with
  | None => True
  | Some os => PureOwnerReference.list_well_formed os
  end.

Definition well_formed_uninitialized (m: t) : Prop :=
  (m.(Name') = ""%go → m.(GenerateName') ≠ ""%go) ∧
  match m.(OwnerReferences') with
  | None => True
  | Some os => PureOwnerReference.list_well_formed os
  end.

Definition own (c: v1.ObjectMeta.t) (v: t): iProp Σ :=
  "%Hown_name" ∷ ⌜ c.(v1.ObjectMeta.Name') = v.(Name') ⌝ ∗
  "%Hown_generatename" ∷ ⌜ c.(v1.ObjectMeta.GenerateName') = v.(GenerateName') ⌝ ∗
  "%Hown_namespace" ∷ ⌜ c.(v1.ObjectMeta.Namespace') = v.(Namespace') ⌝ ∗
  "%Hown_selflink" ∷ ⌜ c.(v1.ObjectMeta.SelfLink') = v.(SelfLink') ⌝ ∗
  "%Hown_uid" ∷ ⌜ c.(v1.ObjectMeta.UID') = v.(UID') ⌝ ∗
  "%Hown_resourceversion" ∷ ⌜ c.(v1.ObjectMeta.ResourceVersion') = v.(ResourceVersion') ⌝ ∗
  "%Hown_generation" ∷ ⌜ c.(v1.ObjectMeta.Generation') = v.(Generation') ⌝ ∗
  "Hown_deletiongraceperiodseconds" ∷ (match v.(DeletionGracePeriodSeconds') with
  | None => ⌜ c.(v1.ObjectMeta.DeletionGracePeriodSeconds') = null ⌝
  | Some i => ∃ deletion_grace_period_seconds,
    c.(v1.ObjectMeta.DeletionGracePeriodSeconds') ↦ deletion_grace_period_seconds ∗ ⌜ deletion_grace_period_seconds = i ⌝
  end) ∗
  "Hown_labels" ∷ (match v.(Labels') with
  | None => ⌜ c.(v1.ObjectMeta.Labels') = null ⌝
  | Some m => ∃ labels, c.(v1.ObjectMeta.Labels') ↦$ labels ∗ ⌜ labels = m ⌝
  end) ∗
  "Hown_annotations" ∷ (match v.(Annotations') with
  | None => ⌜ c.(v1.ObjectMeta.Annotations') = null ⌝
  | Some m => ∃ annotations, c.(v1.ObjectMeta.Annotations') ↦$ annotations ∗ ⌜ annotations = m ⌝
  end) ∗
  "Hown_ownerreferences" ∷ (match v.(OwnerReferences') with
  | None => ⌜ c.(v1.ObjectMeta.OwnerReferences') = slice.nil ⌝
  | Some os => ∃ owner_references,
    c.(v1.ObjectMeta.OwnerReferences') ↦* owner_references ∗ [∗list] oc;ov ∈ owner_references;os, PureOwnerReference.own oc ov
  end) ∗
  "Hown_finalizers" ∷ (match v.(Finalizers') with
  | None => ⌜ c.(v1.ObjectMeta.Finalizers') = slice.nil ⌝
  | Some fs => ∃ finalizers, c.(v1.ObjectMeta.Finalizers') ↦* finalizers ∗ ⌜ finalizers = fs ⌝
  end).
End def.
End PureObjectMeta.

Module PurePodSpec.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {}.
Axiom well_formed: t → Prop.
Definition own (c: v1.PodSpec.t) (v: t): iProp Σ := True%I.
End def.
End PurePodSpec.

Module PurePodStatus.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {}.
Axiom well_formed: t → Prop.
Definition own (c: v1.PodStatus.t) (v: t): iProp Σ := True%I.
End def.
End PurePodStatus.

Module PurePod.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : PureObjectMeta.t;
  Spec' : PurePodSpec.t;
  Status' : PurePodStatus.t;
}.

Definition well_formed (pod: t) : Prop :=
  PureObjectMeta.well_formed pod.(ObjectMeta') ∧
  PurePodSpec.well_formed pod.(Spec') ∧
  PurePodStatus.well_formed pod.(Status').

Definition well_formed_uninitialized (pod: t) : Prop :=
  PureObjectMeta.well_formed_uninitialized pod.(ObjectMeta') ∧
  PurePodSpec.well_formed pod.(Spec') ∧
  PurePodStatus.well_formed pod.(Status').
  (* PurePodSpec.well_formed_uninitialized pod.(Spec') ∧ *)
  (* PurePodStatus.well_formed_uninitialized pod.(Status'). *)

Definition own (c: v1.Pod.t) (v: t): iProp Σ :=
  "%Hown_typemeta" ∷ ⌜ c.(v1.Pod.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hown_objectmeta" ∷ PureObjectMeta.own c.(v1.Pod.ObjectMeta') v.(ObjectMeta') ∗
  "Hown_podspec" ∷ PurePodSpec.own c.(v1.Pod.Spec') v.(Spec') ∗
  "Hown_podstatus" ∷ PurePodStatus.own c.(v1.Pod.Status') v.(Status').
End def.
End PurePod.

Module PureReplicaSetSpec.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  Replicas' : option w32;
  MinReadySeconds' : w32;
  (* Selector' : loc; *)
  (* Template' : v1.PodTemplateSpec.t; *)
}.

Definition own (c: v1.ReplicaSetSpec.t) (v: t): iProp Σ :=
  match v.(Replicas') with
  | None => ⌜ c.(v1.ReplicaSetSpec.Replicas') =  null ⌝
  | Some i => ∃ replicas, c.(v1.ReplicaSetSpec.Replicas') ↦ replicas ∗ ⌜ replicas = i ⌝
  end ∗
  ⌜ c.(v1.ReplicaSetSpec.MinReadySeconds') = v.(MinReadySeconds') ⌝.
End def.
End PureReplicaSetSpec.

Module PureReplicaSetStatus.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {}.
Definition own (c: v1.ReplicaSetStatus.t) (v: t): iProp Σ := True%I.
End def.
End PureReplicaSetStatus.

Module PureReplicaSet.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : PureObjectMeta.t;
  Spec' : PureReplicaSetSpec.t;
  Status' : PureReplicaSetStatus.t;
}.

Definition well_formed (rs: t) : Prop :=
  PureObjectMeta.well_formed rs.(ObjectMeta') ∧
  (∃ (v: w32), rs.(Spec').(PureReplicaSetSpec.Replicas') = Some v ∧ 0 ≤ sint.Z v).

Definition own (c: v1.ReplicaSet.t) (v: t): iProp Σ :=
  ⌜ c.(v1.ReplicaSet.TypeMeta') = v.(TypeMeta') ⌝ ∗
  PureObjectMeta.own c.(v1.ReplicaSet.ObjectMeta') v.(ObjectMeta') ∗
  PureReplicaSetSpec.own c.(v1.ReplicaSet.Spec') v.(Spec') ∗
  PureReplicaSetStatus.own c.(v1.ReplicaSet.Status') v.(Status').
End def.
End PureReplicaSet.

Module KKey.
  Global Instance eq_dec : EqDecision KKey.t.
  Proof. solve_decision. Qed.

  Global Instance countable : Countable KKey.t.
  Proof.
    refine (inj_countable'
              (λ k, (KKey.Kind' k,
                     KKey.Name' k,
                     KKey.Namespace' k))
              (λ '(kind, name, namespace),
                KKey.mk kind name namespace)
              _).
    intros []; reflexivity.
  Qed.
End KKey.

Module PureKObject.
  Inductive t :=
  | Pod (p : PurePod.t)
  | ReplicaSet (rs : PureReplicaSet.t).

  Definition well_formed kobj : Prop :=
    match kobj with
    | Pod p => PurePod.well_formed p
    | ReplicaSet rs => PureReplicaSet.well_formed rs
    end.

  Definition metadata kobj : PureObjectMeta.t :=
    match kobj with
    | Pod p => p.(PurePod.ObjectMeta')
    | ReplicaSet rs => rs.(PureReplicaSet.ObjectMeta')
    end.
End PureKObject.

Global Existing Instance KKey.eq_dec.
Global Existing Instance KKey.countable.
