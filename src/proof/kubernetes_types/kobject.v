From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export pod persistentvolumeclaim replicaset statefulset deployment.
From New.proof.kubernetes_types Require Import top_level.

Module KObject.
Section def.
Inductive t :=
| Pod (p : v1.Pod.t)
| ReplicaSet (rs : v1.ReplicaSet.t)
| PersistentVolumeClaim (pvc : v1.PersistentVolumeClaim.t)
| StatefulSet (sts : v1.StatefulSet.t)
| Deployment (d : v1.Deployment.t).

Definition typemeta o : v1.TypeMeta.t :=
  match o with
  | Pod p => p.(v1.Pod.TypeMeta')
  | ReplicaSet rs => rs.(v1.ReplicaSet.TypeMeta')
  | PersistentVolumeClaim pvc => pvc.(v1.PersistentVolumeClaim.TypeMeta')
  | StatefulSet sts => sts.(v1.StatefulSet.TypeMeta')
  | Deployment d => d.(v1.Deployment.TypeMeta')
  end.

Definition objectmeta o : v1.ObjectMeta.t :=
  match o with
  | Pod p => p.(v1.Pod.ObjectMeta')
  | ReplicaSet rs => rs.(v1.ReplicaSet.ObjectMeta')
  | PersistentVolumeClaim pvc => pvc.(v1.PersistentVolumeClaim.ObjectMeta')
  | StatefulSet sts => sts.(v1.StatefulSet.ObjectMeta')
  | Deployment d => d.(v1.Deployment.ObjectMeta')
  end.

Definition update_objectmeta o m: t :=
  match o with
  | Pod pod => Pod (pod <| v1.Pod.ObjectMeta' := m |>)
  | ReplicaSet rs => ReplicaSet (rs <| v1.ReplicaSet.ObjectMeta' := m |>)
  | PersistentVolumeClaim pvc => PersistentVolumeClaim (pvc <| v1.PersistentVolumeClaim.ObjectMeta' := m |>)
  | StatefulSet sts => StatefulSet (sts <| v1.StatefulSet.ObjectMeta' := m |>)
  | Deployment d => Deployment (d <| v1.Deployment.ObjectMeta' := m |>)
  end.

End def.
End KObject.

Module ObjectSpecV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Inductive t :=
| PodSpec (p : PodSpecV.t)
| ReplicaSetSpec (rs : ReplicaSetSpecV.t)
| PersistentVolumeClaimSpec (pvc : PersistentVolumeClaimSpecV.t)
| StatefulSetSpec (sts : StatefulSetSpecV.t)
| DeploymentSpec (d : DeploymentSpecV.t).

Definition valid (v : t) : Prop :=
  match v with
  | PodSpec p => PodSpecV.valid p
  | ReplicaSetSpec rs => ReplicaSetSpecV.valid rs
  | PersistentVolumeClaimSpec pvc => PersistentVolumeClaimSpecV.valid pvc
  | StatefulSetSpec sts => StatefulSetSpecV.valid sts
  | DeploymentSpec d => DeploymentSpecV.valid d
  end.

Definition extra_valid (v : t) : Prop :=
  match v with
  | ReplicaSetSpec rs => ReplicaSetSpecV.extra_valid rs
  | _ => True
  end.

(* Admission validation of a spec submitted in a create or update request. *)
Definition valid_create (input : t) : Prop :=
  match input with
  | PodSpec input => PodSpecV.valid_create input
  | ReplicaSetSpec input => ReplicaSetSpecV.valid_create input
  | PersistentVolumeClaimSpec input => PersistentVolumeClaimSpecV.valid_create input
  | StatefulSetSpec input => StatefulSetSpecV.valid_create input
  | DeploymentSpec input => DeploymentSpecV.valid_create input
  end.

(** Top-level update-validation contract over the stored old spec and
    submitted input spec. Each object-specific predicate accounts for any
    preparation relevant to the represented fields. *)
Definition valid_update (old input : t) : Prop :=
  match old, input with
  | PodSpec old, PodSpec input => PodSpecV.valid_update old input
  | ReplicaSetSpec old, ReplicaSetSpec input => ReplicaSetSpecV.valid_update old input
  | PersistentVolumeClaimSpec old, PersistentVolumeClaimSpec input =>
      PersistentVolumeClaimSpecV.valid_update old input
  | StatefulSetSpec old, StatefulSetSpec input => StatefulSetSpecV.valid_update old input
  | DeploymentSpec old, DeploymentSpec input => DeploymentSpecV.valid_update old input
  | _, _ => False
  end.

Global Instance valid_update_dec old input :
  Decision (valid_update old input).
Proof. destruct old, input; simpl; apply _. Defined.

Definition created (input stored : t) : Prop :=
  match input, stored with
  | PodSpec input, PodSpec stored => PodSpecV.created input stored
  | ReplicaSetSpec input, ReplicaSetSpec stored => ReplicaSetSpecV.created input stored
  | PersistentVolumeClaimSpec input, PersistentVolumeClaimSpec stored =>
      PersistentVolumeClaimSpecV.created input stored
  | StatefulSetSpec input, StatefulSetSpec stored => StatefulSetSpecV.created input stored
  | DeploymentSpec input, DeploymentSpec stored => DeploymentSpecV.created input stored
  | _, _ => False
  end.

Definition updated (input stored : t) : Prop :=
  match input, stored with
  | PodSpec input, PodSpec stored => PodSpecV.updated input stored
  | ReplicaSetSpec input, ReplicaSetSpec stored => ReplicaSetSpecV.updated input stored
  | PersistentVolumeClaimSpec input, PersistentVolumeClaimSpec stored =>
      PersistentVolumeClaimSpecV.updated input stored
  | StatefulSetSpec input, StatefulSetSpec stored => StatefulSetSpecV.updated input stored
  | DeploymentSpec input, DeploymentSpec stored => DeploymentSpecV.updated input stored
  | _, _ => False
  end.

Lemma extra_valid_created input stored :
  extra_valid input →
  created input stored →
  extra_valid stored.
Proof.
  destruct input, stored; simpl; try done.
  apply ReplicaSetSpecV.extra_valid_created.
Qed.

Lemma extra_valid_updated old input stored :
  extra_valid old →
  valid_update old input →
  updated input stored →
  extra_valid stored.
Proof.
  destruct old, input, stored; simpl; try done.
  apply ReplicaSetSpecV.extra_valid_updated.
Qed.

Definition deepown_l l v dq: iProp Σ :=
  match v with
  | PodSpec p => ∃ c, l ↦{dq} c ∗ PodSpecV.deepown c p dq
  | ReplicaSetSpec rs => ∃ c, l ↦{dq} c ∗ ReplicaSetSpecV.deepown c rs dq
  | PersistentVolumeClaimSpec pvc => ∃ c, l ↦{dq} c ∗ PersistentVolumeClaimSpecV.deepown c pvc dq
  | StatefulSetSpec sts => ∃ c, l ↦{dq} c ∗ StatefulSetSpecV.deepown c sts dq
  | DeploymentSpec d => ∃ c, l ↦{dq} c ∗ DeploymentSpecV.deepown c d dq
  end.

End def.
End ObjectSpecV.

Module ObjectStatusV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Inductive t :=
| PodStatus (p : PodStatusV.t)
| ReplicaSetStatus (rs : ReplicaSetStatusV.t)
| PersistentVolumeClaimStatus (pvc : PersistentVolumeClaimStatusV.t)
| StatefulSetStatus (sts : StatefulSetStatusV.t)
| DeploymentStatus (d : DeploymentStatusV.t).

Definition valid (v : t) : Prop :=
  match v with
  | PodStatus p => PodStatusV.valid p
  | ReplicaSetStatus rs => ReplicaSetStatusV.valid rs
  | PersistentVolumeClaimStatus pvc => PersistentVolumeClaimStatusV.valid pvc
  | StatefulSetStatus sts => StatefulSetStatusV.valid sts
  | DeploymentStatus d => DeploymentStatusV.valid d
  end.

Axiom valid_create : t → Prop.

(* Status-subresource validation after preparation, including both standalone
   checks on the new status and transition checks against the old status. *)
Definition valid_update (old input : t) : Prop :=
  match old, input with
  | PodStatus old, PodStatus input => PodStatusV.valid_update old input
  | ReplicaSetStatus old, ReplicaSetStatus input => ReplicaSetStatusV.valid_update old input
  | PersistentVolumeClaimStatus old, PersistentVolumeClaimStatus input =>
      PersistentVolumeClaimStatusV.valid_update old input
  | StatefulSetStatus old, StatefulSetStatus input => StatefulSetStatusV.valid_update old input
  | DeploymentStatus old, DeploymentStatus input => DeploymentStatusV.valid_update old input
  | _, _ => False
  end.

Global Instance valid_update_dec old input : Decision (valid_update old input).
Proof. destruct old, input; simpl; apply _. Defined.

Definition created (input stored : t) : Prop :=
  match input, stored with
  | PodStatus input, PodStatus stored => PodStatusV.created input stored
  | ReplicaSetStatus input, ReplicaSetStatus stored => ReplicaSetStatusV.created input stored
  | PersistentVolumeClaimStatus input, PersistentVolumeClaimStatus stored =>
    PersistentVolumeClaimStatusV.created input stored
  | StatefulSetStatus input, StatefulSetStatus stored => StatefulSetStatusV.created input stored
  | DeploymentStatus input, DeploymentStatus stored => DeploymentStatusV.created input stored
  | _, _ => False
  end.

Definition updated (input stored : t) : Prop :=
  match input, stored with
  | PodStatus input, PodStatus stored => PodStatusV.updated input stored
  | ReplicaSetStatus input, ReplicaSetStatus stored => ReplicaSetStatusV.updated input stored
  | PersistentVolumeClaimStatus input, PersistentVolumeClaimStatus stored =>
      PersistentVolumeClaimStatusV.updated input stored
  | StatefulSetStatus input, StatefulSetStatus stored => StatefulSetStatusV.updated input stored
  | DeploymentStatus input, DeploymentStatus stored => DeploymentStatusV.updated input stored
  | _, _ => False
  end.

Definition deepown_l l v dq: iProp Σ :=
  match v with
  | PodStatus p => ∃ c, l ↦{dq} c ∗ PodStatusV.deepown c p dq
  | ReplicaSetStatus rs => ∃ c, l ↦{dq} c ∗ ReplicaSetStatusV.deepown c rs dq
  | PersistentVolumeClaimStatus pvc => ∃ c, l ↦{dq} c ∗ PersistentVolumeClaimStatusV.deepown c pvc dq
  | StatefulSetStatus sts => ∃ c, l ↦{dq} c ∗ StatefulSetStatusV.deepown c sts dq
  | DeploymentStatus d => ∃ c, l ↦{dq} c ∗ DeploymentStatusV.deepown c d dq
  end.

End def.
End ObjectStatusV.

Module KObjectV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Inductive t :=
| Pod (p : PodV.t)
| ReplicaSet (rs : ReplicaSetV.t)
| PersistentVolumeClaim (pvc : PersistentVolumeClaimV.t)
| StatefulSet (sts : StatefulSetV.t)
| Deployment (d : DeploymentV.t).

(** These are Go interface-membership facts, not method-call specifications.
    [go.type_set_contains] consults the semantic [method_set], while the
    generated [MethodUnfold] instances for direct and promoted methods constrain
    only method execution. The current generated package assumptions do not
    connect those two parts of the semantics, so these facts cannot yet be
    derived from them. Remove this class once Goose generates signature-bearing
    method-set lookup facts. *)
Class ObjectInterfaceAssumptions : Prop := {
  pod_is_object :
    go.type_set_contains (go.PointerType v1.Pod) v1.Object = true;
  replicaset_is_object :
    go.type_set_contains (go.PointerType v1.ReplicaSet) v1.Object = true;
  persistentvolumeclaim_is_object :
    go.type_set_contains (go.PointerType v1.PersistentVolumeClaim) v1.Object = true;
  statefulset_is_object :
    go.type_set_contains (go.PointerType v1.StatefulSet) v1.Object = true;
  deployment_is_object :
    go.type_set_contains (go.PointerType v1.Deployment) v1.Object = true;
}.

Definition typemeta o : v1.TypeMeta.t :=
  match o with
  | Pod p => p.(PodV.TypeMeta')
  | ReplicaSet rs => rs.(ReplicaSetV.TypeMeta')
  | PersistentVolumeClaim pvc => pvc.(PersistentVolumeClaimV.TypeMeta')
  | StatefulSet sts => sts.(StatefulSetV.TypeMeta')
  | Deployment d => d.(DeploymentV.TypeMeta')
  end.

Definition objectmeta o : ObjectMetaV.t :=
  match o with
  | Pod p => p.(PodV.ObjectMeta')
  | ReplicaSet rs => rs.(ReplicaSetV.ObjectMeta')
  | PersistentVolumeClaim pvc => pvc.(PersistentVolumeClaimV.ObjectMeta')
  | StatefulSet sts => sts.(StatefulSetV.ObjectMeta')
  | Deployment d => d.(DeploymentV.ObjectMeta')
  end.

Definition spec o: ObjectSpecV.t :=
  match o with
  | Pod p => ObjectSpecV.PodSpec p.(PodV.Spec')
  | ReplicaSet rs => ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')
  | PersistentVolumeClaim pvc => ObjectSpecV.PersistentVolumeClaimSpec pvc.(PersistentVolumeClaimV.Spec')
  | StatefulSet sts => ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')
  | Deployment d => ObjectSpecV.DeploymentSpec d.(DeploymentV.Spec')
  end.

Definition status o: ObjectStatusV.t :=
  match o with
  | Pod p => ObjectStatusV.PodStatus p.(PodV.Status')
  | ReplicaSet rs => ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status')
  | PersistentVolumeClaim pvc => ObjectStatusV.PersistentVolumeClaimStatus pvc.(PersistentVolumeClaimV.Status')
  | StatefulSet sts => ObjectStatusV.StatefulSetStatus sts.(StatefulSetV.Status')
  | Deployment d => ObjectStatusV.DeploymentStatus d.(DeploymentV.Status')
  end.

Definition kind o : go_string :=
  match o with
  | Pod _ => PodV.kind
  | ReplicaSet _ => ReplicaSetV.kind
  | PersistentVolumeClaim _ => PersistentVolumeClaimV.kind
  | StatefulSet _ => StatefulSetV.kind
  | Deployment _ => DeploymentV.kind
  end.

Definition same_kind (o1 o2 : t) : Prop :=
  match o1, o2 with
  | Pod _, Pod _ => True
  | ReplicaSet _, ReplicaSet _ => True
  | PersistentVolumeClaim _, PersistentVolumeClaim _ => True
  | StatefulSet _, StatefulSet _ => True
  | Deployment _, Deployment _ => True
  | _, _ => False
  end.

Definition key o : KKey.t :=
  {|
    KKey.Kind' := (kind o);
    KKey.Namespace' := (objectmeta o).(ObjectMetaV.Namespace');
    KKey.Name' := (objectmeta o).(ObjectMetaV.Name')
  |}.

Definition update_objectmeta o m: t :=
  match o with
  | Pod pod => Pod (pod <| PodV.ObjectMeta' := m |>)
  | ReplicaSet rs => ReplicaSet (rs <| ReplicaSetV.ObjectMeta' := m |>)
  | PersistentVolumeClaim pvc => PersistentVolumeClaim (pvc <| PersistentVolumeClaimV.ObjectMeta' := m |>)
  | StatefulSet sts => StatefulSet (sts <| StatefulSetV.ObjectMeta' := m |>)
  | Deployment d => Deployment (d <| DeploymentV.ObjectMeta' := m |>)
  end.

(** [input] is the submitted create request.
    [stored] is the object stored after the successful create. *)
Definition created namespace input stored : Prop :=
  match input, stored with
  | Pod input_pod, Pod stored_pod => PodV.created namespace input_pod stored_pod
  | ReplicaSet input_rs, ReplicaSet stored_rs => ReplicaSetV.created namespace input_rs stored_rs
  | PersistentVolumeClaim input_pvc, PersistentVolumeClaim stored_pvc =>
      PersistentVolumeClaimV.created namespace input_pvc stored_pvc
  | StatefulSet input_sts, StatefulSet stored_sts =>
      StatefulSetV.created namespace input_sts stored_sts
  | Deployment input_d, Deployment stored_d =>
      DeploymentV.created namespace input_d stored_d
  | _, _ => False
  end.

(** End-to-end relation between the submitted object and the stored result of
    a successful update. This relation does not constrain the stored status. *)
Definition updated input stored : Prop :=
  match input, stored with
  | Pod input_pod, Pod stored_pod => PodV.updated input_pod stored_pod
  | ReplicaSet input_rs, ReplicaSet stored_rs => ReplicaSetV.updated input_rs stored_rs
  | PersistentVolumeClaim input_pvc, PersistentVolumeClaim stored_pvc =>
      PersistentVolumeClaimV.updated input_pvc stored_pvc
  | StatefulSet input_sts, StatefulSet stored_sts => StatefulSetV.updated input_sts stored_sts
  | Deployment input_d, Deployment stored_d => DeploymentV.updated input_d stored_d
  | _, _ => False
  end.

(** [input] is the submitted status update.
    [stored] is the object stored after the successful status update.
    This is a relation because the current views omit fields that can affect
    the exact stored value. *)
Definition status_updated input stored : Prop :=
  match input, stored with
  | Pod input, Pod stored => PodV.status_updated input stored
  | ReplicaSet input, ReplicaSet stored => ReplicaSetV.status_updated input stored
  | PersistentVolumeClaim input, PersistentVolumeClaim stored =>
      PersistentVolumeClaimV.status_updated input stored
  | StatefulSet input, StatefulSet stored => StatefulSetV.status_updated input stored
  | Deployment input, Deployment stored => DeploymentV.status_updated input stored
  | _, _ => False
  end.

Lemma kind_update_objectmeta :
  ∀ o m, kind (update_objectmeta o m) = kind o.
Proof. destruct o; done. Qed.

Lemma typemeta_update_objectmeta :
  ∀ o m, typemeta (update_objectmeta o m) = typemeta o.
Proof. destruct o; done. Qed.

Lemma spec_update_objectmeta :
  ∀ o m, spec (update_objectmeta o m) = spec o.
Proof. destruct o; done. Qed.

Lemma status_update_objectmeta :
  ∀ o m, status (update_objectmeta o m) = status o.
Proof. destruct o; done. Qed.

(* Controller-implementation requirements that are not guaranteed by API
   admission. The authoritative Kubernetes model deliberately ranges only over
   stored objects satisfying this predicate as well as [valid]. *)
Definition extra_valid o : Prop :=
  ObjectSpecV.extra_valid (spec o).

Lemma extra_valid_update_objectmeta o m :
  extra_valid o →
  extra_valid (update_objectmeta o m).
Proof. rewrite /extra_valid spec_update_objectmeta //. Qed.

(* [valid] is the complete invariant guaranteed for an object stored by the
   API server. *)
Definition valid o : Prop :=
  valid_typemeta (kind o) (typemeta o) ∧
  valid_resource_version (objectmeta o).(ObjectMetaV.ResourceVersion') ∧
  ObjectMetaV.valid (kind o) (objectmeta o) ∧
  ObjectSpecV.valid (spec o) ∧
  ObjectStatusV.valid (status o).

(** [input] is the object submitted in the create request.

    The create strategies for every resource currently represented by [t]
    (Pod, PersistentVolumeClaim, ReplicaSet, StatefulSet, and Deployment) reset the
    submitted status before validation, so their create predicates impose no
    condition on the input status. Kubernetes permits and validates a Node's
    status on create, which can be expressed in [NodeV.valid_create] if Node is
    added here. Empty TypeMeta kind/apiVersion fields are valid: the create
    request decoder defaults them from the REST endpoint before validation.
    See https://github.com/kubernetes/kubernetes/blob/master/pkg/registry/core/node/strategy.go. *)
Definition valid_create request_kind namespace input : Prop :=
  match input with
  | Pod input => PodV.valid_create request_kind namespace input
  | ReplicaSet input => ReplicaSetV.valid_create request_kind namespace input
  | PersistentVolumeClaim input => PersistentVolumeClaimV.valid_create request_kind namespace input
  | StatefulSet input => StatefulSetV.valid_create request_kind namespace input
  | Deployment input => DeploymentV.valid_create request_kind namespace input
  end.

(** Top-level update-validation contract.
    [request_kind] and [namespace] identify the update request.
    [old_meta] and [old_spec] are the metadata and spec currently in etcd.
    [input] is the object submitted in the update request. *)
Definition valid_update request_kind namespace old_meta old_spec input : Prop :=
  match old_spec, input with
  | ObjectSpecV.PodSpec old_spec, Pod input =>
      PodV.valid_update request_kind namespace old_meta old_spec input
  | ObjectSpecV.ReplicaSetSpec old_spec, ReplicaSet input =>
      ReplicaSetV.valid_update request_kind namespace old_meta old_spec input
  | ObjectSpecV.PersistentVolumeClaimSpec old_spec, PersistentVolumeClaim input =>
      PersistentVolumeClaimV.valid_update request_kind namespace old_meta old_spec input
  | ObjectSpecV.StatefulSetSpec old_spec, StatefulSet input =>
      StatefulSetV.valid_update request_kind namespace old_meta old_spec input
  | ObjectSpecV.DeploymentSpec old_spec, Deployment input =>
      DeploymentV.valid_update request_kind namespace old_meta old_spec input
  | _, _ => False
  end.

(** Top-level status-update validation contract.
    [old_meta] and [old_status] are the metadata and status currently in etcd.
    [input] is the object submitted in the status-update request. *)
Definition valid_status_update request_kind namespace old_meta old_status input : Prop :=
  match old_status, input with
  | ObjectStatusV.PodStatus old_status, Pod input =>
      PodV.valid_status_update request_kind namespace old_meta old_status input
  | ObjectStatusV.ReplicaSetStatus old_status, ReplicaSet input =>
      ReplicaSetV.valid_status_update request_kind namespace old_meta old_status input
  | ObjectStatusV.PersistentVolumeClaimStatus old_status, PersistentVolumeClaim input =>
      PersistentVolumeClaimV.valid_status_update request_kind namespace old_meta old_status input
  | ObjectStatusV.StatefulSetStatus old_status, StatefulSet input =>
      StatefulSetV.valid_status_update request_kind namespace old_meta old_status input
  | ObjectStatusV.DeploymentStatus old_status, Deployment input =>
      DeploymentV.valid_status_update request_kind namespace old_meta old_status input
  | _, _ => False
  end.

Definition valid2 o : Prop :=
  match o with
  | Pod p => PodV.valid p
  | ReplicaSet rs => ReplicaSetV.valid rs
  | PersistentVolumeClaim pvc => PersistentVolumeClaimV.valid pvc
  | StatefulSet sts => StatefulSetV.valid sts
  | Deployment d => DeploymentV.valid d
  end.

Lemma valid_eq_valid2 o :
  valid o = valid2 o.
Proof.
  destruct o as [[tm meta spec status]|[tm meta spec status]|
    [tm meta spec status]|[tm meta spec status]|[tm meta spec status]];
    rewrite /valid /valid2 /PodV.valid /ReplicaSetV.valid
      /PersistentVolumeClaimV.valid /StatefulSetV.valid /DeploymentV.valid
      /ObjectSpecV.valid /ObjectStatusV.valid /=; done.
Qed.

Definition valid_without_meta o : Prop :=
  match o with
  | Pod p => PodV.valid_without_meta p
  | ReplicaSet rs => ReplicaSetV.valid_without_meta rs
  | PersistentVolumeClaim pvc => PersistentVolumeClaimV.valid_without_meta pvc
  | StatefulSet sts => StatefulSetV.valid_without_meta sts
  | Deployment d => DeploymentV.valid_without_meta d
  end.

Definition deepown_l l v dq: iProp Σ :=
  match v with
  | Pod v => PodV.deepown_l l v dq
  | ReplicaSet v => ReplicaSetV.deepown_l l v dq
  | PersistentVolumeClaim v => PersistentVolumeClaimV.deepown_l l v dq
  | StatefulSet v => StatefulSetV.deepown_l l v dq
  | Deployment v => DeploymentV.deepown_l l v dq
  end.

#[global]
Instance top_level_instance : top_level Σ t :=
  Build_top_level Σ t ObjectMetaV.t ObjectSpecV.t ObjectStatusV.t
    valid
    extra_valid
    valid_create
    valid_update
    valid_status_update
    created
    updated
    status_updated
    deepown_l.

Definition deepown_l_without_meta l v dq: iProp Σ :=
  match v with
  | Pod v => PodV.deepown_l_without_meta l v dq
  | ReplicaSet v => ReplicaSetV.deepown_l_without_meta l v dq
  | PersistentVolumeClaim v => PersistentVolumeClaimV.deepown_l_without_meta l v dq
  | StatefulSet v => StatefulSetV.deepown_l_without_meta l v dq
  | Deployment v => DeploymentV.deepown_l_without_meta l v dq
  end.

Definition valid_interface i (l: loc) v: Prop :=
  match v with
  | Pod _ =>
      i = interface.mk (go.PointerType v1.Pod) #l ∧
      go.type_set_contains (go.PointerType v1.Pod) v1.Object = true
  | ReplicaSet _ =>
      i = interface.mk (go.PointerType v1.ReplicaSet) #l ∧
      go.type_set_contains (go.PointerType v1.ReplicaSet) v1.Object = true
  | PersistentVolumeClaim _ =>
      i = interface.mk (go.PointerType v1.PersistentVolumeClaim) #l ∧
      go.type_set_contains (go.PointerType v1.PersistentVolumeClaim) v1.Object = true
  | StatefulSet _ =>
      i = interface.mk (go.PointerType v1.StatefulSet) #l ∧
      go.type_set_contains (go.PointerType v1.StatefulSet) v1.Object = true
  | Deployment _ =>
      i = interface.mk (go.PointerType v1.Deployment) #l ∧
      go.type_set_contains (go.PointerType v1.Deployment) v1.Object = true
  end.

Definition deepown_i i v dq: iProp Σ :=
  ∃ l, ⌜ valid_interface i l v ⌝ ∗ deepown_l l v dq.

Section object_interface_assumptions.
Context `{object_interface_sem : !ObjectInterfaceAssumptions}.

Lemma valid_interface_Pod l p :
  valid_interface (interface.mk (go.PointerType v1.Pod) #l) l (Pod p).
Proof using object_interface_sem. split; [done|apply pod_is_object]. Qed.

Lemma valid_interface_ReplicaSet l rs :
  valid_interface (interface.mk (go.PointerType v1.ReplicaSet) #l) l
    (ReplicaSet rs).
Proof using object_interface_sem. split; [done|apply replicaset_is_object]. Qed.

Lemma valid_interface_PersistentVolumeClaim l pvc :
  valid_interface (interface.mk (go.PointerType v1.PersistentVolumeClaim) #l) l
    (PersistentVolumeClaim pvc).
Proof using object_interface_sem.
  split; [done|apply persistentvolumeclaim_is_object].
Qed.

Lemma valid_interface_StatefulSet l sts :
  valid_interface (interface.mk (go.PointerType v1.StatefulSet) #l) l
    (StatefulSet sts).
Proof using object_interface_sem. split; [done|apply statefulset_is_object]. Qed.

Lemma valid_interface_Deployment l d :
  valid_interface (interface.mk (go.PointerType v1.Deployment) #l) l
    (Deployment d).
Proof using object_interface_sem. split; [done|apply deployment_is_object]. Qed.

End object_interface_assumptions.

Definition typemeta_ptr l v: loc :=
  match v with
  | Pod _ => struct_field_ref v1.Pod.t "TypeMeta" l
  | ReplicaSet _ => struct_field_ref v1.ReplicaSet.t "TypeMeta" l
  | PersistentVolumeClaim _ => struct_field_ref v1.PersistentVolumeClaim.t "TypeMeta" l
  | StatefulSet _ => struct_field_ref v1.StatefulSet.t "TypeMeta" l
  | Deployment _ => struct_field_ref v1.Deployment.t "TypeMeta" l
  end.

Definition objectmeta_ptr l v: loc :=
  match v with
  | Pod _ => struct_field_ref v1.Pod.t "ObjectMeta" l
  | ReplicaSet _ => struct_field_ref v1.ReplicaSet.t "ObjectMeta" l
  | PersistentVolumeClaim _ => struct_field_ref v1.PersistentVolumeClaim.t "ObjectMeta" l
  | StatefulSet _ => struct_field_ref v1.StatefulSet.t "ObjectMeta" l
  | Deployment _ => struct_field_ref v1.Deployment.t "ObjectMeta" l
  end.

Definition spec_ptr l v: loc :=
  match v with
  | Pod _ => struct_field_ref v1.Pod.t "Spec" l
  | ReplicaSet _ => struct_field_ref v1.ReplicaSet.t "Spec" l
  | PersistentVolumeClaim _ => struct_field_ref v1.PersistentVolumeClaim.t "Spec" l
  | StatefulSet _ => struct_field_ref v1.StatefulSet.t "Spec" l
  | Deployment _ => struct_field_ref v1.Deployment.t "Spec" l
  end.

Definition status_ptr l v: loc :=
  match v with
  | Pod _ => struct_field_ref v1.Pod.t "Status" l
  | ReplicaSet _ => struct_field_ref v1.ReplicaSet.t "Status" l
  | PersistentVolumeClaim _ => struct_field_ref v1.PersistentVolumeClaim.t "Status" l
  | StatefulSet _ => struct_field_ref v1.StatefulSet.t "Status" l
  | Deployment _ => struct_field_ref v1.Deployment.t "Status" l
  end.

End def.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Lemma deepown_l_split l v dq:
  deepown_l l v dq ⊢
    ⌜ l ≠ null ⌝ ∗
    (typemeta_ptr l v) ↦{dq} (typemeta v) ∗
    ObjectMetaV.deepown_l (objectmeta_ptr l v) (objectmeta v) dq ∗
    ObjectSpecV.deepown_l (spec_ptr l v) (spec v) dq ∗
    ObjectStatusV.deepown_l (status_ptr l v) (status v) dq.
Proof.
  destruct v as [p|rs|pvc|sts|d]; simpl.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply PodV.deepown_l_split.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply ReplicaSetV.deepown_l_split.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply PersistentVolumeClaimV.deepown_l_split.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply StatefulSetV.deepown_l_split.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply DeploymentV.deepown_l_split.
Qed.

(* TODO: deepown_l_merge is only used for merging updated objectmeta; generalize it later *)
Lemma deepown_l_merge l v vm dq:
  l ≠ null →
  (typemeta_ptr l v) ↦{dq} (typemeta v) ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l v) vm dq ∗
  ObjectSpecV.deepown_l (spec_ptr l v) (spec v) dq ∗
  ObjectStatusV.deepown_l (status_ptr l v) (status v) dq ⊢
    deepown_l l (update_objectmeta v vm) dq.
Proof.
  intros Hnot_null.
  destruct v as [p|rs|pvc|sts|d]; simpl.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (PodV.deepown_l_merge l p vm dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (ReplicaSetV.deepown_l_merge l rs vm dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (PersistentVolumeClaimV.deepown_l_merge l pvc vm dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (StatefulSetV.deepown_l_merge l sts vm dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (DeploymentV.deepown_l_merge l d vm dq Hnot_null).
Qed.

Lemma deepown_l_restore l v dq:
  l ≠ null →
  (typemeta_ptr l v) ↦{dq} (typemeta v) ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l v) (objectmeta v) dq ∗
  ObjectSpecV.deepown_l (spec_ptr l v) (spec v) dq ∗
  ObjectStatusV.deepown_l (status_ptr l v) (status v) dq ⊢
    deepown_l l v dq.
Proof.
  intros Hnot_null.
  destruct v as [p|rs|pvc|sts|d]; simpl.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (PodV.deepown_l_restore l p dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (ReplicaSetV.deepown_l_restore l rs dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (PersistentVolumeClaimV.deepown_l_restore l pvc dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (StatefulSetV.deepown_l_restore l sts dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (DeploymentV.deepown_l_restore l d dq Hnot_null).
Qed.

Lemma deepown_i_yields_deepown_l i l v dq:
  deepown_i i v dq ∗ ⌜ valid_interface i l v ⌝ -∗
    deepown_l l v dq.
Proof.
  iIntros "[Hdeepown_i %Hvalid]".
  iDestruct "Hdeepown_i" as (l') "[%Hvalid' Hdeepown_l]".
  destruct v; simpl in *;
  destruct Hvalid as [Hvalid _];
  destruct Hvalid' as [Hvalid' _];
  subst i;
  simplify_eq;
  done.
Qed.

Lemma valid_create_pod_set_name pod request_kind namespace name :
  valid_create request_kind namespace (Pod pod) →
  name ≠ ""%go →
  valid_name PodV.kind name →
  valid_create request_kind namespace
    (Pod (PodV.update_objectmeta pod
      (pod.(PodV.ObjectMeta') <| ObjectMetaV.Name' := name |>))).
Proof.
  rewrite /valid_create /=.
  intros (Hkind & Hns_nonempty & Hns_valid & Htypemeta & Hmeta & Hspec)
    Hname_nonempty Hname_valid.
  assert (ObjectMetaV.valid_create PodV.kind namespace
      (pod.(PodV.ObjectMeta') <| ObjectMetaV.Name' := name |>)) as Hmeta_named.
  { unfold ObjectMetaV.valid_create in Hmeta |- *.
    simpl. destruct (decide (name = ""%go)) as [Hname_empty | Hname_ne];
      first contradiction.
    destruct (decide (pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = ""%go));
      simpl in Hmeta;
      destruct Hmeta as ((Hgenerate_name & _) & Hrest).
    - split; [split; [intros _; exact Hgenerate_name|exact Hname_valid]|exact Hrest].
    - split; [split; [exact Hgenerate_name|exact Hname_valid]|exact Hrest]. }
  split_and!; done.
Qed.

End proof.
End KObjectV.

Global Instance key_eq_dec : EqDecision KKey.t.
Proof. solve_decision. Qed.

Global Instance key_countable : Countable KKey.t.
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

Global Instance key_uid_eq_dec : EqDecision (KKey.t * types.UID.t).
Proof. solve_decision. Qed.

Global Instance key_uid_countable : Countable (KKey.t * types.UID.t).
Proof.
  refine (inj_countable'
            (λ '(k, uid), (KKey.Kind' k,
                           KKey.Name' k,
                           KKey.Namespace' k,
                           uid))
            (λ '(kind, name, namespace, uid),
              (KKey.mk kind name namespace, uid))
            _).
  intros [[] ?]; reflexivity.
Qed.

Definition meta_parent_ref meta : option (KKey.t * types.UID.t) :=
  match meta.(ObjectMetaV.OwnerReferences') with
  | Some orefs => match list_find (λ oref, oref.(OwnerReferenceV.Controller') = Some true) orefs with
    | Some (_, oref) => Some (
                          {|
                            KKey.Kind' := oref.(OwnerReferenceV.Kind');
                            KKey.Namespace' := meta.(ObjectMetaV.Namespace');
                            KKey.Name' := oref.(OwnerReferenceV.Name');
                          |},
                          oref.(OwnerReferenceV.UID')
                        )
    | None => None
    end
  | None => None
  end.


Definition meta_parent_ref_is meta kind name uid : Prop :=
  meta_parent_ref meta = Some ({|
                                KKey.Kind' := kind;
                                KKey.Namespace' := meta.(ObjectMetaV.Namespace');
                                KKey.Name' := name;
                              |}, uid).

Definition obj_parent_ref obj : option (KKey.t * types.UID.t) :=
  meta_parent_ref (KObjectV.objectmeta obj).

Definition obj_parent_ref_is obj kind name uid : Prop :=
  meta_parent_ref_is (KObjectV.objectmeta obj) kind name uid.

Definition obj_ref k obj : KKey.t * types.UID.t :=
  (k, (KObjectV.objectmeta obj).(ObjectMetaV.UID')).

Definition no_speculative_parent_reference meta (used_uid: gset types.UID.t): Prop :=
  ∀ kind name uid, meta_parent_ref_is meta kind name uid → uid ∈ used_uid.

Definition is_controller_parent_of (o: OwnerReferenceV.t) kind name uid : Prop :=
  o.(OwnerReferenceV.Controller') = Some true ∧
  o.(OwnerReferenceV.Kind') = kind ∧
  o.(OwnerReferenceV.Name') = name ∧
  o.(OwnerReferenceV.UID') = uid.

Global Instance is_controller_parent_of_dec o kind name uid :
  Decision (is_controller_parent_of o kind name uid).
Proof.
  unfold is_controller_parent_of.
  repeat apply and_dec; apply _.
Qed.

Definition os_has_controller_parent_of (os: list OwnerReferenceV.t) kind name uid : Prop :=
  ∃ o, o ∈ os ∧ is_controller_parent_of o kind name uid.

Global Instance os_has_controller_parent_of_dec os kind name uid :
  Decision (os_has_controller_parent_of os kind name uid).
Proof.
  unfold os_has_controller_parent_of.
  apply list_exist_dec. intros o.
  apply and_dec; apply _.
Qed.

Definition obj_has_controller_parent_of child kind name uid: Prop :=
  match (KObjectV.objectmeta child).(ObjectMetaV.OwnerReferences') with
  | Some os => os_has_controller_parent_of os kind name uid
  | None => False
  end.

Global Instance obj_has_controller_parent_of_dec child kind name uid :
  Decision (obj_has_controller_parent_of child kind name uid).
Proof.
  unfold obj_has_controller_parent_of.
  destruct ((KObjectV.objectmeta child).(ObjectMetaV.OwnerReferences')); apply _.
Qed.

Lemma valid_object_has_valid_objectmeta obj:
  KObjectV.valid2 obj →
    ObjectMetaV.valid (KObjectV.kind obj) (KObjectV.objectmeta obj).
Proof.
  rewrite -KObjectV.valid_eq_valid2.
  intros (_ & _ & Hmeta & _ & _). exact Hmeta.
Qed.

Lemma valid_object_has_valid_key key obj:
  key = KObjectV.key obj →
  KObjectV.valid2 obj →
    key.(KKey.Name') ≠ ""%go ∧
    valid_name key.(KKey.Kind') key.(KKey.Name') ∧
    key.(KKey.Namespace') ≠ ""%go ∧
    valid_namespace key.(KKey.Namespace').
Proof.
  intros Hkey Hwf.
  apply valid_object_has_valid_objectmeta in Hwf.
  destruct obj; simpl in *; subst key; simpl;
  destruct Hwf as [_ [Hname_ne [Hname_valid [Hns_ne Hns_valid]]]];
  destruct Hns_valid as [Hns_valid _];
  exact (conj Hname_ne (conj Hname_valid (conj Hns_ne Hns_valid))).
Qed.

Lemma valid_owner_references_has_at_most_one_controller_parent os:
  OwnerReferenceV.list_valid os →
    ∀ kind1 name1 uid1 kind2 name2 uid2,
      os_has_controller_parent_of os kind1 name1 uid1 →
        os_has_controller_parent_of os kind2 name2 uid2 →
          kind1 = kind2 ∧ name1 = name2 ∧ uid1 = uid2.
Proof.
  intros Hwf kind1 name1 uid1 kind2 name2 uid2 H1 H2.
  unfold os_has_controller_parent_of in H1, H2.
  destruct H1 as (o1 & Hin1 & Hctrl1).
  destruct H2 as (o2 & Hin2 & Hctrl2).
  unfold is_controller_parent_of in Hctrl1, Hctrl2.
  destruct Hctrl1 as (Hctrl1_c & Hkind1 & Hname1 & Huid1).
  destruct Hctrl2 as (Hctrl2_c & Hkind2 & Hname2 & Huid2).
  apply list_elem_of_lookup_1 in Hin1 as [i1 Hlookup1].
  apply list_elem_of_lookup_1 in Hin2 as [i2 Hlookup2].
  unfold OwnerReferenceV.list_valid in Hwf.
  assert (i1 = i2) as Heq.
  { apply (Hwf i1 o1 i2 o2).
    split; [|split; [|split]]; assumption. }
  subst i2.
  rewrite Hlookup1 in Hlookup2.
  injection Hlookup2 as ->.
  split.
  - rewrite <- Hkind1. exact Hkind2.
  - split.
    + rewrite <- Hname1. exact Hname2.
    + rewrite <- Huid1. exact Huid2.
Qed.

Lemma valid_obj_has_at_most_one_controller_parent obj:
  KObjectV.valid2 obj →
    ∀ kind1 name1 uid1 kind2 name2 uid2,
      obj_has_controller_parent_of obj kind1 name1 uid1 →
        obj_has_controller_parent_of obj kind2 name2 uid2 →
          kind1 = kind2 ∧ name1 = name2 ∧ uid1 = uid2.
Proof.
  intros Hwf kind1 name1 uid1 kind2 name2 uid2 H1 H2.
  unfold obj_has_controller_parent_of in H1, H2.
  apply valid_object_has_valid_objectmeta in Hwf.
  assert (valid_owner_references
      (KObjectV.objectmeta obj).(ObjectMetaV.OwnerReferences')) as Hwf_ownerref.
  { unfold ObjectMetaV.valid in Hwf. tauto. }
  destruct (ObjectMetaV.OwnerReferences' (KObjectV.objectmeta obj)) as [os|]; simpl in H1, H2, Hwf_ownerref.
  - unfold valid_owner_references in Hwf_ownerref. simpl in Hwf_ownerref.
    assert (OwnerReferenceV.list_valid os) as Hwf_list.
    { intros i1 o1 i2 o2 (Hlookup1 & Hctrl1 & Hlookup2 & Hctrl2).
      destruct Hwf_ownerref as [Hunique _].
      eauto.
    }
    apply valid_owner_references_has_at_most_one_controller_parent with (os := os); assumption.
  - contradiction.
Qed.

(* Use this when the goal is to prove [KObjectV.valid] for an object obtained by
   [KObjectV.update_objectmeta]. The parameters are expected to be:
   - [Hvalid_typemeta]: typemeta validity of the pre-update object.
   - [Hvalid_rv]: validity of the replacement metadata's resource version.
   - [Hvalid_meta]: validity of the replacement objectmeta.
   - [Hvalid_spec]: validity of the object's spec before the objectmeta update.
   - [Hvalid_status]: validity of the object's status before the objectmeta
     update.
   The tactic combines these to rebuild [KObjectV.valid] for the updated object,
   reusing [KObjectV.spec_update_objectmeta] and
   [KObjectV.status_update_objectmeta]. In practice this is most convenient
   after destructing the concrete object constructors so [simpl] exposes the
   required equalities. *)
Ltac solve_update_objectmeta_valid
    Hvalid_typemeta Hvalid_rv Hvalid_meta Hvalid_spec Hvalid_status :=
  split_and!;
    [ rewrite KObjectV.kind_update_objectmeta;
      rewrite KObjectV.typemeta_update_objectmeta;
      exact Hvalid_typemeta
    | simpl; exact Hvalid_rv
    | rewrite KObjectV.kind_update_objectmeta; exact Hvalid_meta
    | rewrite KObjectV.spec_update_objectmeta; exact Hvalid_spec
    | rewrite KObjectV.status_update_objectmeta; exact Hvalid_status
    ].
