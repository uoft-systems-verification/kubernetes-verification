Require Export New.proof.sync.
From proof.k8s_io.api.apps Require Export v1_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From proof Require Import prelude empty_ffi.
From proof Require Export deepown.


Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L169 *)
Axiom valid_name: go_string → Prop.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L177 *)
Axiom valid_namespace: go_string → Prop.

Definition well_formed_OwnerReferences (os: list PureOwnerReference.t) : Prop :=
  (* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L92 *)
  ∀ i1 o1 i2 o2,
    os !! i1 = Some o1 ∧ o1.(PureOwnerReference.Controller') = Some true ∧
    os !! i2 = Some o2 ∧ o2.(PureOwnerReference.Controller') = Some true →
      i1 = i2.

(* TODO: translate https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go to spec *)
Definition well_formed_ObjectMeta (m: PureObjectMeta.t) : Prop :=
  (m.(PureObjectMeta.GenerateName') ≠ ""%go → valid_name m.(PureObjectMeta.GenerateName')) ∧
  m.(PureObjectMeta.Name') ≠ ""%go ∧
  valid_name m.(PureObjectMeta.Name') ∧
  m.(PureObjectMeta.Namespace') ≠ ""%go ∧
  valid_namespace m.(PureObjectMeta.Namespace') ∧
  match m.(PureObjectMeta.OwnerReferences') with
  | None => True
  | Some os => well_formed_OwnerReferences os
  end.

Axiom well_formed_PodSpec: PurePodSpec.t → Prop.

Axiom well_formed_PodStatus: PurePodStatus.t → Prop.

Definition well_formed_Pod (pod: PurePod.t) : Prop :=
  well_formed_ObjectMeta pod.(PurePod.ObjectMeta') ∧
  well_formed_PodSpec pod.(PurePod.Spec') ∧
  well_formed_PodStatus pod.(PurePod.Status').

Definition well_formed_to_create_ObjectMeta (m: PureObjectMeta.t) : Prop :=
  (m.(PureObjectMeta.Name') = ""%go → m.(PureObjectMeta.GenerateName') ≠ ""%go) ∧
  match m.(PureObjectMeta.OwnerReferences') with
  | None => True
  | Some os => well_formed_OwnerReferences os
  end.

(* Axiom well_formed_to_create_PodSpec: PurePodSpec.t → Prop.

Axiom well_formed_to_create_PodStatus: PurePodStatus.t → Prop. *)

Definition well_formed_to_create_Pod (pod: PurePod.t) : Prop :=
  well_formed_to_create_ObjectMeta pod.(PurePod.ObjectMeta') ∧
  well_formed_PodSpec pod.(PurePod.Spec') ∧
  well_formed_PodStatus pod.(PurePod.Status').
  (* well_formed_to_create_PodSpec pod.(PurePod.Spec') ∧ *)
  (* well_formed_to_create_PodStatus pod.(PurePod.Status'). *)

Definition well_formed_ReplicaSet (rs: PureReplicaSet.t) : Prop :=
  well_formed_ObjectMeta rs.(PureReplicaSet.ObjectMeta') ∧
  (∃ (v: w32), rs.(PureReplicaSet.Spec').(PureReplicaSetSpec.Replicas') = Some v ∧ 0 ≤ sint.Z v).

End proof.
