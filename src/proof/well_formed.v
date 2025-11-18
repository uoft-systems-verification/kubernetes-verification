Require Export New.proof.sync.
From proof.k8s_io.api.apps Require Export v1_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From proof Require Import prelude empty_ffi.
From proof Require Export deepcopy.


Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Definition object_meta_well_formed (m: v1.ObjectMeta.t) : iProp Σ :=
  ⌜ m.(v1.ObjectMeta.UID') ≠ "_ORPHAN_POD"%go ⌝.

Definition pod_well_formed (pod: v1.Pod.t) : iProp Σ :=
  object_meta_well_formed pod.(v1.Pod.ObjectMeta').

Axiom pod_well_formed_for_creation: v1.Pod.t → iProp Σ.

Definition pod_nn_well_formed (pod: v1.Pod.t) (namespace name: go_string) : iProp Σ :=
  ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ⌝ ∗
  ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name') = name ⌝ ∗
  pod_well_formed pod.

Definition replicaset_well_formed (rs: v1.ReplicaSet.t) : iProp Σ :=
  object_meta_well_formed rs.(v1.ReplicaSet.ObjectMeta') ∗
  ∃ (v: w32), rs.(v1.ReplicaSet.Spec').(v1.ReplicaSetSpec.Replicas') ↦ v ∗ ⌜ 0 ≤ sint.Z v ⌝.

Definition replicaset_nn_well_formed (rs: v1.ReplicaSet.t) (namespace name: go_string) : iProp Σ :=
  ⌜ rs.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ⌝ ∗
  ⌜ rs.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Name') = name ⌝ ∗
  replicaset_well_formed rs.

Lemma well_formed_preserved_by_deepcopy_ReplicaSet rs1 rs2 namespace name:
  deepcopy_ReplicaSet rs1 rs2 -∗
    replicaset_nn_well_formed rs1 namespace name -∗
      deepcopy_ReplicaSet rs1 rs2 ∗
      replicaset_nn_well_formed rs1 namespace name ∗
      replicaset_nn_well_formed rs2 namespace name.
Proof.
Admitted.

End proof.