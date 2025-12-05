Require Export New.proof.sync.
From proof.k8s_io.api.apps Require Export v1_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From proof Require Import prelude empty_ffi.
From proof Require Export deepcopy.


Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Definition has_controller_parent (oslice: slice.t) (os: list v1.OwnerReference.t) (o: v1.OwnerReference.t) (c: bool) : iProp Σ :=
  oslice ↦*□ os ∗ ⌜ o ∈ os ⌝ ∗ o.(v1.OwnerReference.Controller') ↦□ c ∗ ⌜ c = true ⌝.

Definition has_controller_parent_of (oslice: slice.t) (uid: go_string) : iProp Σ :=
  ∃ os o c, has_controller_parent oslice os o c ∗ ⌜ o.(v1.OwnerReference.UID') = uid ⌝.

Definition object_meta_well_formed (m: v1.ObjectMeta.t) : iProp Σ :=
  "%uid_well_formed" ∷ ⌜ m.(v1.ObjectMeta.UID') ≠ "_ORPHAN_POD"%go ⌝ ∗
  (* Kubernetes guarantees there is only one element in OwnerReferences' whose Controller' is true,
  but here we only need a weaker specification saying that if there are two controller parents then they are the same. *)
  "#at_most_one_controller_parent" ∷ □ ∀ uid1 uid2,
    has_controller_parent_of m.(v1.ObjectMeta.OwnerReferences') uid1 -∗ 
      has_controller_parent_of m.(v1.ObjectMeta.OwnerReferences') uid2 -∗
        ⌜ uid1 = uid2 ⌝.

Axiom pod_spec_well_formed: v1.PodSpec.t → iProp Σ.
Global Instance pod_spec_well_formed_persistent spec : Persistent (pod_spec_well_formed spec).
Proof. Admitted.

Axiom pod_status_well_formed: v1.PodStatus.t → iProp Σ.
Global Instance pod_status_well_formed_persistent status : Persistent (pod_status_well_formed status).
Proof. Admitted.

Definition pod_well_formed (pod: v1.Pod.t) : iProp Σ :=
  "#pod_metadata_well_formed" ∷ object_meta_well_formed pod.(v1.Pod.ObjectMeta') ∗
  "#pod_spec_well_formed" ∷ pod_spec_well_formed pod.(v1.Pod.Spec') ∗
  "#pod_status_well_formed" ∷ pod_status_well_formed pod.(v1.Pod.Status').

Definition pod_nn_well_formed (pod: v1.Pod.t) (namespace name: go_string) : iProp Σ :=
  "%namespace_match" ∷ ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ⌝ ∗
  "%name_match" ∷ ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name') = name ⌝ ∗
  "#pod_well_formed" ∷ pod_well_formed pod.

Definition object_meta_to_create_well_formed (m: v1.ObjectMeta.t) : iProp Σ :=
  "%generatename_not_empty_if_name_empty" ∷ ⌜ m.(v1.ObjectMeta.Name') = ""%go → m.(v1.ObjectMeta.GenerateName') ≠ ""%go ⌝.

Axiom pod_spec_to_create_well_formed: v1.PodSpec.t → iProp Σ.
Global Instance pod_spec_to_create_well_formed_persistent spec : Persistent (pod_spec_to_create_well_formed spec).
Proof. Admitted.

Axiom pod_status_to_create_well_formed: v1.PodStatus.t → iProp Σ.
Global Instance pod_status_to_create_well_formed_persistent status : Persistent (pod_status_to_create_well_formed status).
Proof. Admitted.

Definition pod_to_create_well_formed (pod: v1.Pod.t) : iProp Σ :=
  "#pod_metadata_to_create_well_formed" ∷ object_meta_to_create_well_formed pod.(v1.Pod.ObjectMeta') ∗
  "#pod_spec_to_create_well_formed" ∷ pod_spec_to_create_well_formed pod.(v1.Pod.Spec') ∗
  "#pod_status_to_create_well_formed" ∷ pod_status_to_create_well_formed pod.(v1.Pod.Status').

Definition pod_to_create_nn_well_formed (pod: v1.Pod.t) (namespace name: go_string) : iProp Σ :=
  "%namespace_match" ∷ ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ⌝ ∗
  "%name_match" ∷ ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name') = name ⌝ ∗
  "#pod_to_create_well_formed" ∷ pod_to_create_well_formed pod.

Definition replicaset_well_formed (rs: v1.ReplicaSet.t) : iProp Σ :=
  object_meta_well_formed rs.(v1.ReplicaSet.ObjectMeta') ∗
  ∃ (v: w32), rs.(v1.ReplicaSet.Spec').(v1.ReplicaSetSpec.Replicas') ↦□ v ∗ ⌜ 0 ≤ sint.Z v ⌝.

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