Require Export New.proof.sync.
From proof.k8s_io.api.apps Require Export v1_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From proof Require Import prelude empty_ffi.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Definition symmetric_iProp {A} (R : A → A → iProp Σ) :=
  ∀ x y, R x y ⊣⊢ R y x.

(* TODO: finish the deepcopy definition *)

Definition deepcopy_of_w32_loc (src dst: loc) : iProp Σ :=
  ⌜src = null ↔ dst = null⌝ ∧
  ∀ (v1 v2: w32), src ↦ v1 -∗ dst ↦ v2 -∗ ⌜ v1 = v2 ⌝.

Definition deepcopy_of_type_meta (src dst: v1.TypeMeta.t) : iProp Σ :=
  ⌜ src = dst ⌝.

Definition deepcopy_of_object_meta (src dst: v1.ObjectMeta.t) : iProp Σ :=
  True%I.

Definition deepcopy_of_pod_spec (src dst: v1.PodSpec.t) : iProp Σ :=
  True%I.

Definition deepcopy_of_pod_status (src dst: v1.PodStatus.t) : iProp Σ :=
  True%I.

Definition deepcopy_of_pod (src dst: v1.Pod.t) : iProp Σ :=
  deepcopy_of_type_meta src.(v1.Pod.TypeMeta') dst.(v1.Pod.TypeMeta') ∗
  deepcopy_of_object_meta src.(v1.Pod.ObjectMeta') dst.(v1.Pod.ObjectMeta') ∗
  deepcopy_of_pod_spec src.(v1.Pod.Spec') dst.(v1.Pod.Spec') ∗
  deepcopy_of_pod_status src.(v1.Pod.Status') dst.(v1.Pod.Status').

Definition deepcopy_of_replicaset_spec (src dst: v1.ReplicaSetSpec.t) : iProp Σ :=
  deepcopy_of_w32_loc src.(v1.ReplicaSetSpec.Replicas') dst.(v1.ReplicaSetSpec.Replicas').

Definition deepcopy_of_replicaset_status (src dst: v1.ReplicaSetStatus.t) : iProp Σ :=
  True%I.

Definition deepcopy_of_replicaset (src dst: v1.ReplicaSet.t) : iProp Σ :=
  deepcopy_of_type_meta src.(v1.ReplicaSet.TypeMeta') dst.(v1.ReplicaSet.TypeMeta') ∗
  deepcopy_of_object_meta src.(v1.ReplicaSet.ObjectMeta') dst.(v1.ReplicaSet.ObjectMeta') ∗
  deepcopy_of_replicaset_spec src.(v1.ReplicaSet.Spec') dst.(v1.ReplicaSet.Spec') ∗
  deepcopy_of_replicaset_status src.(v1.ReplicaSet.Status') dst.(v1.ReplicaSet.Status').

Lemma deepcopy_of_pod_symmetric:
  symmetric_iProp deepcopy_of_pod.
Proof.
Admitted.

Lemma deepcopy_of_replicaset_symmetric:
  symmetric_iProp deepcopy_of_replicaset.
Proof.
Admitted.

End proof.
