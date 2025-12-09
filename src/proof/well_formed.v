Require Export New.proof.sync.
From proof.k8s_io.api.apps Require Export v1_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From proof Require Import prelude empty_ffi.
From proof Require Export deepcopy.


Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Definition has_controller_parent l os i o c : iProp Σ :=
  l ↦*□ os ∗ ⌜ os !! i = Some o ⌝ ∗ o.(v1.OwnerReference.Controller') ↦□ c ∗ ⌜ c = true ⌝.

Definition has_controller_parent_of l uid : iProp Σ :=
  ∃ os i o c, has_controller_parent l os i o c ∗ ⌜ o.(v1.OwnerReference.UID') = uid ⌝.

Definition has_controller_parent_at l i : iProp Σ :=
  ∃ os o c, has_controller_parent l os i o c.

Definition well_formed_OwnerReferences l : iProp Σ :=
  (* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L92 *)
  "#at_most_one_controller_parent" ∷ □ ∀ i1 i2,
    has_controller_parent_at l i1 -∗ has_controller_parent_at l i2 -∗ ⌜ i1 = i2 ⌝.

Definition well_formed_ObjectMeta (m: v1.ObjectMeta.t) : iProp Σ :=
  "%uid_well_formed" ∷ ⌜ m.(v1.ObjectMeta.UID') ≠ "_ORPHAN_POD"%go ⌝ ∗
  "#well_formed_OwnerReferences" ∷ well_formed_OwnerReferences m.(v1.ObjectMeta.OwnerReferences').

Lemma at_most_one_controller_parent_implies_same_uid o:
  (□ ∀ i1 i2, has_controller_parent_at o i1 -∗ has_controller_parent_at o i2 -∗ ⌜ i1 = i2 ⌝)
  ⊢ (□ ∀ uid1 uid2, has_controller_parent_of o uid1 -∗ has_controller_parent_of o uid2 -∗ ⌜ uid1 = uid2 ⌝).
Proof.
  iIntros "#H". iModIntro.
  iIntros (uid1 uid2) "Huid1 Huid2".
  iDestruct "Huid1" as (os1 i1 o1 c1) "[Hparent1 %Huid1]".
  iDestruct "Huid2" as (os2 i2 o2 c2) "[Hparent2 %Huid2]".
  iDestruct ("H" $! i1 i2 with "[Hparent1] [Hparent2]") as "%Hi_eq".
  { iExists os1, o1, c1. iFrame "Hparent1". }
  { iExists os2, o2, c2. iFrame "Hparent2". }
  subst i2.
  iDestruct "Hparent1" as "(#Hos1 & %Hlookup1 & _)".
  iDestruct "Hparent2" as "(#Hos2 & %Hlookup2 & _)".
  iDestruct (own_slice_agree with "Hos1 Hos2") as %Hos_eq.
  subst os2.
  rewrite Hlookup1 in Hlookup2.
  injection Hlookup2 as <-.
  iPureIntro.
  congruence.
Qed.

Axiom well_formed_PodSpec: v1.PodSpec.t → iProp Σ.
Global Instance well_formed_PodSpec_persistent spec : Persistent (well_formed_PodSpec spec).
Proof. Admitted.

Axiom well_formed_PodStatus: v1.PodStatus.t → iProp Σ.
Global Instance well_formed_PodStatus_persistent status : Persistent (well_formed_PodStatus status).
Proof. Admitted.

Definition well_formed_Pod (pod: v1.Pod.t) : iProp Σ :=
  "#pod_metadata_well_formed" ∷ well_formed_ObjectMeta pod.(v1.Pod.ObjectMeta') ∗
  "#well_formed_PodSpec" ∷ well_formed_PodSpec pod.(v1.Pod.Spec') ∗
  "#well_formed_PodStatus" ∷ well_formed_PodStatus pod.(v1.Pod.Status').

Definition well_formed_to_create_ObjectMeta (m: v1.ObjectMeta.t) : iProp Σ :=
  "%generatename_not_empty_if_name_empty" ∷ ⌜ m.(v1.ObjectMeta.Name') = ""%go → m.(v1.ObjectMeta.GenerateName') ≠ ""%go ⌝.

Axiom well_formed_to_create_PodSpec: v1.PodSpec.t → iProp Σ.
Global Instance well_formed_to_create_PodSpec_persistent spec : Persistent (well_formed_to_create_PodSpec spec).
Proof. Admitted.

Axiom well_formed_to_create_PodStatus: v1.PodStatus.t → iProp Σ.
Global Instance well_formed_to_create_PodStatus_persistent status : Persistent (well_formed_to_create_PodStatus status).
Proof. Admitted.

Definition well_formed_to_create_Pod (pod: v1.Pod.t) : iProp Σ :=
  "#pod_metadata_to_create_well_formed" ∷ well_formed_to_create_ObjectMeta pod.(v1.Pod.ObjectMeta') ∗
  "#well_formed_to_create_PodSpec" ∷ well_formed_to_create_PodSpec pod.(v1.Pod.Spec') ∗
  "#well_formed_to_create_PodStatus" ∷ well_formed_to_create_PodStatus pod.(v1.Pod.Status').

Definition well_formed_ReplicaSet (rs: v1.ReplicaSet.t) : iProp Σ :=
  well_formed_ObjectMeta rs.(v1.ReplicaSet.ObjectMeta') ∗
  ∃ (v: w32), rs.(v1.ReplicaSet.Spec').(v1.ReplicaSetSpec.Replicas') ↦□ v ∗ ⌜ 0 ≤ sint.Z v ⌝.

Lemma well_formed_preserved_by_deepcopy_ReplicaSet rs1 rs2 namespace name:
  deepcopy_ReplicaSet rs1 rs2 -∗
    ⌜ rs1.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ⌝ -∗
    ⌜ rs1.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Name') = name ⌝ -∗
    well_formed_ReplicaSet rs1 -∗
      deepcopy_ReplicaSet rs1 rs2 ∗
      ⌜ rs1.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ⌝ ∗
      ⌜ rs1.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Name') = name ⌝ ∗
      ⌜ rs2.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ⌝ ∗
      ⌜ rs2.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Name') = name ⌝ ∗
      well_formed_ReplicaSet rs2.
Proof.
Admitted.

End proof.