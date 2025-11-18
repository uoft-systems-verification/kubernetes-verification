Require Export New.proof.sync.
From proof.k8s_io.api.apps Require Export v1_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof Require Export time.
From proof Require Import prelude empty_ffi.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Definition symmetric_iProp {A} (R : A → A → iProp Σ) :=
  ∀ x y, R x y ⊣⊢ R y x.

Definition deepcopy_w32_loc (src dst: loc) : iProp Σ :=
  ⌜src = null ↔ dst = null⌝ ∧
  ∀ (v1 v2: w32), src ↦ v1 -∗ dst ↦ v2 -∗ ⌜ v1 = v2 ⌝.

Definition deepcopy_w64_loc (src dst: loc) : iProp Σ :=
  ⌜src = null ↔ dst = null⌝ ∧
  ∀ (v1 v2: w64), src ↦ v1 -∗ dst ↦ v2 -∗ ⌜ v1 = v2 ⌝.

Definition deepcopy_gmap_string_string (src dst: loc) : iProp Σ :=
  ⌜src = null ↔ dst = null⌝ ∧
  ∀ (v1 v2: gmap go_string go_string), src ↦$ v1 -∗ dst ↦$ v2 -∗ ⌜ v1 = v2 ⌝.

Axiom deepcopy_Time: time.Time.t → time.Time.t → iProp Σ.

Definition deepcopy_Time_loc (src dst: loc) : iProp Σ :=
  ⌜src = null ↔ dst = null⌝ ∧
  ∀ (v1 v2: time.Time.t), src ↦ v1 -∗ dst ↦ v2 -∗ deepcopy_Time v1 v2.

Axiom deepcopy_OwnerReference: v1.OwnerReference.t → v1.OwnerReference.t → iProp Σ.

Definition deepcopy_list_OwnerReference (src dst: slice.t) : iProp Σ :=
  ⌜src = slice.nil ↔ dst = slice.nil⌝ ∧
  ∀ (vs1 vs2: list v1.OwnerReference.t), src ↦* vs1 -∗ dst ↦* vs2 -∗
    [∗ list] v1;v2 ∈ vs1;vs2, deepcopy_OwnerReference v1 v2.

Definition deepcopy_list_string (src dst: slice.t) : iProp Σ :=
  ⌜src = slice.nil ↔ dst = slice.nil⌝ ∧
  ∀ (vs1 vs2: list go_string), src ↦* vs1 -∗ dst ↦* vs2 -∗ ⌜ vs1 = vs2 ⌝.

Axiom deepcopy_ManagedFieldsEntry: v1.ManagedFieldsEntry.t → v1.ManagedFieldsEntry.t → iProp Σ.

Definition deepcopy_list_ManagedFieldsEntry (src dst: slice.t) : iProp Σ :=
  ⌜src = slice.nil ↔ dst = slice.nil⌝ ∧
  ∀ (vs1 vs2: list v1.ManagedFieldsEntry.t), src ↦* vs1 -∗ dst ↦* vs2 -∗
    [∗ list] v1;v2 ∈ vs1;vs2, deepcopy_ManagedFieldsEntry v1 v2.

Definition deepcopy_TypeMeta (src dst: v1.TypeMeta.t) : iProp Σ :=
  ⌜ src = dst ⌝.

Definition deepcopy_ObjectMeta (src dst: v1.ObjectMeta.t) : iProp Σ :=
  ⌜ src.(v1.ObjectMeta.Name') = dst.(v1.ObjectMeta.Name') ∧
    src.(v1.ObjectMeta.GenerateName') = dst.(v1.ObjectMeta.GenerateName') ∧
    src.(v1.ObjectMeta.Namespace') = dst.(v1.ObjectMeta.Namespace') ∧
    src.(v1.ObjectMeta.SelfLink') = dst.(v1.ObjectMeta.SelfLink') ∧ 
    src.(v1.ObjectMeta.UID') = dst.(v1.ObjectMeta.UID') ∧ 
    src.(v1.ObjectMeta.ResourceVersion') = dst.(v1.ObjectMeta.ResourceVersion') ∧
    src.(v1.ObjectMeta.Generation') = dst.(v1.ObjectMeta.Generation') ∧
    src.(v1.ObjectMeta.CreationTimestamp') = dst.(v1.ObjectMeta.CreationTimestamp') ⌝ ∗
  deepcopy_Time_loc src.(v1.ObjectMeta.DeletionTimestamp') dst.(v1.ObjectMeta.DeletionTimestamp') ∗
  deepcopy_w64_loc src.(v1.ObjectMeta.DeletionGracePeriodSeconds') dst.(v1.ObjectMeta.DeletionGracePeriodSeconds') ∗
  deepcopy_gmap_string_string src.(v1.ObjectMeta.Labels') dst.(v1.ObjectMeta.Labels') ∗
  deepcopy_gmap_string_string src.(v1.ObjectMeta.Annotations') dst.(v1.ObjectMeta.Annotations') ∗
  deepcopy_list_OwnerReference src.(v1.ObjectMeta.OwnerReferences') dst.(v1.ObjectMeta.OwnerReferences') ∗
  deepcopy_list_string src.(v1.ObjectMeta.Finalizers') dst.(v1.ObjectMeta.Finalizers') ∗
  deepcopy_list_ManagedFieldsEntry src.(v1.ObjectMeta.ManagedFields') dst.(v1.ObjectMeta.ManagedFields').

Axiom deepcopy_PodSpec: v1.PodSpec.t → v1.PodSpec.t → iProp Σ.

Axiom deepcopy_PodStatus: v1.PodStatus.t → v1.PodStatus.t → iProp Σ.

Definition deepcopy_Pod (src dst: v1.Pod.t) : iProp Σ :=
  deepcopy_TypeMeta src.(v1.Pod.TypeMeta') dst.(v1.Pod.TypeMeta') ∗
  deepcopy_ObjectMeta src.(v1.Pod.ObjectMeta') dst.(v1.Pod.ObjectMeta') ∗
  deepcopy_PodSpec src.(v1.Pod.Spec') dst.(v1.Pod.Spec') ∗
  deepcopy_PodStatus src.(v1.Pod.Status') dst.(v1.Pod.Status').

Definition deepcopy_ReplicaSetSpec (src dst: v1.ReplicaSetSpec.t) : iProp Σ :=
  deepcopy_w32_loc src.(v1.ReplicaSetSpec.Replicas') dst.(v1.ReplicaSetSpec.Replicas').

Definition deepcopy_ReplicaSetStatus (src dst: v1.ReplicaSetStatus.t) : iProp Σ :=
  True%I.

Definition deepcopy_ReplicaSet (src dst: v1.ReplicaSet.t) : iProp Σ :=
  deepcopy_TypeMeta src.(v1.ReplicaSet.TypeMeta') dst.(v1.ReplicaSet.TypeMeta') ∗
  deepcopy_ObjectMeta src.(v1.ReplicaSet.ObjectMeta') dst.(v1.ReplicaSet.ObjectMeta') ∗
  deepcopy_ReplicaSetSpec src.(v1.ReplicaSet.Spec') dst.(v1.ReplicaSet.Spec') ∗
  deepcopy_ReplicaSetStatus src.(v1.ReplicaSet.Status') dst.(v1.ReplicaSet.Status').

Lemma deepcopy_Pod_symmetric:
  symmetric_iProp deepcopy_Pod.
Proof.
Admitted.

Lemma deepcopy_ReplicaSet_symmetric:
  symmetric_iProp deepcopy_ReplicaSet.
Proof.
Admitted.

End proof.
