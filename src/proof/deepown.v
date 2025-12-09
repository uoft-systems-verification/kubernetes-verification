Require Export New.proof.sync.
From proof.k8s_io.api.apps Require Export v1_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof Require Export time.
From proof Require Import prelude empty_ffi.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Axiom deepown_Time: time.Time.t → iProp Σ.
Global Instance deepown_Time_persistent v : Persistent (deepown_Time v).
Proof. Admitted.

Definition deepown_Time_loc l: iProp Σ :=
  ⌜ l = null ⌝ ∨ ∃ (v: time.Time.t), l ↦□ v ∗ deepown_Time v.

Definition deepown_w64_loc l : iProp Σ :=
  ⌜ l = null ⌝ ∨ ∃ (v: w64), l ↦□ v.

Definition deepown_bool_loc l : iProp Σ :=
  ⌜ l = null ⌝ ∨ ∃ (v: bool), l ↦□ v.

Definition deepown_string_slice l : iProp Σ :=
  ⌜ l = slice.nil ⌝ ∨ ∃ (vs: list go_string), l ↦*□ vs.

Definition deepown_string_string_map l : iProp Σ :=
  ⌜ l = null ⌝ ∨ ∃ (v: gmap go_string go_string), l ↦$□ v.

Definition deepown_OwnerReference (v: v1.OwnerReference.t) : iProp Σ :=
  deepown_bool_loc v.(v1.OwnerReference.Controller') ∗
  deepown_bool_loc v.(v1.OwnerReference.BlockOwnerDeletion').

Definition deepown_OwnerReference_slice l : iProp Σ :=
  ⌜ l = slice.nil ⌝ ∨
  ∃ (vs : list v1.OwnerReference.t), l ↦*□ vs ∗ [∗ list] v ∈ vs, deepown_OwnerReference v.

Axiom deepown_ManagedFieldsEntry: v1.ManagedFieldsEntry.t → iProp Σ.
Global Instance deepown_ManagedFieldsEntry_persistent v : Persistent (deepown_ManagedFieldsEntry v).
Proof. Admitted.

Definition deepown_ManagedFieldsEntry_slice l : iProp Σ :=
  ⌜ l = slice.nil ⌝ ∨
  ∃ (vs : list v1.ManagedFieldsEntry.t), l ↦*□ vs ∗ [∗ list] v ∈ vs, deepown_ManagedFieldsEntry v.

Definition deepown_ObjectMeta (v: v1.ObjectMeta.t) : iProp Σ :=
  deepown_Time_loc v.(v1.ObjectMeta.DeletionTimestamp') ∗
  deepown_w64_loc v.(v1.ObjectMeta.DeletionGracePeriodSeconds') ∗
  deepown_string_string_map v.(v1.ObjectMeta.Labels') ∗
  deepown_string_string_map v.(v1.ObjectMeta.Annotations') ∗
  deepown_OwnerReference_slice v.(v1.ObjectMeta.OwnerReferences') ∗
  deepown_string_slice v.(v1.ObjectMeta.Finalizers') ∗
  deepown_ManagedFieldsEntry_slice v.(v1.ObjectMeta.ManagedFields').

Axiom deepown_PodSpec: v1.PodSpec.t → iProp Σ.
Global Instance deepown_PodSpec_persistent v : Persistent (deepown_PodSpec v).
Proof. Admitted.

Axiom deepown_PodStatus: v1.PodStatus.t → iProp Σ.
Global Instance deepown_PodStatus_persistent v : Persistent (deepown_PodStatus v).
Proof. Admitted.

Definition deepown_Pod (v: v1.Pod.t) : iProp Σ :=
  deepown_ObjectMeta v.(v1.Pod.ObjectMeta') ∗
  deepown_PodSpec v.(v1.Pod.Spec') ∗
  deepown_PodStatus v.(v1.Pod.Status').

End proof.
