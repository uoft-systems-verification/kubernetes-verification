From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export objectmeta.

Module PersistentVolumeClaimSpecV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Axiom t : Type.
(* The admission predicate used for both create validation and the general
   validation phase of update. PVC schema defaulting, including the default
   VolumeMode, is not yet expressible because [t] is abstract. *)
Axiom valid_create: t → Prop.

(* The currently abstract fields prevent us from spelling out the two storage
   normalization relations. A standalone PVC receives both schema defaults and
   the PVC strategy's data-source normalization; a StatefulSet
   volumeClaimTemplate receives schema defaults but not that REST strategy. *)
Axiom standalone_storage_normalized : t → Prop.
Axiom embedded_storage_normalized : t → Prop.

Definition valid (spec : t) : Prop :=
  valid_create spec ∧ standalone_storage_normalized spec.

Definition valid_embedded (spec : t) : Prop :=
  valid_create spec ∧ embedded_storage_normalized spec.

(* This is a conservative projection of PVC update validation while the PVC
   spec remains abstract: an unchanged spec is always permitted, even when
   [old] has not yet received the normalization required by [valid].
   Upstream also permits controlled binding and expansion changes, but those
   depend on currently unmodeled spec and status fields:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/core/validation/validation.go#L2464-L2549 *)
Definition valid_update (old new : t) : Prop :=
  old = new.

Axiom valid_update_dec :
  ∀ old new, Decision (valid_update old new).
Global Existing Instance valid_update_dec.

(* The conservative update predicate is equality, so its assumed decision
   procedure also supplies equality decision for this otherwise opaque type. *)
Global Instance eq_dec : EqDecision t.
Proof. intros old new. exact (valid_update_dec old new). Defined.

Lemma valid_update_refl spec :
  valid_update spec spec.
Proof. unfold valid_update. done. Qed.

(* The translated PVC spec is still abstract, so the strongest concrete
   create relation currently expressible is that the output has received all
   standalone storage normalization. *)
Definition created (_input stored : t) : Prop :=
  valid stored.

(* StatefulSet volume-claim templates receive schema defaults but do not pass
   through the standalone PVC REST strategy. *)
Definition embedded_created (_input stored : t) : Prop :=
  valid_embedded stored.

(* A PVC update applies schema defaults and the PVC strategy's data-source
   normalization just like creation. The abstract view cannot yet express how
   that normalization depends on the existing PVC, so reuse the strongest
   currently expressible standalone-storage relation. *)
Definition updated (input stored : t) : Prop :=
  created input stored.

Axiom deepown : v1.PersistentVolumeClaimSpec.t → t → dfrac → iProp Σ.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End PersistentVolumeClaimSpecV.

Module PersistentVolumeClaimStatusV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Axiom t : Type.
Axiom eq_dec : EqDecision t.
Global Existing Instance eq_dec.
(* This includes validation and feature-gated normalization of PVC status. *)
Axiom valid: t → Prop.
Axiom deepown : v1.PersistentVolumeClaimStatus.t → t → dfrac → iProp Σ.

Definition created (_input stored : t) : Prop :=
  valid stored.

Definition updated (input stored : t) : Prop :=
  stored = input.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End PersistentVolumeClaimStatusV.

Module PersistentVolumeClaimV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : ObjectMetaV.t;
  Spec' : PersistentVolumeClaimSpecV.t;
  Status' : PersistentVolumeClaimStatusV.t;
}.

Global Instance eq_dec : EqDecision t.
Proof. solve_decision. Defined.

Definition kind : go_string :=
  "PersistentVolumeClaim"%go.

Definition meta_key (meta : ObjectMetaV.t) : KKey.t :=
  {|
    KKey.Kind' := kind;
    KKey.Namespace' := meta.(ObjectMetaV.Namespace');
    KKey.Name' := meta.(ObjectMetaV.Name')
  |}.

Definition key (v: t) : KKey.t :=
  meta_key v.(ObjectMeta').

Definition valid (pvc: t) : Prop :=
  valid_typemeta kind pvc.(TypeMeta') ∧
  valid_resource_version pvc.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  ObjectMetaV.valid kind pvc.(ObjectMeta') ∧
  PersistentVolumeClaimSpecV.valid pvc.(Spec') ∧
  PersistentVolumeClaimStatusV.valid pvc.(Status').

Definition valid_nameless_create ns (pvc : t) : Prop :=
  valid_create_typemeta kind pvc.(TypeMeta') ∧
  ObjectMetaV.valid_nameless_create kind ns pvc.(ObjectMeta') ∧
  PersistentVolumeClaimSpecV.valid_create pvc.(Spec').

Definition valid_named_create ns (pvc : t) : Prop :=
  valid_create_typemeta kind pvc.(TypeMeta') ∧
  ObjectMetaV.valid_named_create kind ns pvc.(ObjectMeta') ∧
  PersistentVolumeClaimSpecV.valid_create pvc.(Spec').

Definition valid_without_meta (pvc: t) : Prop :=
  PersistentVolumeClaimSpecV.valid pvc.(Spec') ∧
  PersistentVolumeClaimStatusV.valid pvc.(Status').

Definition deepown (c: v1.PersistentVolumeClaim.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.PersistentVolumeClaim.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.PersistentVolumeClaim.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_spec" ∷ PersistentVolumeClaimSpecV.deepown c.(v1.PersistentVolumeClaim.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ PersistentVolumeClaimStatusV.deepown c.(v1.PersistentVolumeClaim.Status') v.(Status') dq.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

Definition typemeta_ptr l: loc :=
  struct_field_ref v1.PersistentVolumeClaim.t "TypeMeta" l.

Definition objectmeta_ptr l: loc :=
  struct_field_ref v1.PersistentVolumeClaim.t "ObjectMeta" l.

Definition spec_ptr l: loc :=
  struct_field_ref v1.PersistentVolumeClaim.t "Spec" l.

Definition status_ptr l: loc :=
  struct_field_ref v1.PersistentVolumeClaim.t "Status" l.

Definition update_objectmeta (v: t) (m: ObjectMetaV.t) : t :=
  v <| ObjectMeta' := m |>.

Definition deepown_without_meta (c: v1.PersistentVolumeClaim.t) (v: t) dq: iProp Σ :=
  "Hdeepown_spec" ∷ PersistentVolumeClaimSpecV.deepown c.(v1.PersistentVolumeClaim.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ PersistentVolumeClaimStatusV.deepown c.(v1.PersistentVolumeClaim.Status') v.(Status') dq.

Definition deepown_l_without_meta l v (dq: dfrac): iProp Σ :=
  ∃ c,
  spec_ptr l ↦{dq} c.(v1.PersistentVolumeClaim.Spec') ∗
  status_ptr l ↦{dq} c.(v1.PersistentVolumeClaim.Status') ∗
  deepown_without_meta c v dq.

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
    (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
    ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
    PersistentVolumeClaimSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
    PersistentVolumeClaimStatusV.deepown_l (status_ptr l) v.(Status') dq.
Proof.
  unfold deepown_l, deepown.
  iIntros "H".
  iDestruct "H" as (c) "[Hl Hdeepown]".
  iDestruct "Hdeepown" as "(%Htypemeta & Hobjectmeta & Hspec & Hstatus)".
  iDestruct (struct_fields_split (V:=v1.PersistentVolumeClaim.t) with "Hl") as "[Hfields %Hnot_null]".
  iNamedPrefix "Hfields" "H".
  iSplitR; first done.
  rewrite -Htypemeta.
  iFrame "HTypeMeta".
  iSplitL "HObjectMeta Hobjectmeta".
  { unfold ObjectMetaV.deepown_l, objectmeta_ptr. iFrame. }
  iSplitL "HSpec Hspec".
  { unfold PersistentVolumeClaimSpecV.deepown_l, spec_ptr. iFrame. }
  unfold PersistentVolumeClaimStatusV.deepown_l, status_ptr. iFrame.
Qed.

Lemma deepown_l_merge l v vm dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) vm dq ∗
  PersistentVolumeClaimSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  PersistentVolumeClaimStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
    deepown_l l (update_objectmeta v vm) dq.
Proof.
  intros Hnot_null.
  destruct v as [v_typemeta v_objectmeta v_spec v_status].
  unfold deepown_l, deepown, update_objectmeta.
  rewrite /typemeta_ptr /objectmeta_ptr /spec_ptr /status_ptr.
  iIntros "(HTypeMeta & Hobjectmeta & Hspec_l & Hstatus_l)".
  iDestruct "Hobjectmeta" as (cm) "(HObjectMeta & Hobjectmeta)".
  iDestruct "Hspec_l" as (cspec) "(HSpec & Hspec)".
  iDestruct "Hstatus_l" as (cstatus) "(HStatus & Hstatus)".
  iAssert (typed_pointsto_def l (v1.PersistentVolumeClaim.mk v_typemeta cm cspec cstatus) dq)
    with "[HTypeMeta HObjectMeta HSpec HStatus]" as "Hfields".
  { simpl. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.PersistentVolumeClaim.t)
    l (v1.PersistentVolumeClaim.mk v_typemeta cm cspec cstatus) dq Hnot_null with "Hfields") as "Hl".
  iExists (v1.PersistentVolumeClaim.mk v_typemeta cm cspec cstatus).
  iSplitL "Hl"; first iExact "Hl".
  iSplitR "Hobjectmeta Hspec Hstatus"; first done.
  simpl. iFrame.
Qed.

Lemma deepown_l_restore l v dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
  PersistentVolumeClaimSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  PersistentVolumeClaimStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
    deepown_l l v dq.
Proof.
  intros Hnot_null.
  iIntros "H".
  iPoseProof (deepown_l_merge l v v.(ObjectMeta') dq Hnot_null with "H") as "H".
  assert (update_objectmeta v v.(ObjectMeta') = v) as ->.
  { destruct v. done. }
  iFrame.
Qed.

End proof.
End PersistentVolumeClaimV.
