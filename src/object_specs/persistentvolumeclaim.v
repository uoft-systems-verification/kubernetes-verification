From New.generatedviews Require Export persistentvolumeclaim.
From New.proof Require Import prelude empty_ffi.
From New.object_specs Require Export objectmeta.
From New.object_specs Require Import top_level.


(* These adapter lemmas compare canonical ownership with the included views. *)
Local Transparent ObjectMetaView.ObjectMetaV.deepown ObjectMetaV.deepown.

Module PersistentVolumeClaimSpecV.
Include PersistentVolumeClaimView.PersistentVolumeClaimSpecV.

(* Imported admission validation acts on the complete concrete PVC spec. *)
Axiom valid_create: t → Prop.
Axiom valid_create_dec : ∀ spec, Decision (valid_create spec).
Global Existing Instance valid_create_dec.

(* The two imported storage-normalization predicates distinguish API writes
   from embedded claim templates. A standalone PVC receives both schema defaults and
   the PVC strategy's data-source normalization; a StatefulSet
   volumeClaimTemplate receives schema defaults but not that REST strategy. *)
Axiom standalone_storage_normalized : t → Prop.
Axiom embedded_storage_normalized : t → Prop.

Definition valid (spec : t) : Prop :=
  valid_create spec ∧ standalone_storage_normalized spec.

Definition valid_embedded (spec : t) : Prop :=
  valid_create spec ∧ embedded_storage_normalized spec.

(** Top-level PVC update validation over the stored old spec and submitted
    input spec. It includes PVC's private-old preparation and input
    normalization through the existing imported semantic contract. *)
Axiom valid_update : t → t → Prop.
Axiom valid_update_dec : ∀ old input, Decision (valid_update old input).
Global Existing Instance valid_update_dec.
Axiom valid_update_refl : ∀ spec, valid_create spec → valid_update spec spec.

(* The existing conservative create contract exposes standalone storage
   normalization. Concrete fields and ownership are generated independently
   of these imported semantic contracts. *)
Definition created (_input stored : t) : Prop :=
  valid stored.

(* StatefulSet volume-claim templates receive schema defaults but do not pass
   through the standalone PVC REST strategy. *)
Definition embedded_created (_input stored : t) : Prop :=
  valid_embedded stored.

(* A PVC update applies schema defaults and the PVC strategy's data-source
   normalization just like creation. The existing imported contract exposes standalone storage normalization
   conservatively; it does not specify individual field transformations. *)
Definition updated (input stored : t) : Prop :=
  valid stored.

End PersistentVolumeClaimSpecV.

Module PersistentVolumeClaimStatusV.
Include PersistentVolumeClaimView.PersistentVolumeClaimStatusV.

Axiom valid: t → Prop.
Axiom valid_update : t → t → Prop.
Axiom valid_update_dec : ∀ old input, Decision (valid_update old input).
Global Existing Instance valid_update_dec.
Definition created (_input stored : t) : Prop := stored = zero <| Phase' := "Pending"%go |>.
Axiom updated : t → t → Prop.

End PersistentVolumeClaimStatusV.

Module PersistentVolumeClaimV.
Include PersistentVolumeClaimView.PersistentVolumeClaimV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

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

Definition extra_valid (_pvc : t) : Prop := True.

Definition valid_create request_kind ns (pvc : t) : Prop :=
  request_kind = kind ∧
  ns ≠ ""%go ∧
  valid_namespace ns ∧
  valid_create_typemeta kind pvc.(TypeMeta') ∧
  ObjectMetaV.valid_create kind ns pvc.(ObjectMeta') ∧
  PersistentVolumeClaimSpecV.valid_create pvc.(Spec').

Definition valid_update request_kind namespace old_meta old_spec (input : t) : Prop :=
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  valid_create request_kind namespace input ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  PersistentVolumeClaimSpecV.valid_update old_spec input.(Spec').

Definition valid_status_update request_kind namespace old_meta old_status (input : t) : Prop :=
  request_kind = kind ∧
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  PersistentVolumeClaimStatusV.valid_update old_status input.(Status').

Definition valid_without_meta (pvc: t) : Prop :=
  PersistentVolumeClaimSpecV.valid pvc.(Spec') ∧
  PersistentVolumeClaimStatusV.valid pvc.(Status').

(** Add the PVC-protection finalizer exactly as the fixed mutating-admission
    model does on create. *)
Definition pvc_protection_finalizer : go_string :=
  "kubernetes.io/pvc-protection"%go.

(** The StorageObjectInUseProtection admission plugin leaves the finalizers
    unchanged when the PVC-protection finalizer is already present. Otherwise,
    it appends that finalizer; a nil slice therefore becomes a singleton list.
    https://github.com/kubernetes/kubernetes/blob/release-1.34/plugin/pkg/admission/storage/storageobjectinuseprotection/admission.go#L120-L128 *)
Definition add_pvc_protection_finalizer (finalizers : option (list go_string)) : option (list go_string) :=
  if decide (pvc_protection_finalizer ∈ default [] finalizers)
  then finalizers
  else Some (default [] finalizers ++ [pvc_protection_finalizer]).

(** [input] is the submitted create request.
    [stored] is the object stored after the successful create. *)
Definition created (namespace : go_string) (input stored : t) : Prop :=
  valid_typemeta kind stored.(TypeMeta') ∧
  ObjectMetaV.created namespace
    (input.(ObjectMeta')
      <| ObjectMetaV.Finalizers' := add_pvc_protection_finalizer input.(ObjectMeta').(ObjectMetaV.Finalizers') |>)
    stored.(ObjectMeta') ∧
  stored.(ObjectMeta').(ObjectMetaV.Generation') = input.(ObjectMeta').(ObjectMetaV.Generation') ∧
  PersistentVolumeClaimSpecV.created input.(Spec') stored.(Spec') ∧
  PersistentVolumeClaimStatusV.created input.(Status') stored.(Status').

(** [input] is the submitted status update.
    [stored] is the object stored after the successful status update. *)
Definition status_updated (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  ObjectMetaV.updated input.(ObjectMeta') stored.(ObjectMeta') ∧
  PersistentVolumeClaimStatusV.updated input.(Status') stored.(Status').

(** End-to-end relation between the existing object, submitted object, and
    stored result of a successful update. Generation and resource version are
    intentionally left unspecified because storage manages them. *)
Definition updated (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  ObjectMetaV.updated input.(ObjectMeta') stored.(ObjectMeta') ∧
  PersistentVolumeClaimSpecV.updated input.(Spec') stored.(Spec').

#[global]
Instance top_level_instance : top_level Σ t :=
  Build_top_level Σ t ObjectMetaV.t PersistentVolumeClaimSpecV.t PersistentVolumeClaimStatusV.t
    valid
    extra_valid
    valid_create
    valid_update
    valid_status_update
    created
    (λ _, updated)
    status_updated
    deepown_l.

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
