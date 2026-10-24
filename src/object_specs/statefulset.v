From New.generatedviews Require Export statefulset.
From New.proof Require Import prelude empty_ffi.
From New.object_specs Require Export labelselector pod persistentvolumeclaim.
From New.object_specs Require Import top_level.


(* These adapter lemmas compare canonical ownership with the included views. *)
Local Transparent ObjectMetaView.ObjectMetaV.deepown ObjectMetaV.deepown.
Local Transparent StatefulSetView.StatefulSetSpecV.deepown StatefulSetView.StatefulSetStatusV.deepown.

Module StatefulSetSpecV.
Include StatefulSetView.StatefulSetSpecV.

Local Transparent deepown.
(** Imported Kubernetes schema defaulting, feature-gated preparation, and
    validation for the additional represented fields. These functions use the
    checked-out model's feature configuration. As with [PodAPI], their semantics
    remain a trusted library boundary; the representation and ownership are
    fully concrete. *)
Parameter validate_additional_create_fields : t → bool.
Parameter additional_storage_normalized : t → bool.

(* Kubernetes validation and semantic equality treat nil and allocated empty
   volume-claim-template slices identically. Preserve that representation
   distinction in [VolumeClaimTemplates'] and use this projection where only
   the logical sequence matters. *)
Definition volume_claim_templates_list (spec : t) : list PersistentVolumeClaimV.t :=
  default [] spec.(VolumeClaimTemplates').

Definition volume_claim_template_names (spec : t) : list go_string :=
  (λ pvc, pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name')) <$> volume_claim_templates_list spec.

(* Before validating a StatefulSet's Pod template, Kubernetes replaces every
   template volume whose name occurs in [VolumeClaimTemplates] with the
   generated PVC-backed volume. These are precisely the original volumes that
   survive that replacement. *)
Definition preserved_template_volumes (spec : t) : list VolumeV.t :=
  filter
    (λ volume, volume.(VolumeV.Name') ∉ volume_claim_template_names spec)
    (PodSpecV.volumes_list spec.(Template').(PodTemplateSpecV.Spec')).

Definition effective_template_spec (spec : t) : PodSpecV.t :=
  let template_spec := (PodTemplateSpecV.normalized spec.(Template')).(PodTemplateSpecV.Spec') in
  let names := elements (list_to_set (C:=gset go_string) (volume_claim_template_names spec)) in
  let claims := (λ name, VolumeV.mk name
    (VolumeSourceV.zero <| VolumeSourceV.PersistentVolumeClaim' :=
      Some (v1.PersistentVolumeClaimVolumeSource.mk name false) |>)) <$> names in
  let volumes := if decide (names = []) then template_spec.(PodSpecV.Volumes')
    else Some (claims ++ filter (λ volume, volume.(VolumeV.Name') ∉ names)
      (PodSpecV.volumes_list template_spec)) in
  template_spec <| PodSpecV.Volumes' := volumes |>
    <| PodSpecV.Hostname' := ""%go |> <| PodSpecV.Subdomain' := ""%go |>.

(* The projection of StatefulSet's effective Pod-template validation onto the
   represented metadata and PodSpec fields. Kubernetes clears the template's
   Hostname and Subdomain because the controller overwrites them, so neither
   field is constrained here. Claim-template volumes are handled separately
   below; their names are map keys and are therefore unique, while filtering
   makes them disjoint from the preserved original volumes.
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L193-L214 *)
Definition valid_template (spec : t) : Prop :=
  valid_labels spec.(Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') ∧
  valid_annotations spec.(Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations') ∧
  Forall VolumeV.valid (preserved_template_volumes spec) ∧
  NoDup (VolumeV.Name' <$> preserved_template_volumes spec) ∧
  PodAPI.validate_template spec.(Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')
    (drop_legacy_init_container_annotations
      spec.(Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations')) (effective_template_spec spec) = true ∧
  (PodTemplateSpecV.normalized spec.(Template')).(PodTemplateSpecV.Spec').(PodSpecV.RestartPolicy') = "Always"%go ∧
  (PodTemplateSpecV.normalized spec.(Template')).(PodTemplateSpecV.Spec').(PodSpecV.ActiveDeadlineSeconds') = None.

Global Instance valid_template_dec spec : Decision (valid_template spec).
Proof. unfold valid_template. apply _. Defined.

Definition valid_create (spec : t) : Prop :=
  (match spec.(Replicas') with
   | Some replicas => 0 ≤ sint.Z replicas
   | None => True
   end) ∧
  (∃ selector,
    spec.(Selector') = Some selector ∧
    LabelSelectorV.valid selector ∧
    ¬ LabelSelectorV.empty selector ∧
    LabelSelectorV.matches selector spec.(Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')
  ) ∧
  valid_template spec ∧
  (* Kubernetes injects every claim-template name as a Pod volume name before
     validating the StatefulSet's Pod template, so each name must be a
     DNS-1123 label:
     https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L193-L214 *)
  Forall (λ pvc, valid_dns1123_label pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name'))
    (volume_claim_templates_list spec) ∧
  Forall (λ pvc, PersistentVolumeClaimSpecV.valid_create pvc.(PersistentVolumeClaimV.Spec'))
    (volume_claim_templates_list spec) ∧
  (spec.(ServiceName') = ""%go ∨ valid_dns1123_label spec.(ServiceName')) ∧
  validate_additional_create_fields spec = true.

(* A stored StatefulSet spec satisfies admission validation. Schema defaulting
   has additionally made [Replicas'] non-nil, zeroed the TypeMeta of embedded
   PVC templates, and normalized those embedded PVC specs. Its Pod template is
   already prepared in the model's fixed feature configuration.
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L117-L178 *)
Definition valid (spec : t) : Prop :=
  valid_create spec ∧
  (∃ replicas, spec.(Replicas') = Some replicas ∧ 0 ≤ sint.Z replicas) ∧
  Forall (λ pvc,
    pvc.(PersistentVolumeClaimV.TypeMeta') = zero_val v1.TypeMeta.t ∧
    PersistentVolumeClaimSpecV.valid_embedded pvc.(PersistentVolumeClaimV.Spec'))
    (volume_claim_templates_list spec) ∧
  PodTemplateSpecV.normalized spec.(Template') = spec.(Template') ∧
  additional_storage_normalized spec = true.

(* Of the represented fields, Kubernetes permits updates to Replicas and the
   Pod template. Selector, volume-claim templates, and service name remain
   immutable. *)
Definition valid_update (old input : t) : Prop :=
  valid_create input ∧
  input.(Selector') = old.(Selector') ∧
  volume_claim_templates_list input = volume_claim_templates_list old ∧
  input.(ServiceName') = old.(ServiceName') ∧
  input.(PodManagementPolicy') = old.(PodManagementPolicy').

Global Instance valid_update_dec old input :
  Decision (valid_update old input).
Proof.
  unfold valid_update, valid_create.
  apply and_dec.
  - apply and_dec; first (destruct input.(Replicas'); apply _).
    apply and_dec.
    + apply LabelSelectorV.exists_eq_some_dec.
      intros selector. apply _.
    + apply and_dec; first apply _.
      apply and_dec; first apply _.
      apply and_dec; apply _.
  - apply and_dec; first apply _.
    apply and_dec; apply _.
Defined.

Lemma valid_update_refl spec :
  valid_create spec →
  valid_update spec spec.
Proof. unfold valid_update. done. Qed.

(* StatefulSet creation defaults an omitted replica count, removes obsolete
   init-container annotations from its Pod template, and normalizes each
   embedded PVC template. The PVC spec relation uses the existing imported defaulting contract. *)
Definition created (input stored : t) : Prop :=
  stored.(Replicas') = Some (default (W32 1) input.(Replicas')) ∧
  stored.(Selector') = input.(Selector') ∧
  stored.(Template') =
    PodTemplateSpecV.normalized input.(Template') ∧
  stored.(ServiceName') = input.(ServiceName') ∧
  (stored.(VolumeClaimTemplates') = None ↔ input.(VolumeClaimTemplates') = None) ∧
  Forall2
    (λ input_claim stored_claim,
      stored_claim.(PersistentVolumeClaimV.TypeMeta') = zero_val v1.TypeMeta.t ∧
      stored_claim.(PersistentVolumeClaimV.ObjectMeta') = input_claim.(PersistentVolumeClaimV.ObjectMeta') ∧
      PersistentVolumeClaimSpecV.embedded_created
        input_claim.(PersistentVolumeClaimV.Spec') stored_claim.(PersistentVolumeClaimV.Spec') ∧
      stored_claim.(PersistentVolumeClaimV.Status') = input_claim.(PersistentVolumeClaimV.Status'))
    (volume_claim_templates_list input)
    (volume_claim_templates_list stored) ∧
  validate_additional_create_fields stored = true ∧
  additional_storage_normalized stored = true.

(* Update decoding applies the represented replica default and embedded-PVC
   normalization to a create-valid submitted spec, as it does on create. *)
Definition updated (input stored : t) : Prop :=
  created input stored.

Lemma valid_replicas v :
  valid v → ∃ (i: w32), v.(Replicas') = Some i ∧ 0 ≤ sint.Z i.
Proof. intros (_ & Hreplicas & _). exact Hreplicas. Qed.

End StatefulSetSpecV.
Local Transparent StatefulSetSpecV.deepown.

Module StatefulSetStatusV.
Include StatefulSetView.StatefulSetStatusV.

Local Transparent deepown.
Axiom valid: t → Prop.
Axiom valid_update : t → t → Prop.
Axiom valid_update_dec : ∀ old input, Decision (valid_update old input).
Global Existing Instance valid_update_dec.
Definition created (_input stored : t) : Prop := stored = zero.
Axiom updated : t → t → Prop.

End StatefulSetStatusV.
Local Transparent StatefulSetStatusV.deepown.

Module StatefulSetV.
Include StatefulSetView.StatefulSetV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Definition kind : go_string :=
  "StatefulSet"%go.

Definition meta_key (meta : ObjectMetaV.t) : KKey.t :=
  {|
    KKey.Kind' := kind;
    KKey.Namespace' := meta.(ObjectMetaV.Namespace');
    KKey.Name' := meta.(ObjectMetaV.Name')
  |}.

Definition key (v: t) : KKey.t :=
  meta_key v.(ObjectMeta').

Definition valid (sts: t) : Prop :=
  valid_typemeta kind sts.(TypeMeta') ∧
  valid_resource_version sts.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  ObjectMetaV.valid kind sts.(ObjectMeta') ∧
  StatefulSetSpecV.valid sts.(Spec') ∧
  StatefulSetStatusV.valid sts.(Status').

Definition extra_valid (_sts : t) : Prop := True.

Definition valid_create request_kind ns (sts : t) : Prop :=
  request_kind = kind ∧
  ns ≠ ""%go ∧
  valid_namespace ns ∧
  valid_create_typemeta kind sts.(TypeMeta') ∧
  ObjectMetaV.valid_create kind ns sts.(ObjectMeta') ∧
  StatefulSetSpecV.valid_create sts.(Spec').

Definition valid_update request_kind namespace old_meta old_spec (input : t) : Prop :=
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  (* TODO: Requiring the update input to pass all current create validation is
     too strong. Kubernetes deliberately does not call [ValidateStatefulSet]
     from [ValidateStatefulSetUpdate], because doing so would revalidate names
     and prevent updates to legacy StatefulSets whose names were accepted under
     older validation rules. Update validation also tolerates invalid values in
     immutable legacy fields: it allows an existing invalid service name, skips
     validation of existing volume-claim templates, and may skip Pod-template
     validation when the old template is already invalid.

     Replace this conjunct with an update-specific predicate that models the
     relaxed validation relative to [old_meta] and [old_spec]. The same fix is
     needed for [StatefulSetSpecV.valid_update], which currently requires
     [StatefulSetSpecV.valid_create input]. Until then, [valid_update] is only a
     sufficient condition for successful updates and does not characterize all
     updates accepted by Kubernetes.

     Upstream implementation:
     https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L237-L271 *)
  valid_create request_kind namespace input ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  StatefulSetSpecV.valid_update old_spec input.(Spec').

Definition valid_status_update request_kind namespace old_meta old_status (input : t) : Prop :=
  request_kind = kind ∧
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  StatefulSetStatusV.valid_update old_status input.(Status').

Definition valid_without_meta (sts: t) : Prop :=
  StatefulSetSpecV.valid sts.(Spec') ∧
  StatefulSetStatusV.valid sts.(Status').

Definition created (namespace : go_string) (input stored : t) : Prop :=
  valid_typemeta kind stored.(TypeMeta') ∧
  ObjectMetaV.created namespace input.(ObjectMeta') stored.(ObjectMeta') ∧
  stored.(ObjectMeta').(ObjectMetaV.Generation') = W64 1 ∧
  StatefulSetSpecV.created input.(Spec') stored.(Spec') ∧
  StatefulSetStatusV.created input.(Status') stored.(Status').

Definition status_updated (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  ObjectMetaV.updated input.(ObjectMeta') stored.(ObjectMeta') ∧
  StatefulSetStatusV.updated input.(Status') stored.(Status').

Definition updated (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  ObjectMetaV.updated input.(ObjectMeta') stored.(ObjectMeta') ∧
  StatefulSetSpecV.updated input.(Spec') stored.(Spec').

#[global]
Instance top_level_instance : top_level Σ t :=
  Build_top_level Σ t ObjectMetaV.t StatefulSetSpecV.t StatefulSetStatusV.t
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
  struct_field_ref v1.StatefulSet.t "TypeMeta" l.

Definition objectmeta_ptr l: loc :=
  struct_field_ref v1.StatefulSet.t "ObjectMeta" l.

Definition spec_ptr l: loc :=
  struct_field_ref v1.StatefulSet.t "Spec" l.

Definition status_ptr l: loc :=
  struct_field_ref v1.StatefulSet.t "Status" l.

Definition update_objectmeta (v: t) (m: ObjectMetaV.t) : t :=
  v <| ObjectMeta' := m |>.

Definition deepown_without_meta (c: v1.StatefulSet.t) (v: t) dq: iProp Σ :=
  "Hdeepown_spec" ∷ StatefulSetSpecV.deepown c.(v1.StatefulSet.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ StatefulSetStatusV.deepown c.(v1.StatefulSet.Status') v.(Status') dq.

Definition deepown_l_without_meta l v (dq: dfrac): iProp Σ :=
  ∃ c,
    spec_ptr l ↦{dq} c.(v1.StatefulSet.Spec') ∗
    status_ptr l ↦{dq} c.(v1.StatefulSet.Status') ∗
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
    StatefulSetSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
    StatefulSetStatusV.deepown_l (status_ptr l) v.(Status') dq.
Proof.
  unfold deepown_l, deepown.
  iIntros "H".
  iDestruct "H" as (c) "[Hl Hdeepown]".
  iDestruct "Hdeepown" as "(%Htypemeta & Hobjectmeta & Hspec & Hstatus)".
  iDestruct (struct_fields_split (V:=v1.StatefulSet.t) with "Hl") as "[Hfields %Hnot_null]".
  iNamedPrefix "Hfields" "H".
  iSplitR; first done.
  rewrite -Htypemeta.
  iFrame "HTypeMeta".
  iSplitL "HObjectMeta Hobjectmeta".
  { unfold ObjectMetaV.deepown_l, objectmeta_ptr. iFrame. }
  iSplitL "HSpec Hspec".
  { unfold StatefulSetSpecV.deepown_l, spec_ptr. iFrame. }
  unfold StatefulSetStatusV.deepown_l, status_ptr. iFrame.
Qed.

Lemma deepown_l_merge l v vm dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) vm dq ∗
  StatefulSetSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  StatefulSetStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
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
  iAssert (typed_pointsto_def l (v1.StatefulSet.mk v_typemeta cm cspec cstatus) dq)
    with "[HTypeMeta HObjectMeta HSpec HStatus]" as "Hfields".
  { simpl. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.StatefulSet.t)
    l (v1.StatefulSet.mk v_typemeta cm cspec cstatus) dq Hnot_null with "Hfields") as "Hl".
  iExists (v1.StatefulSet.mk v_typemeta cm cspec cstatus).
  iSplitL "Hl"; first iExact "Hl".
  iSplitR "Hobjectmeta Hspec Hstatus"; first done.
  simpl. iFrame.
Qed.

Lemma deepown_l_restore l v dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
  StatefulSetSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  StatefulSetStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
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
End StatefulSetV.
