From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export labelselector pod persistentvolumeclaim.

Module StatefulSetSpecV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {
  Replicas' : option w32;
  Selector' : option LabelSelectorV.t;
  Template' : PodTemplateSpecV.t;
  VolumeClaimTemplates' : option (list PersistentVolumeClaimV.t);
  ServiceName' : go_string;
  (* PodManagementPolicy' : v1.PodManagementPolicyType.t; *)
  (* UpdateStrategy' : v1.StatefulSetUpdateStrategy.t; *)
  (* RevisionHistoryLimit' : loc; *)
  (* MinReadySeconds' : w32; *)
  (* PersistentVolumeClaimRetentionPolicy' : loc; *)
  (* Ordinals' : loc; *)
}.

(* Kubernetes validation and semantic equality treat nil and allocated empty
   volume-claim-template slices identically. Preserve that representation
   distinction in [VolumeClaimTemplates'] and use this projection where only
   the logical sequence matters. *)
Definition volume_claim_templates_list
    (spec : t) : list PersistentVolumeClaimV.t :=
  default [] spec.(VolumeClaimTemplates').

Definition volume_claim_template_names (spec : t) : list go_string :=
  (λ pvc,
    pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name'))
  <$> volume_claim_templates_list spec.

(* Before validating a StatefulSet's Pod template, Kubernetes replaces every
   template volume whose name occurs in [VolumeClaimTemplates] with the
   generated PVC-backed volume. These are precisely the original volumes that
   survive that replacement. *)
Definition preserved_template_volumes (spec : t) : list VolumeV.t :=
  filter
    (λ volume,
      volume.(VolumeV.Name') ∉ volume_claim_template_names spec)
    (PodSpecV.volumes_list spec.(Template').(PodTemplateSpecV.Spec')).

(* The projection of StatefulSet's effective Pod-template validation onto the
   represented metadata and PodSpec fields. Kubernetes clears the template's
   Hostname and Subdomain because the controller overwrites them, so neither
   field is constrained here. Claim-template volumes are handled separately
   below; their names are map keys and are therefore unique, while filtering
   makes them disjoint from the preserved original volumes.
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L193-L214 *)
Definition valid_template (spec : t) : Prop :=
  valid_labels
    spec.(Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') ∧
  valid_annotations
    spec.(Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations') ∧
  Forall VolumeV.valid (preserved_template_volumes spec) ∧
  NoDup
    (VolumeV.Name' <$> preserved_template_volumes spec).

(* The admission predicate used for both create validation and the general
   validation phase of update. Kubernetes may still need to default an omitted
   replica count and apply schema defaults to embedded volume claim templates
   before the object reaches stored [valid]. *)
Definition valid_create (spec : t) : Prop :=
  (match spec.(Replicas') with
   | Some replicas => 0 ≤ sint.Z replicas
   | None => True
   end) ∧
  (∃ selector,
    spec.(Selector') = Some selector ∧
    LabelSelectorV.valid selector ∧
    ¬ LabelSelectorV.empty selector ∧
    LabelSelectorV.matches
      selector spec.(Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')) ∧
  valid_template spec ∧
  (* Kubernetes injects every claim-template name as a Pod volume name before
     validating the StatefulSet's Pod template, so each name must be a
     DNS-1123 label:
     https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L193-L214 *)
  Forall
    (λ pvc,
      valid_dns1123_label
        pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name'))
    (volume_claim_templates_list spec) ∧
  Forall (λ pvc, PersistentVolumeClaimSpecV.valid_create pvc.(PersistentVolumeClaimV.Spec'))
    (volume_claim_templates_list spec) ∧
  (spec.(ServiceName') = ""%go ∨ valid_dns1123_label spec.(ServiceName')).

(* A stored StatefulSet spec satisfies admission validation. Schema defaulting
   has additionally made [Replicas'] non-nil, zeroed the TypeMeta of embedded
   PVC templates, and normalized those embedded PVC specs.
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L117-L178 *)
Definition valid (spec : t) : Prop :=
  valid_create spec ∧
  (∃ replicas, spec.(Replicas') = Some replicas ∧ 0 ≤ sint.Z replicas) ∧
  Forall (λ pvc,
    pvc.(PersistentVolumeClaimV.TypeMeta') = zero_val v1.TypeMeta.t ∧
    PersistentVolumeClaimSpecV.valid_embedded
      pvc.(PersistentVolumeClaimV.Spec'))
    (volume_claim_templates_list spec).

(* Of the represented fields, Kubernetes permits updates to Replicas and the
   Pod template. Selector, volume-claim templates, and service name remain
   immutable:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L238-L275 *)
Definition valid_update (old new : t) : Prop :=
  new.(Selector') = old.(Selector') ∧
  volume_claim_templates_list new = volume_claim_templates_list old ∧
  new.(ServiceName') = old.(ServiceName').

Global Instance valid_update_dec old new :
  Decision (valid_update old new).
Proof. unfold valid_update. solve_decision. Defined.

Lemma valid_update_refl spec :
  valid_update spec spec.
Proof. unfold valid_update. done. Qed.

(* StatefulSet creation defaults an omitted replica count, preserves the
   directly represented fields, and normalizes each embedded PVC template.
   The PVC spec relation is necessarily abstract until those fields are
   translated. *)
Definition created (input stored : t) : Prop :=
  stored.(Replicas') = Some (default (W32 1) input.(Replicas')) ∧
  stored.(Selector') = input.(Selector') ∧
  stored.(Template') = input.(Template') ∧
  stored.(ServiceName') = input.(ServiceName') ∧
  (stored.(VolumeClaimTemplates') = None ↔
    input.(VolumeClaimTemplates') = None) ∧
  Forall2
    (λ input_claim stored_claim,
      stored_claim.(PersistentVolumeClaimV.TypeMeta') =
        zero_val v1.TypeMeta.t ∧
      stored_claim.(PersistentVolumeClaimV.ObjectMeta') =
        input_claim.(PersistentVolumeClaimV.ObjectMeta') ∧
      PersistentVolumeClaimSpecV.embedded_created
        input_claim.(PersistentVolumeClaimV.Spec')
        stored_claim.(PersistentVolumeClaimV.Spec') ∧
      stored_claim.(PersistentVolumeClaimV.Status') =
        input_claim.(PersistentVolumeClaimV.Status'))
    (volume_claim_templates_list input)
    (volume_claim_templates_list stored).

(* Update callers require the submitted StatefulSet to satisfy [valid], so its
   represented schema defaults and embedded-PVC normalization are already
   present. *)
Definition updated (input stored : t) : Prop :=
  stored = input.

Lemma valid_replicas :
  ∀ v, valid v →
  ∃ (i: w32), v.(Replicas') = Some i ∧ 0 ≤ sint.Z i.
Proof. intros v (_ & Hreplicas & _). exact Hreplicas. Qed.

Definition deepown (c: v1.StatefulSetSpec.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_replicas_none" ∷ ⌜c.(v1.StatefulSetSpec.Replicas') = null ↔ v.(Replicas') = None⌝ ∗
  "Hdeepown_replicas_some" ∷ (match v.(Replicas') with
  | Some i => ∃ replicas, c.(v1.StatefulSetSpec.Replicas') ↦{dq} replicas ∗ ⌜ replicas = i ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_selector_none" ∷
    ⌜c.(v1.StatefulSetSpec.Selector') = null ↔ v.(Selector') = None⌝ ∗
  "Hdeepown_selector_some" ∷
    (match v.(Selector') with
    | Some selector =>
        ∃ selector_c,
          c.(v1.StatefulSetSpec.Selector') ↦{dq} selector_c ∗
          LabelSelectorV.deepown selector_c selector dq
    | None => True%I
    end) ∗
  "Hdeepown_template" ∷ PodTemplateSpecV.deepown c.(v1.StatefulSetSpec.Template') v.(Template') dq ∗
  "%Hdeepown_volumeclaimtemplates_none" ∷
    ⌜c.(v1.StatefulSetSpec.VolumeClaimTemplates') = slice.nil ↔
      v.(VolumeClaimTemplates') = None⌝ ∗
  "Hdeepown_volumeclaimtemplates" ∷
    (∃ claim_templates,
      deepown_list c.(v1.StatefulSetSpec.VolumeClaimTemplates') claim_templates
        (volume_claim_templates_list v)
        (λ claim_template pure_claim_template,
          PersistentVolumeClaimV.deepown claim_template pure_claim_template dq)) ∗
  "%Hdeepown_servicename" ∷ ⌜c.(v1.StatefulSetSpec.ServiceName') = v.(ServiceName')⌝.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End StatefulSetSpecV.

Module StatefulSetStatusV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Axiom t : Type.
(* This includes validation and normalization of the unmodeled status fields. *)
Axiom valid: t → Prop.
Axiom deepown : v1.StatefulSetStatus.t → t → dfrac → iProp Σ.

Definition created (_input stored : t) : Prop :=
  valid stored.

Definition updated (input stored : t) : Prop :=
  stored = input.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End StatefulSetStatusV.

Module StatefulSetV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : ObjectMetaV.t;
  Spec' : StatefulSetSpecV.t;
  Status' : StatefulSetStatusV.t;
}.

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

Definition valid_nameless_create ns (sts : t) : Prop :=
  valid_create_typemeta kind sts.(TypeMeta') ∧
  ObjectMetaV.valid_nameless_create kind ns sts.(ObjectMeta') ∧
  StatefulSetSpecV.valid_create sts.(Spec').

Definition valid_named_create ns (sts : t) : Prop :=
  valid_create_typemeta kind sts.(TypeMeta') ∧
  ObjectMetaV.valid_named_create kind ns sts.(ObjectMeta') ∧
  StatefulSetSpecV.valid_create sts.(Spec').

Definition valid_without_meta (sts: t) : Prop :=
  StatefulSetSpecV.valid sts.(Spec') ∧
  StatefulSetStatusV.valid sts.(Status').

Definition deepown (c: v1.StatefulSet.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.StatefulSet.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.StatefulSet.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_spec" ∷ StatefulSetSpecV.deepown c.(v1.StatefulSet.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ StatefulSetStatusV.deepown c.(v1.StatefulSet.Status') v.(Status') dq.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

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
