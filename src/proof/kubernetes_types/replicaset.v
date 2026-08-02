From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export labelselector pod.

Module ReplicaSetSpecV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {
  Replicas' : option w32;
  MinReadySeconds' : w32;
  Selector' : option LabelSelectorV.t;
  Template' : PodTemplateSpecV.t;
}.

(* The admission predicate used for both create validation and the general
   validation phase of update. It deliberately permits fields that schema
   defaulting normalizes before storage.
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/v1/defaults.go#L148-L153 *)
Definition valid_create (rs : t) : Prop :=
  (match rs.(Replicas') with
   | Some replicas => 0 ≤ sint.Z replicas
   | None => True
   end) ∧
  0 ≤ sint.Z rs.(MinReadySeconds') ∧
  (∃ selector,
    rs.(Selector') = Some selector ∧
    LabelSelectorV.valid selector ∧
    ¬ LabelSelectorV.empty selector ∧
    LabelSelectorV.matches
      selector rs.(Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')) ∧
  PodTemplateSpecV.valid rs.(Template').

(* A stored ReplicaSet spec satisfies admission validation, and schema
   defaulting has additionally made [Replicas'] non-nil.
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L806-L854 *)
Definition valid (rs : t) : Prop :=
  valid_create rs ∧
  ∃ replicas, rs.(Replicas') = Some replicas ∧ 0 ≤ sint.Z replicas.

(* Kubernetes allows the represented replica count, minimum-ready duration,
   and Pod template to change, but keeps the selector immutable:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L763-L770 *)
Definition valid_update (old new : t) : Prop :=
  new.(Selector') = old.(Selector').

Global Instance valid_update_dec old new :
  Decision (valid_update old new).
Proof. unfold valid_update. solve_decision. Defined.

Lemma valid_update_refl spec :
  valid_update spec spec.
Proof. unfold valid_update. done. Qed.

(* ReplicaSet create defaults an omitted replica count to one; the other
   represented fields are preserved. *)
Definition created (input stored : t) : Prop :=
  stored.(Replicas') = Some (default (W32 1) input.(Replicas')) ∧
  stored.(MinReadySeconds') = input.(MinReadySeconds') ∧
  stored.(Selector') = input.(Selector') ∧
  stored.(Template') = input.(Template').

(* Update callers require the submitted ReplicaSet to satisfy [valid], so its
   represented schema defaults are already present. *)
Definition updated (input stored : t) : Prop :=
  stored = input.

Lemma valid_replicas :
  ∀ v, valid v →
  ∃ (i: w32), v.(Replicas') = Some i ∧ 0 ≤ sint.Z i.
Proof. intros v (_ & Hreplicas). exact Hreplicas. Qed.

Lemma valid_template :
  ∀ v, valid v →
  PodTemplateSpecV.valid v.(Template').
Proof.
  intros v (Hvalid_create & _).
  destruct Hvalid_create as (_ & _ & _ & Htemplate).
  exact Htemplate.
Qed.

Definition deepown (c: v1.ReplicaSetSpec.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_replicas_none" ∷ ⌜c.(v1.ReplicaSetSpec.Replicas') = null ↔ v.(Replicas') = None⌝ ∗
  "Hdeepown_replicas_some" ∷ (match v.(Replicas') with
  | Some i => ∃ replicas, c.(v1.ReplicaSetSpec.Replicas') ↦{dq} replicas ∗ ⌜ replicas = i ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_minreadyseconds" ∷ ⌜ c.(v1.ReplicaSetSpec.MinReadySeconds') = v.(MinReadySeconds') ⌝ ∗
  "%Hdeepown_selector_none" ∷
    ⌜c.(v1.ReplicaSetSpec.Selector') = null ↔ v.(Selector') = None⌝ ∗
  "Hdeepown_selector_some" ∷
    (match v.(Selector') with
    | Some selector =>
        ∃ selector_c,
          c.(v1.ReplicaSetSpec.Selector') ↦{dq} selector_c ∗
          LabelSelectorV.deepown selector_c selector dq
    | None => True%I
    end) ∗
  "Hdeepown_template" ∷ PodTemplateSpecV.deepown c.(v1.ReplicaSetSpec.Template') v.(Template') dq.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End ReplicaSetSpecV.

Module ReplicaSetStatusV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {}.
(* This includes validation and normalization of the unmodeled status fields. *)
Axiom valid : t → Prop.
Axiom deepown : v1.ReplicaSetStatus.t → t → dfrac → iProp Σ.

Definition created (_input stored : t) : Prop :=
  valid stored.

Definition updated (input stored : t) : Prop :=
  stored = input.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End ReplicaSetStatusV.

Module ReplicaSetV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : ObjectMetaV.t;
  Spec' : ReplicaSetSpecV.t;
  Status' : ReplicaSetStatusV.t;
}.

Definition kind : go_string :=
   "ReplicaSet"%go.

Definition meta_key (meta : ObjectMetaV.t) : KKey.t :=
  {|
    KKey.Kind' := kind;
    KKey.Namespace' := meta.(ObjectMetaV.Namespace');
    KKey.Name' := meta.(ObjectMetaV.Name')
  |}.

Definition key (v: t) : KKey.t :=
  meta_key v.(ObjectMeta').

Definition valid (rs: t) : Prop :=
  valid_typemeta kind rs.(TypeMeta') ∧
  valid_resource_version rs.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  ObjectMetaV.valid kind rs.(ObjectMeta') ∧
  ReplicaSetSpecV.valid rs.(Spec') ∧
  ReplicaSetStatusV.valid rs.(Status').

Definition valid_nameless_create ns (rs : t) : Prop :=
  valid_create_typemeta kind rs.(TypeMeta') ∧
  ObjectMetaV.valid_nameless_create kind ns rs.(ObjectMeta') ∧
  ReplicaSetSpecV.valid_create rs.(Spec').

Definition valid_named_create ns (rs : t) : Prop :=
  valid_create_typemeta kind rs.(TypeMeta') ∧
  ObjectMetaV.valid_named_create kind ns rs.(ObjectMeta') ∧
  ReplicaSetSpecV.valid_create rs.(Spec').

Definition valid_without_meta (rs: t) : Prop :=
  ReplicaSetSpecV.valid rs.(Spec') ∧
  ReplicaSetStatusV.valid rs.(Status').

Definition deepown (c: v1.ReplicaSet.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.ReplicaSet.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.ReplicaSet.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_spec" ∷ ReplicaSetSpecV.deepown c.(v1.ReplicaSet.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ ReplicaSetStatusV.deepown c.(v1.ReplicaSet.Status') v.(Status') dq.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

Definition typemeta_ptr l: loc :=
  struct_field_ref v1.ReplicaSet.t "TypeMeta" l.

Definition objectmeta_ptr l: loc :=
  struct_field_ref v1.ReplicaSet.t "ObjectMeta" l.

Definition spec_ptr l: loc :=
  struct_field_ref v1.ReplicaSet.t "Spec" l.

Definition status_ptr l: loc :=
  struct_field_ref v1.ReplicaSet.t "Status" l.

Definition update_objectmeta (v: t) (m: ObjectMetaV.t) : t :=
  v <| ObjectMeta' := m |>.

Definition deepown_without_meta (c: v1.ReplicaSet.t) (v: t) dq: iProp Σ :=
  "Hdeepown_spec" ∷ ReplicaSetSpecV.deepown c.(v1.ReplicaSet.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ ReplicaSetStatusV.deepown c.(v1.ReplicaSet.Status') v.(Status') dq.

Definition deepown_l_without_meta l v (dq: dfrac): iProp Σ :=
  ∃ c,
  spec_ptr l ↦{dq} c.(v1.ReplicaSet.Spec') ∗
  status_ptr l ↦{dq} c.(v1.ReplicaSet.Status') ∗
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
    ReplicaSetSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
    ReplicaSetStatusV.deepown_l (status_ptr l) v.(Status') dq.
Proof.
  unfold deepown_l, deepown.
  iIntros "H".
  iDestruct "H" as (c) "[Hl Hdeepown]".
  iDestruct "Hdeepown" as "(%Htypemeta & Hobjectmeta & Hspec & Hstatus)".
  iDestruct (struct_fields_split (V:=v1.ReplicaSet.t) with "Hl") as "[Hfields %Hnot_null]".
  iNamedPrefix "Hfields" "H".
  iSplitR; first done.
  rewrite -Htypemeta.
  iFrame "HTypeMeta".
  iSplitL "HObjectMeta Hobjectmeta".
  { unfold ObjectMetaV.deepown_l, objectmeta_ptr. iFrame. }
  iSplitL "HSpec Hspec".
  { unfold ReplicaSetSpecV.deepown_l, spec_ptr. iFrame. }
  unfold ReplicaSetStatusV.deepown_l, status_ptr. iFrame.
Qed.

Lemma deepown_l_merge l v vm dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) vm dq ∗
  ReplicaSetSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  ReplicaSetStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
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
  iAssert (typed_pointsto_def l (v1.ReplicaSet.mk v_typemeta cm cspec cstatus) dq)
    with "[HTypeMeta HObjectMeta HSpec HStatus]" as "Hfields".
  { simpl. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.ReplicaSet.t)
    l (v1.ReplicaSet.mk v_typemeta cm cspec cstatus) dq Hnot_null with "Hfields") as "Hl".
  iExists (v1.ReplicaSet.mk v_typemeta cm cspec cstatus).
  iSplitL "Hl"; first iExact "Hl".
  iSplitR "Hobjectmeta Hspec Hstatus"; first done.
  simpl. iFrame.
Qed.

Lemma deepown_l_restore l v dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
  ReplicaSetSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  ReplicaSetStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
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
End ReplicaSetV.
