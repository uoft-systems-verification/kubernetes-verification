From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export pod persistentvolumeclaim.

Module StatefulSetSpecV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {
  Replicas' : option w32;
  (* Selector' : loc; *)
  Template' : PodTemplateSpecV.t;
  VolumeClaimTemplates' : list PersistentVolumeClaimV.t;
  ServiceName' : go_string;
  (* PodManagementPolicy' : v1.PodManagementPolicyType.t; *)
  (* UpdateStrategy' : v1.StatefulSetUpdateStrategy.t; *)
  (* RevisionHistoryLimit' : loc; *)
  (* MinReadySeconds' : w32; *)
  (* PersistentVolumeClaimRetentionPolicy' : loc; *)
  (* Ordinals' : loc; *)
}.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L117-L178 *)
Definition valid (spec : t) : Prop :=
  (∃ replicas, spec.(Replicas') = Some replicas ∧ 0 ≤ sint.Z replicas) ∧
  PodTemplateSpecV.valid spec.(Template') ∧
  Forall (λ pvc, PersistentVolumeClaimSpecV.valid pvc.(PersistentVolumeClaimV.Spec')) spec.(VolumeClaimTemplates') ∧
  (spec.(ServiceName') = ""%go ∨ valid_dns1123_label spec.(ServiceName')).

Lemma valid_replicas :
  ∀ v, valid v →
  ∃ (i: w32), v.(Replicas') = Some i ∧ 0 ≤ sint.Z i.
Proof. intros v (Hreplicas & _). exact Hreplicas. Qed.

Definition deepown (c: v1.StatefulSetSpec.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_replicas_none" ∷ ⌜c.(v1.StatefulSetSpec.Replicas') = null ↔ v.(Replicas') = None⌝ ∗
  "Hdeepown_replicas_some" ∷ (match v.(Replicas') with
  | Some i => ∃ replicas, c.(v1.StatefulSetSpec.Replicas') ↦{dq} replicas ∗ ⌜ replicas = i ⌝
  | None => True%I
  end) ∗
  "Hdeepown_template" ∷ PodTemplateSpecV.deepown c.(v1.StatefulSetSpec.Template') v.(Template') dq ∗
  "Hdeepown_volumeclaimtemplates" ∷
    (∃ claim_templates,
      deepown_list c.(v1.StatefulSetSpec.VolumeClaimTemplates') claim_templates
        v.(VolumeClaimTemplates')
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
Axiom valid: t → Prop.
Axiom deepown : v1.StatefulSetStatus.t → t → dfrac → iProp Σ.

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
