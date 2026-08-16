From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export replicaset.
From New.proof.kubernetes_types Require Import top_level.

Module DeploymentSpecV.
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
  (* The rollout strategy is not represented: the simplified controller
     ignores maxSurge/maxUnavailable and scales ReplicaSets straight to their
     target counts. *)
  (* Strategy' : v1.DeploymentStrategy.t; *)
  (* RevisionHistoryLimit' : loc; *)
  (* Paused' : bool; *)
  (* ProgressDeadlineSeconds' : loc; *)
}.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L638-L675 *)
(* This is the projection of Kubernetes' Deployment spec validation onto the
   represented fields. The template is validated exactly as a ReplicaSet's is
   (both go through ValidatePodTemplateSpecForReplicaSet); checks on unmodeled
   PodSpec fields are outside this projection. *)
Definition valid (spec : t) : Prop :=
  (∃ replicas, spec.(Replicas') = Some replicas ∧ 0 ≤ sint.Z replicas) ∧
  0 ≤ sint.Z spec.(MinReadySeconds') ∧
  (∃ selector,
    spec.(Selector') = Some selector ∧
    LabelSelectorV.valid selector ∧
    ¬ LabelSelectorV.empty selector ∧
    LabelSelectorV.matches selector spec.(Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')) ∧
  PodTemplateSpecV.valid spec.(Template').

(* On create the replica count may be omitted; defaulting fills in 1:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/v1/defaults.go#L38-L43 *)
Definition valid_create (spec : t) : Prop :=
  (match spec.(Replicas') with
   | Some replicas => 0 ≤ sint.Z replicas
   | None => True
   end) ∧
  0 ≤ sint.Z spec.(MinReadySeconds') ∧
  (∃ selector,
    spec.(Selector') = Some selector ∧
    LabelSelectorV.valid selector ∧
    ¬ LabelSelectorV.empty selector ∧
    LabelSelectorV.matches selector spec.(Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')) ∧
  PodTemplateSpecV.valid spec.(Template').

(* Kubernetes allows the represented replica count, minimum-ready duration, and
   Pod template to change, but keeps the selector immutable. This relation is
   also meaningful when [old] is only [valid_create], before its replica count
   has been defaulted:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L709-L714 *)
Definition valid_update (old input : t) : Prop :=
  valid_create input ∧
  input.(Selector') = old.(Selector').

Global Instance valid_update_dec old input :
  Decision (valid_update old input).
Proof.
  unfold valid_update, valid_create.
  apply and_dec.
  - apply and_dec; first (destruct input.(Replicas'); apply _).
    apply and_dec; first apply _.
    apply and_dec; last apply _.
    apply LabelSelectorV.exists_eq_some_dec.
    intros selector. apply _.
  - apply _.
Defined.

Lemma valid_update_refl spec :
  valid_create spec →
  valid_update spec spec.
Proof. unfold valid_update. done. Qed.

Lemma valid_replicas v :
  valid v → ∃ (i: w32), v.(Replicas') = Some i ∧ 0 ≤ sint.Z i.
Proof. intros (Hreplicas & _). exact Hreplicas. Qed.

Lemma valid_template v :
  valid v → PodTemplateSpecV.valid v.(Template').
Proof. intros (_ & _ & _ & Htemplate). exact Htemplate. Qed.

(* Creation fills an omitted replica count with one and removes obsolete
   init-container annotations from the Pod template during version conversion.
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/v1/defaults.go#L38-L73
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/core/v1/conversion.go#L247-L254 *)
Definition created (input stored : t) : Prop :=
  stored.(Replicas') = (match input.(Replicas') with
                        | Some replicas => Some replicas
                        | None => Some (W32 1)
                        end) ∧
  stored.(MinReadySeconds') = input.(MinReadySeconds') ∧
  stored.(Selector') = input.(Selector') ∧
  stored.(Template') =
    input.(Template') <| PodTemplateSpecV.ObjectMeta' :=
      pod_objectmeta_after_conversion input.(Template').(PodTemplateSpecV.ObjectMeta') |>.

(* Likewise on update: decoder defaulting precedes PrepareForUpdate, which
   restores the old status and bumps the generation without otherwise changing
   the represented spec:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/apps/deployment/strategy.go#L110-L124
   Thus [updated] includes the same replica default as [created]. *)
Definition updated (input stored : t) : Prop :=
  created input stored.

(* A created spec has an explicit, nonnegative replica count, so a spec that
   passes create validation is valid once stored. *)
Lemma valid_create_created spec spec' :
  valid_create spec →
  created spec spec' →
  valid spec'.
Proof.
  intros (Hreplicas & Hminready & Hselector & Htemplate)
    (Hreplicas' & Hminready' & Hselector' & Htemplate').
  split_and!.
  - destruct spec.(Replicas') as [replicas|].
    + exists replicas. split; [exact Hreplicas'|exact Hreplicas].
    + exists (W32 1). split; [exact Hreplicas'|word].
  - rewrite Hminready'. exact Hminready.
  - rewrite Hselector' Htemplate'. exact Hselector.
  - rewrite Htemplate'. apply PodTemplateSpecV.valid_after_conversion. exact Htemplate.
Qed.

Definition deepown (c: v1.DeploymentSpec.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_replicas_none" ∷ ⌜c.(v1.DeploymentSpec.Replicas') = null ↔ v.(Replicas') = None⌝ ∗
  "Hdeepown_replicas_some" ∷ (match v.(Replicas') with
    | Some i => ∃ replicas, c.(v1.DeploymentSpec.Replicas') ↦{dq} replicas ∗ ⌜ replicas = i ⌝
    | None => True%I
    end) ∗
  "%Hdeepown_minreadyseconds" ∷ ⌜ c.(v1.DeploymentSpec.MinReadySeconds') = v.(MinReadySeconds') ⌝ ∗
  "%Hdeepown_selector_none" ∷ ⌜c.(v1.DeploymentSpec.Selector') = null ↔ v.(Selector') = None⌝ ∗
  "Hdeepown_selector_some" ∷ (match v.(Selector') with
    | Some selector =>
        ∃ selector_c,
          c.(v1.DeploymentSpec.Selector') ↦{dq} selector_c ∗
          LabelSelectorV.deepown selector_c selector dq
    | None => True%I
    end) ∗
  "Hdeepown_template" ∷ PodTemplateSpecV.deepown c.(v1.DeploymentSpec.Template') v.(Template') dq.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End DeploymentSpecV.

Module DeploymentStatusV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {}.
Axiom valid : t → Prop.
Axiom valid_update : t → t → Prop.
Axiom valid_update_dec : ∀ old input, Decision (valid_update old input).
Global Existing Instance valid_update_dec.
Axiom created : t → t → Prop.
Axiom updated : t → t → Prop.
Axiom deepown : v1.DeploymentStatus.t → t → dfrac → iProp Σ.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End DeploymentStatusV.

Module DeploymentV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : ObjectMetaV.t;
  Spec' : DeploymentSpecV.t;
  Status' : DeploymentStatusV.t;
}.

Definition kind : go_string :=
   "Deployment"%go.

Definition meta_key (meta : ObjectMetaV.t) : KKey.t :=
  {|
    KKey.Kind' := kind;
    KKey.Namespace' := meta.(ObjectMetaV.Namespace');
    KKey.Name' := meta.(ObjectMetaV.Name')
  |}.

Definition key (v: t) : KKey.t :=
  meta_key v.(ObjectMeta').

Definition valid (d: t) : Prop :=
  valid_typemeta kind d.(TypeMeta') ∧
  valid_resource_version d.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  ObjectMetaV.valid kind d.(ObjectMeta') ∧
  DeploymentSpecV.valid d.(Spec') ∧
  DeploymentStatusV.valid d.(Status').

Definition extra_valid (_d : t) : Prop := True.

Definition valid_create request_kind ns (d : t) : Prop :=
  request_kind = kind ∧
  ns ≠ ""%go ∧
  valid_namespace ns ∧
  valid_create_typemeta kind d.(TypeMeta') ∧
  ObjectMetaV.valid_create kind ns d.(ObjectMeta') ∧
  DeploymentSpecV.valid_create d.(Spec').

Definition valid_update request_kind namespace old_meta old_spec (input : t) : Prop :=
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  valid_create request_kind namespace input ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  DeploymentSpecV.valid_update old_spec input.(Spec').

Definition valid_status_update request_kind namespace old_meta old_status (input : t) : Prop :=
  request_kind = kind ∧
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  DeploymentStatusV.valid_update old_status input.(Status').

Definition valid_without_meta (d: t) : Prop :=
  DeploymentSpecV.valid d.(Spec') ∧
  DeploymentStatusV.valid d.(Status').

Definition created (namespace : go_string) (input stored : t) : Prop :=
  valid_typemeta kind stored.(TypeMeta') ∧
  ObjectMetaV.created namespace input.(ObjectMeta') stored.(ObjectMeta') ∧
  stored.(ObjectMeta').(ObjectMetaV.Generation') = W64 1 ∧
  DeploymentSpecV.created input.(Spec') stored.(Spec') ∧
  DeploymentStatusV.created input.(Status') stored.(Status').

Definition updated (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  ObjectMetaV.updated input.(ObjectMeta') stored.(ObjectMeta') ∧
  DeploymentSpecV.updated input.(Spec') stored.(Spec').

Definition status_updated (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  ObjectMetaV.updated input.(ObjectMeta') stored.(ObjectMeta') ∧
  DeploymentStatusV.updated input.(Status') stored.(Status').

Definition deepown (c: v1.Deployment.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.Deployment.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.Deployment.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_spec" ∷ DeploymentSpecV.deepown c.(v1.Deployment.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ DeploymentStatusV.deepown c.(v1.Deployment.Status') v.(Status') dq.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

#[global]
Instance top_level_instance : top_level Σ t :=
  Build_top_level Σ t ObjectMetaV.t DeploymentSpecV.t DeploymentStatusV.t
    valid
    extra_valid
    valid_create
    valid_update
    valid_status_update
    created
    updated
    status_updated
    deepown_l.

Definition typemeta_ptr l: loc :=
  struct_field_ref v1.Deployment.t "TypeMeta" l.

Definition objectmeta_ptr l: loc :=
  struct_field_ref v1.Deployment.t "ObjectMeta" l.

Definition spec_ptr l: loc :=
  struct_field_ref v1.Deployment.t "Spec" l.

Definition status_ptr l: loc :=
  struct_field_ref v1.Deployment.t "Status" l.

Definition update_objectmeta (v: t) (m: ObjectMetaV.t) : t :=
  v <| ObjectMeta' := m |>.

Definition deepown_without_meta (c: v1.Deployment.t) (v: t) dq: iProp Σ :=
  "Hdeepown_spec" ∷ DeploymentSpecV.deepown c.(v1.Deployment.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ DeploymentStatusV.deepown c.(v1.Deployment.Status') v.(Status') dq.

Definition deepown_l_without_meta l v (dq: dfrac): iProp Σ :=
  ∃ c,
    spec_ptr l ↦{dq} c.(v1.Deployment.Spec') ∗
    status_ptr l ↦{dq} c.(v1.Deployment.Status') ∗
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
    DeploymentSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
    DeploymentStatusV.deepown_l (status_ptr l) v.(Status') dq.
Proof.
  unfold deepown_l, deepown.
  iIntros "H".
  iDestruct "H" as (c) "[Hl Hdeepown]".
  iDestruct "Hdeepown" as "(%Htypemeta & Hobjectmeta & Hspec & Hstatus)".
  iDestruct (struct_fields_split (V:=v1.Deployment.t) with "Hl") as "[Hfields %Hnot_null]".
  iNamedPrefix "Hfields" "H".
  iSplitR; first done.
  rewrite -Htypemeta.
  iFrame "HTypeMeta".
  iSplitL "HObjectMeta Hobjectmeta".
  { unfold ObjectMetaV.deepown_l, objectmeta_ptr. iFrame. }
  iSplitL "HSpec Hspec".
  { unfold DeploymentSpecV.deepown_l, spec_ptr. iFrame. }
  unfold DeploymentStatusV.deepown_l, status_ptr. iFrame.
Qed.

Lemma deepown_l_merge l v vm dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) vm dq ∗
  DeploymentSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  DeploymentStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
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
  iAssert (typed_pointsto_def l (v1.Deployment.mk v_typemeta cm cspec cstatus) dq)
    with "[HTypeMeta HObjectMeta HSpec HStatus]" as "Hfields".
  { simpl. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.Deployment.t)
    l (v1.Deployment.mk v_typemeta cm cspec cstatus) dq Hnot_null with "Hfields") as "Hl".
  iExists (v1.Deployment.mk v_typemeta cm cspec cstatus).
  iSplitL "Hl"; first iExact "Hl".
  iSplitR "Hobjectmeta Hspec Hstatus"; first done.
  simpl. iFrame.
Qed.

Lemma deepown_l_restore l v dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
  DeploymentSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  DeploymentStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
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
End DeploymentV.
