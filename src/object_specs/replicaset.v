From New.generatedviews Require Export replicaset.
From New.proof Require Import prelude empty_ffi util.
From New.proof.k8s_io.utils Require Import ptr.
From New.object_specs Require Export labelselector pod.
From New.object_specs Require Import top_level.


(* These adapter lemmas compare canonical ownership with the included views. *)
Local Transparent ObjectMetaView.ObjectMetaV.deepown ObjectMetaV.deepown.

Module ReplicaSetSpecV.
Include ReplicaSetView.ReplicaSetSpecV.

(* Conditions required by verified controller implementations but not enforced
   by Kubernetes API admission. Keep this separate from [valid_create]. *)
Definition extra_valid (rs : t) : Prop :=
  ∀ selector, rs.(Selector') = Some selector → LabelSelectorV.extra_valid selector.

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

(* A stored ReplicaSet spec satisfies admission validation, has a non-nil
   replica count, and has a prepared template in the fixed feature configuration.
   The latter excludes legacy disabled fields that update preparation retains.
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L806-L854 *)
Definition valid (rs : t) : Prop :=
  valid_create rs ∧
  (∃ replicas, rs.(Replicas') = Some replicas ∧ 0 ≤ sint.Z replicas) ∧
  PodTemplateSpecV.normalized rs.(Template') = rs.(Template').

(* Kubernetes allows the represented replica count, minimum-ready duration,
   and Pod template to change, but keeps the selector immutable. Update
   preparation does not change the selector, so this request-level predicate
   already accounts for preparation. In particular, [old] only needs to meet
   [valid_create], not the stronger post-defaulting [valid] predicate:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L763-L770 *)
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
  valid_create spec → valid_update spec spec.
Proof. unfold valid_update. done. Qed.

Definition created (input stored : t) : Prop :=
  stored.(Replicas') = Some (default (W32 1) input.(Replicas')) ∧
  stored.(MinReadySeconds') = input.(MinReadySeconds') ∧
  stored.(Selector') = input.(Selector') ∧
  stored.(Template') =
    PodTemplateSpecV.normalized input.(Template').

Definition updated (input stored : t) : Prop :=
  created input stored.

Lemma extra_valid_created input stored :
  extra_valid input →
  created input stored →
  extra_valid stored.
Proof.
  intros Hextra (_ & _ & Hselector & _) selector Hselector_stored.
  apply Hextra.
  rewrite -Hselector. exact Hselector_stored.
Qed.

Lemma extra_valid_updated old input stored :
  extra_valid old →
  valid_update old input →
  updated input stored →
  extra_valid stored.
Proof.
  intros Hextra Hvalid_update Hupdated.
  apply (extra_valid_created input stored); [|exact Hupdated].
  intros selector Hselector.
  apply Hextra.
  rewrite -(proj2 Hvalid_update). exact Hselector.
Qed.

Lemma valid_replicas v :
  valid v → ∃ (i: w32), v.(Replicas') = Some i ∧ 0 ≤ sint.Z i.
Proof. intros (_ & Hreplicas & _). exact Hreplicas. Qed.

Lemma valid_template v :
  valid v → PodTemplateSpecV.valid v.(Template').
Proof.
  intros (Hvalid_create & _).
  destruct Hvalid_create as (_ & _ & _ & Htemplate).
  exact Htemplate.
Qed.

End ReplicaSetSpecV.

Module ReplicaSetConditionV.
Include ReplicaSetView.ReplicaSetConditionV.

(* Every field is a plain value (the transition time is only its instant, see
   [TimeV]), so the view is a function of the Go struct. *)

End ReplicaSetConditionV.

Module ReplicaSetStatusV.
Include ReplicaSetView.ReplicaSetStatusV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

(* The admission check on a status: ValidateReplicaSetStatus,
   kubernetes/pkg/apis/apps/validation/validation.go. Conditions have no
   additional validation in that function. A status-update request is checked
   on its prepared status, see [valid_update]. *)
Definition valid_request (v : t) : Prop :=
  0 ≤ sint.Z v.(Replicas') ∧
  0 ≤ sint.Z v.(FullyLabeledReplicas') ∧
  0 ≤ sint.Z v.(ReadyReplicas') ∧
  0 ≤ sint.Z v.(AvailableReplicas') ∧
  0 ≤ sint.Z v.(ObservedGeneration') ∧
  (match v.(TerminatingReplicas') with
   | Some n => 0 ≤ sint.Z n
   | None => True
   end) ∧
  sint.Z v.(FullyLabeledReplicas') ≤ sint.Z v.(Replicas') ∧
  sint.Z v.(ReadyReplicas') ≤ sint.Z v.(Replicas') ∧
  sint.Z v.(AvailableReplicas') ≤ sint.Z v.(Replicas') ∧
  sint.Z v.(AvailableReplicas') ≤ sint.Z v.(ReadyReplicas').

Global Instance valid_request_dec v : Decision (valid_request v).
Proof.
  unfold valid_request.
  destruct v.(TerminatingReplicas'); apply _.
Defined.

(* A stored status passed [valid_request]: creation stores [zero], and a status
   update stores its prepared status after validating it. Storage changes no
   represented field, so the invariant adds nothing to the admission check. *)
Definition valid (v : t) : Prop :=
  valid_request v.

(* The status strategy's PrepareForUpdate (dropDisabledStatusFields): while the
   DeploymentReplicaSetTerminatingReplicas gate is off, the submitted
   TerminatingReplicas is dropped unless the stored status already has one.
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/apps/replicaset/strategy.go#L226-L232 *)
Definition drop_disabled_status_fields (gate : bool) (old input : t) : t :=
  if gate then input
  else match old.(TerminatingReplicas') with
       | Some _ => input
       | None => input <| TerminatingReplicas' := None |>
       end.

(* The guard of a status write: Kubernetes validates the prepared status
   (ValidateReplicaSetStatusUpdate after PrepareForUpdate). The model does not
   fix the feature gate, so the guard requires acceptance for either value. *)
Definition valid_update (old input : t) : Prop :=
  ∀ gate, valid_request (drop_disabled_status_fields gate old input).

(* With the gate on the submitted status is validated unchanged, and dropping
   TerminatingReplicas only removes a check, so the old status plays no role. *)
Lemma valid_update_iff old input :
  valid_update old input ↔ valid_request input.
Proof.
  split.
  - intros Hvalid. exact (Hvalid true).
  - intros Hvalid [|]; first done.
    rewrite /drop_disabled_status_fields.
    destruct old.(TerminatingReplicas'); first done.
    rewrite /valid_request /= in Hvalid |- *. tauto.
Qed.

Global Instance valid_update_dec old input : Decision (valid_update old input).
Proof.
  destruct (decide (valid_request input)) as [Hvalid|Hinvalid];
    [left|right]; rewrite valid_update_iff; done.
Defined.

(* PrepareForCreate clears the submitted status. *)
Definition created (_input stored : t) : Prop := stored = zero.

(* A conservative status-update relation: the status strategy may clear the
   feature-gated count, but preserves every other represented status field.
   This deliberately does not claim that every permitted outcome occurs. *)
Definition updated (input stored : t) : Prop :=
  stored = input ∨ stored = input <| TerminatingReplicas' := None |>.

Lemma valid_zero : valid zero.
Proof. rewrite /valid /valid_request /zero /=. split_and!; word. Qed.

Lemma valid_updated input stored : valid_request input → updated input stored → valid stored.
Proof.
  intros Hvalid [-> | ->]; first done.
  destruct Hvalid as (? & ? & ? & ? & ? & _ & ? & ? & ? & ?).
  rewrite /valid /valid_request /=. split_and!; done.
Qed.

Lemma updated_replicas input stored : updated input stored → stored.(Replicas') = input.(Replicas').
Proof. by intros [-> | ->]. Qed.

Lemma terminating_rep (sc : v1.ReplicaSetStatus.t) (st : t) :
  deepown sc st DfracDiscarded ⊢
  opt_ptr_rep sc.(v1.ReplicaSetStatus.TerminatingReplicas')
    st.(TerminatingReplicas') DfracDiscarded.
Proof.
  rewrite /deepown /opt_ptr_rep. iIntros "H". iNamed "H".
  destruct (st.(TerminatingReplicas')) as [n|].
  - iDestruct "Hdeepown_terminatingreplicas_some" as (value_c) "[Hptr ->]". iExact "Hptr".
  - iPureIntro. by apply Hdeepown_terminatingreplicas_none.
Qed.

Lemma deepown_set_observed_generation (sc : v1.ReplicaSetStatus.t)
    (st : t) (g : w64) dq :
  deepown sc st dq ⊢
  deepown (sc <| v1.ReplicaSetStatus.ObservedGeneration' := g |>)
    (st <| ObservedGeneration' := g |>) dq.
Proof. rewrite /deepown. iIntros "H". iNamed "H". simpl. iFrame "∗ %". done. Qed.

(* The status returned by [calculateStatus]: the counts and terminating
   pointer are replaced, observed generation and conditions are kept. *)
Lemma deepown_set_counts (sc : v1.ReplicaSetStatus.t) (st : t)
    r f rd av (tptr : loc) (topt : option w32) :
  deepown sc st DfracDiscarded -∗
  opt_ptr_rep tptr topt DfracDiscarded -∗
  deepown
    (v1.ReplicaSetStatus.mk r f rd av tptr
      sc.(v1.ReplicaSetStatus.ObservedGeneration')
      sc.(v1.ReplicaSetStatus.Conditions'))
    (mk r f rd av topt
      st.(ObservedGeneration') st.(Conditions'))
    DfracDiscarded.
Proof.
  rewrite /deepown /opt_ptr_rep. iIntros "H Ht". iNamed "H". simpl.
  iFrame "# %". destruct topt as [n|]; simpl.
  - iDestruct (typed_pointsto_not_null with "Ht") as %Hnn.
    iFrame "Ht Hdeepown_conditions ". iPureIntro.
    split_and!; done.
  - iDestruct "Ht" as %->. iFrame "Hdeepown_conditions ". iPureIntro.
    split_and!; done.
Qed.

End def.
End ReplicaSetStatusV.

Module ReplicaSetV.
Include ReplicaSetView.ReplicaSetV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

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

Definition extra_valid (rs : t) : Prop :=
  ReplicaSetSpecV.extra_valid rs.(Spec').

Definition valid_create request_kind ns (rs : t) : Prop :=
  request_kind = kind ∧
  ns ≠ ""%go ∧
  valid_namespace ns ∧
  valid_create_typemeta kind rs.(TypeMeta') ∧
  ObjectMetaV.valid_create kind ns rs.(ObjectMeta') ∧
  ReplicaSetSpecV.valid_create rs.(Spec').

Definition valid_update request_kind namespace old_meta old_spec (input : t) : Prop :=
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  valid_create request_kind namespace input ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  ReplicaSetSpecV.valid_update old_spec input.(Spec').

Definition valid_status_update request_kind namespace old_meta old_status (input : t) : Prop :=
  request_kind = kind ∧
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  ReplicaSetStatusV.valid_update old_status input.(Status').

Definition valid_without_meta (rs: t) : Prop :=
  ReplicaSetSpecV.valid rs.(Spec') ∧
  ReplicaSetStatusV.valid rs.(Status').

Definition created (namespace : go_string) (input stored : t) : Prop :=
  valid_typemeta kind stored.(TypeMeta') ∧
  ObjectMetaV.created namespace input.(ObjectMeta') stored.(ObjectMeta') ∧
  stored.(ObjectMeta').(ObjectMetaV.Generation') = W64 1 ∧
  ReplicaSetSpecV.created input.(Spec') stored.(Spec') ∧
  ReplicaSetStatusV.created input.(Status') stored.(Status').

Definition updated (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  ObjectMetaV.updated input.(ObjectMeta') stored.(ObjectMeta') ∧
  ReplicaSetSpecV.updated input.(Spec') stored.(Spec').

Definition status_updated (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  ObjectMetaV.updated input.(ObjectMeta') stored.(ObjectMeta') ∧
  ReplicaSetStatusV.updated input.(Status') stored.(Status').

#[global]
Instance top_level_instance : top_level Σ t :=
  Build_top_level Σ t ObjectMetaV.t ReplicaSetSpecV.t ReplicaSetStatusV.t
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

Lemma deepown_set_status (c : v1.ReplicaSet.t) (v : t)
    (sc : v1.ReplicaSetStatus.t) (st : ReplicaSetStatusV.t) dq :
  deepown c v dq -∗ ReplicaSetStatusV.deepown sc st dq -∗
  deepown (c <| v1.ReplicaSet.Status' := sc |>)
    (v <| Status' := st |>) dq.
Proof.
  rewrite /deepown. iIntros "H Hst". iNamed "H". simpl. iFrame "∗ %".
Qed.

Lemma meta_equiv_key_uid (m1 m2 : ObjectMetaV.t) :
  ObjectMetaV.equiv_except_resource_version m1 m2 →
  meta_key m1 = meta_key m2 ∧
  m1.(ObjectMetaV.UID') = m2.(ObjectMetaV.UID') ∧
  m1.(ObjectMetaV.Namespace') = m2.(ObjectMetaV.Namespace') ∧
  m1.(ObjectMetaV.Name') = m2.(ObjectMetaV.Name').
Proof.
  rewrite /ObjectMetaV.equiv_except_resource_version /ObjectMetaV.without_resource_version.
  destruct m1, m2; simpl. intros Heq. inversion Heq; subst. done.
Qed.

End proof.
End ReplicaSetV.
