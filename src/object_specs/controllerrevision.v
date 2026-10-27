From New.proof Require Import prelude empty_ffi.
From New.generatedviews Require Export controllerrevision.
From New.object_specs Require Export objectmeta typemeta replicaset.
From New.object_specs Require Import top_level.

Module RawExtensionV := ControllerRevisionView.RawExtensionV.

(* Library boundary for encoding/json.Unmarshal's successful, non-null JSON
   object case in ValidateControllerRevisionCreate. RawExtension.Object is
   represented and explicitly restricted to nil, including in deepown. *)
Parameter raw_is_json_object : list w8 → bool.

Module ControllerRevisionSpecV.
Definition t := (RawExtensionV.t * w64)%type.
Definition valid (body : t) : Prop :=
  body.1.(RawExtensionV.Object') = interface.nil ∧
  (match body.1.(RawExtensionV.Raw') with Some raw => raw_is_json_object raw = true | None => False end) ∧
  0 ≤ sint.Z body.2.
Definition valid_create := valid.
Definition valid_update (old input : t) : Prop :=
  valid input ∧ input.1 = old.1.
#[global] Instance valid_update_dec old input : Decision (valid_update old input).
Proof. unfold valid_update, valid. destruct input.1.(RawExtensionV.Raw'); apply _. Defined.
Lemma valid_update_refl body : valid body → valid_update body body.
Proof. intros Hvalid. split; done. Qed.
Definition created (input stored : t) : Prop := stored = input.
Definition updated := created.

Section ownership.
Context `{hG : !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
(* Both Data and Revision are ordinary-update fields. The body pointer is the
   object root; it is not a pointer to a fictitious Go Spec field. *)
Definition deepown_l (l : loc) (body : t) dq : iProp Σ :=
  RawExtensionV.deepown_l (struct_field_ref v1.ControllerRevision.t "Data" l) body.1 dq ∗
  struct_field_ref v1.ControllerRevision.t "Revision" l ↦{dq} body.2.
End ownership.
End ControllerRevisionSpecV.

Module ControllerRevisionV.
Include ControllerRevisionView.ControllerRevisionV.
Definition kind : go_string := "ControllerRevision"%go.
Definition spec (v : t) : ControllerRevisionSpecV.t := (v.(Data'), v.(Revision')).
Definition key (v : t) : KKey.t := {| KKey.Kind' := kind;
  KKey.Namespace' := v.(ObjectMeta').(ObjectMetaV.Namespace');
  KKey.Name' := v.(ObjectMeta').(ObjectMetaV.Name') |}.
Definition valid (v : t) : Prop :=
  valid_typemeta kind v.(TypeMeta') ∧
  valid_resource_version v.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  ObjectMetaV.valid kind v.(ObjectMeta') ∧
  ControllerRevisionSpecV.valid (spec v) ∧ True.
Definition extra_valid (_ : t) : Prop := True.
Definition valid_without_meta (v : t) : Prop := ControllerRevisionSpecV.valid (spec v) ∧ True.
Definition valid_create request_kind namespace (input : t) : Prop :=
  request_kind = kind ∧
  namespace ≠ ""%go ∧
  valid_namespace namespace ∧
  valid_typemeta kind input.(TypeMeta') ∧
  ObjectMetaV.valid_create kind namespace input.(ObjectMeta') ∧
  ControllerRevisionSpecV.valid_create (spec input).
(* A sufficient update precondition, matching the generic API contracts for
   other resources: the input must also pass current create validation. This
   does not characterize every update of legacy metadata accepted upstream. *)
Definition valid_update request_kind namespace old_meta old_spec (input : t) : Prop :=
  request_kind = kind ∧
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  valid_create request_kind namespace input ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  ControllerRevisionSpecV.valid_update old_spec (spec input).
Definition created namespace (input stored : t) : Prop :=
  valid_typemeta kind stored.(TypeMeta') ∧
  ObjectMetaV.created namespace input.(ObjectMeta') stored.(ObjectMeta') ∧
  stored.(ObjectMeta').(ObjectMetaV.Generation') = input.(ObjectMeta').(ObjectMetaV.Generation') ∧
  ControllerRevisionSpecV.created (spec input) (spec stored) ∧ True.
Definition updated (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  ObjectMetaV.updated input.(ObjectMeta') stored.(ObjectMeta') ∧
  ControllerRevisionSpecV.updated (spec input) (spec stored).
Definition update_objectmeta (v : t) (m : ObjectMetaV.t) : t := v <| ObjectMeta' := m |>.

Section ownership.
Context `{hG : !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Local Set Default Proof Using "All".
Definition typemeta_ptr l : loc := struct_field_ref v1.ControllerRevision.t "TypeMeta" l.
Definition objectmeta_ptr l : loc := struct_field_ref v1.ControllerRevision.t "ObjectMeta" l.

Local Transparent deepown RawExtensionV.deepown ObjectMetaView.ObjectMetaV.deepown ObjectMetaV.deepown.
Definition deepown_l_without_meta l v dq : iProp Σ := ControllerRevisionSpecV.deepown_l l (spec v) dq.
Lemma deepown_l_split l v dq :
  deepown_l l v dq ⊢
  ⌜ l ≠ null ⌝ ∗ typemeta_ptr l ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
  ControllerRevisionSpecV.deepown_l l (spec v) dq.
Proof.
  unfold deepown_l, deepown.
  iIntros "H". iDestruct "H" as (c) "[Hl H]".
  iDestruct "H" as "(%Htm & Hmeta & Hdata & %Hnumber)".
  iDestruct (struct_fields_split (V:=v1.ControllerRevision.t) with "Hl") as "[Hfields %Hne]".
  iNamedPrefix "Hfields" "H".
  rewrite /typemeta_ptr /objectmeta_ptr /ControllerRevisionSpecV.deepown_l /spec /=.
  iSplitR; first done.
  rewrite -Htm -Hnumber. iFrame "HTypeMeta HRevision".
  iSplitL "HObjectMeta Hmeta".
  { iExists _. iFrame. }
  iExists _. iFrame.
Qed.
Lemma deepown_l_merge l v m dq :
  l ≠ null →
  typemeta_ptr l ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) m dq ∗
  ControllerRevisionSpecV.deepown_l l (spec v) dq ⊢ deepown_l l (update_objectmeta v m) dq.
Proof.
  intros Hne. destruct v as [tm meta data number].
  rewrite /typemeta_ptr /objectmeta_ptr /ControllerRevisionSpecV.deepown_l /spec /update_objectmeta /=.
  iIntros "(Htm & Hmeta & Hdata & Hnumber)".
  iDestruct "Hmeta" as (cm) "[Hm Hmeta]".
  iDestruct "Hdata" as (cd) "[Hd Hdata]".
  iAssert (typed_pointsto_def l (v1.ControllerRevision.mk tm cm cd number) dq)
    with "[Htm Hm Hd Hnumber]" as "Hfields".
  { simpl. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.ControllerRevision.t) _ _ _ Hne with "Hfields") as "Hl".
  iExists _. iFrame. rewrite /deepown /=. iFrame. done.
Qed.
Lemma deepown_l_restore l v dq :
  l ≠ null →
  typemeta_ptr l ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
  ControllerRevisionSpecV.deepown_l l (spec v) dq ⊢ deepown_l l v dq.
Proof.
  intros Hne. iIntros "H".
  iPoseProof (deepown_l_merge l v v.(ObjectMeta') dq Hne with "H") as "H".
  assert (update_objectmeta v v.(ObjectMeta') = v) as -> by (destruct v; done).
  iExact "H".
Qed.
End ownership.
End ControllerRevisionV.
