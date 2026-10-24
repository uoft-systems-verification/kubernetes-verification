From New.generatedviews Require Export pod.
(** Complete recursive Pod, PodSpec, and PodStatus views.
    Field representation and ownership cover every field; validation and API
    preparation below still contain the existing model abstractions. *)
From New.proof Require Import prelude empty_ffi util.
From New.object_specs Require Export objectmeta.
From New.object_specs Require Import top_level.

(** Conversion between versioned and internal Pods removes these obsolete
    annotations from Pods and Pod templates. This function is the exact effect
    of that conversion on the projected annotation map.
    https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/core/v1/conversion.go#L511-L545 *)
Definition legacy_init_container_annotation_keys : list go_string :=
  ["pod.beta.kubernetes.io/init-containers"%go;
   "pod.alpha.kubernetes.io/init-containers"%go;
   "pod.beta.kubernetes.io/init-container-statuses"%go;
   "pod.alpha.kubernetes.io/init-container-statuses"%go].

Definition drop_legacy_init_container_annotations
    (annotations : option (gmap go_string go_string)) : option (gmap go_string go_string) :=
  match annotations with
  | None => None
  | Some annotations => Some (foldr delete annotations legacy_init_container_annotation_keys)
  end.

Definition pod_objectmeta_after_conversion (meta : ObjectMetaV.t) : ObjectMetaV.t :=
  meta <| ObjectMetaV.Annotations' :=
    drop_legacy_init_container_annotations meta.(ObjectMetaV.Annotations') |>.

Lemma annotations_size_delete annotations key :
  annotations_size (delete key annotations) ≤ annotations_size annotations.
Proof.
  destruct (annotations !! key) as [value|] eqn:Hlookup.
  - rewrite /annotations_size.
    pose proof (map_to_list_delete annotations key value Hlookup) as Hperm.
    setoid_rewrite <-Hperm. simpl. lia.
  - rewrite delete_id; done.
Qed.

Lemma annotations_size_foldr_delete annotations keys :
  annotations_size (foldr delete annotations keys) ≤ annotations_size annotations.
Proof.
  induction keys as [|key keys IH]; first done.
  simpl. etrans; first apply annotations_size_delete. exact IH.
Qed.

Lemma valid_annotations_drop_legacy_init_container_annotations annotations :
  valid_annotations annotations →
  valid_annotations (drop_legacy_init_container_annotations annotations).
Proof.
  destruct annotations as [annotations|]; simpl; last done.
  intros [Hentries Hsize]. split.
  - repeat apply map_Forall_delete. exact Hentries.
  - etrans; first apply annotations_size_delete.
    etrans; first apply annotations_size_delete.
    etrans; first apply annotations_size_delete.
    etrans; first apply annotations_size_delete.
    exact Hsize.
Qed.

(** Semantic boundary for imported Kubernetes routines. These functions act
    on complete recursive field views, including nil/empty distinctions. Their
    bodies remain opaque, just as the upstream Go defaulting and validation
    calls do in the Goose translation. They describe the checked-out model's
    feature-gate and admission configuration, not an arbitrary cluster.

    [create_spec] and [create_status] include schema defaults, conversion,
    mutating admission, PrepareForCreate, and conversion back to v1. Only
    labels and annotations from metadata affect these fields. In particular,
    PrepareForCreate is NOT assumed idempotent (affinity selector merging can
    append requirements). [update_spec] uses the stored old spec and the
    update-specific strategy instead.

    Sources: kubernetes_model/apimodel/api_model.go;
    kubernetes/pkg/apis/core/v1/{defaults,zz_generated.defaults}.go;
    kubernetes/pkg/registry/core/pod/strategy.go;
    kubernetes/pkg/apis/core/validation/validation.go. *)
Lemma drop_legacy_init_container_annotations_idempotent annotations :
  drop_legacy_init_container_annotations (drop_legacy_init_container_annotations annotations) =
    drop_legacy_init_container_annotations annotations.
Proof.
  destruct annotations as [annotations|]; last done.
  unfold drop_legacy_init_container_annotations, legacy_init_container_annotation_keys; simpl.
  f_equal. apply map_eq. intros key. repeat rewrite lookup_delete. repeat case_decide; done.
Qed.


(* These adapter lemmas compare canonical ownership with the included views. *)
Local Transparent ObjectMetaView.ObjectMetaV.deepown ObjectMetaV.deepown.
Local Transparent PodView.VolumeSourceV.deepown PodView.PodSpecV.deepown PodView.PodStatusV.deepown.

Module PodAPI.
Definition string_map := option (gmap go_string go_string).
Parameter schema_defaults : PodView.PodSpecV.t → PodView.PodSpecV.t.
Parameter template_defaults : string_map → string_map → PodView.PodSpecV.t → PodView.PodSpecV.t.
(** Preparation never changes volume names, PVC references, Hostname, or
    Subdomain. Other volume-source fields are defaulted/prepared recursively.
    The rest of the spec does not depend on these three controller-managed
    fields; making that decomposition explicit avoids assuming identity for
    containers, probes, tolerations, affinity, or any other nested fields. *)
Definition without_managed (spec : PodView.PodSpecV.t) : PodView.PodSpecV.t :=
  spec <| PodView.PodSpecV.Volumes' := None |>
    <| PodView.PodSpecV.Hostname' := ""%go |> <| PodView.PodSpecV.Subdomain' := ""%go |>.
Parameter create_unmanaged_spec : string_map → string_map → PodView.PodSpecV.t → PodView.PodSpecV.t.
Parameter create_volume_source : PodView.VolumeSourceV.t → PodView.VolumeSourceV.t.
Definition create_volume (volume : PodView.VolumeV.t) : PodView.VolumeV.t :=
  let source := volume.(PodView.VolumeV.VolumeSource') in
  volume <| PodView.VolumeV.VolumeSource' :=
    (create_volume_source source) <| PodView.VolumeSourceV.PersistentVolumeClaim' :=
      source.(PodView.VolumeSourceV.PersistentVolumeClaim') |> |>.
Definition create_spec labels annotations (spec : PodView.PodSpecV.t) : PodView.PodSpecV.t :=
  (create_unmanaged_spec labels annotations (without_managed spec))
    <| PodView.PodSpecV.Volumes' := fmap (M:=option) (fmap (M:=list) create_volume)
      spec.(PodView.PodSpecV.Volumes') |>
    <| PodView.PodSpecV.Hostname' := spec.(PodView.PodSpecV.Hostname') |>
    <| PodView.PodSpecV.Subdomain' := spec.(PodView.PodSpecV.Subdomain') |>.

Lemma without_managed_idempotent spec :
  without_managed (without_managed spec) = without_managed spec.
Proof. destruct spec. done. Qed.
Lemma create_spec_without_managed labels annotations spec :
  without_managed (create_spec labels annotations spec) =
    without_managed (create_spec labels annotations (without_managed spec)).
Proof. unfold create_spec, without_managed. destruct spec. done. Qed.
(** Scheduling-gate conditions use metav1.Now, so status preparation is a
    relation over complete results rather than a deterministic function. *)
Parameter create_status : string_map → string_map → PodView.PodSpecV.t → PodView.PodStatusV.t → Prop.
Parameter update_spec : PodView.PodSpecV.t → PodView.PodSpecV.t → PodView.PodSpecV.t.
Parameter validate_spec : PodView.PodSpecV.t → bool.
Parameter validate_spec_update : PodView.PodSpecV.t → PodView.PodSpecV.t → bool.
Parameter validate_annotations : string_map → PodView.PodSpecV.t → bool.
Parameter validate_annotations_update : string_map → PodView.PodSpecV.t →
  string_map → PodView.PodSpecV.t → bool.
Parameter validate_template : string_map → string_map → PodView.PodSpecV.t → bool.
End PodAPI.

Module VolumeSourceV.
Include PodView.VolumeSourceV.
Local Transparent deepown.
Definition valid (source : t) : Prop :=
  match source.(PersistentVolumeClaim') with
  | Some pvc => valid_dns1123_subdomain pvc.(v1.PersistentVolumeClaimVolumeSource.ClaimName')
  | None => True
  end.
Global Instance valid_dec source : Decision (valid source).
Proof. unfold valid. destruct source.(PersistentVolumeClaim'); apply _. Defined.
Section ownership.
Context `{hG : !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Local Set Default Proof Using "All".

Definition deepown_rest (c : v1.VolumeSource.t) (v : t) dq : iProp Σ :=
  deepown (c <| v1.VolumeSource.PersistentVolumeClaim' := null |>)
    (v <| PersistentVolumeClaim' := None |>) dq.

Lemma deepown_split c v dq : deepown c v dq ⊣⊢
  "%Hdeepown_persistentvolumeclaim_none" ∷
    ⌜c.(v1.VolumeSource.PersistentVolumeClaim') = null ↔ v.(PersistentVolumeClaim') = None⌝ ∗
  "Hdeepown_persistentvolumeclaim_some" ∷ (match v.(PersistentVolumeClaim') with
    | Some pvc => ∃ c_pvc, c.(v1.VolumeSource.PersistentVolumeClaim') ↦{dq} c_pvc ∗ ⌜c_pvc = pvc⌝
    | None => True%I
    end) ∗
  "Hdeepown_rest" ∷ deepown_rest c v dq.
Proof.
  iSplit.
  - rewrite /deepown. iNamed 1.
    iDestruct "Hdeepown_persistentvolumeclaim" as "[%Hnil Hpvc]".
    iFrame "%". iSplitL "Hpvc"; first done.
    rewrite /deepown_rest /deepown /=. iFrame.
    iApply deepown_ptr_nil.
  - iIntros "(%Hnil & Hpvc & Hrest)".
    rewrite /deepown_rest /deepown /=. iNamed "Hrest". iNamed "Hdeepown_rest".
    iFrame. rewrite /deepown_ptr. iFrame "%".
Qed.
End ownership.
End VolumeSourceV.
Local Transparent VolumeSourceV.deepown.

Module VolumeV.
Include PodView.VolumeV.
Definition valid (volume : t) : Prop :=
  valid_dns1123_label volume.(Name') ∧ VolumeSourceV.valid volume.(VolumeSource').
Global Instance valid_dec volume : Decision (valid volume).
Proof. unfold valid. apply _. Defined.
End VolumeV.

Module PodSpecV.
Include PodView.PodSpecV.
Local Transparent deepown.
(* Kubernetes validation and semantic equality treat a nil volume slice and
   an allocated empty slice identically. The option-valued field above keeps
   the concrete distinction for representation-sensitive operations, while
   this projection exposes the logical list used by validation and
   controllers. *)
Definition volumes_list (spec : t) : list VolumeV.t :=
  default [] spec.(Volumes').

Definition valid_create (spec : t) : Prop :=
  Forall VolumeV.valid (volumes_list spec) ∧
  (spec.(Hostname') = ""%go ∨ valid_dns1123_label spec.(Hostname')) ∧
  (spec.(Subdomain') = ""%go ∨ valid_dns1123_label spec.(Subdomain')) ∧
  PodAPI.validate_spec (PodAPI.schema_defaults spec) = true.

Global Instance valid_create_dec spec : Decision (valid_create spec).
Proof. unfold valid_create. apply _. Defined.

(* Stored specs satisfy full spec validation and are fixed points of the
   update-specific preparation path. Create preparation is deliberately not
   required to be idempotent. *)
Definition valid (spec : t) : Prop :=
  valid_create spec ∧
  PodAPI.validate_spec spec = true ∧
  PodAPI.update_spec spec spec = spec ∧
  PodAPI.validate_spec_update spec spec = true.

(* Pod update validation treats Volumes, Hostname, and Subdomain as immutable.
   Update preparation does not change these represented fields, so this
   request-level predicate already accounts for preparation. The relation does
   not assume that [old] satisfies anything stronger than [valid_create].
   The full validator below additionally checks every represented field of
   the update-prepared spec, including the exceptions for mutable fields:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/core/validation/validation.go#L5571-L5675 *)
Definition valid_update (old input : t) : Prop :=
  valid_create input ∧
  volumes_list input = volumes_list old ∧
  input.(Hostname') = old.(Hostname') ∧
  input.(Subdomain') = old.(Subdomain') ∧
  PodAPI.validate_spec_update old (PodAPI.update_spec old input) = true.

Global Instance valid_update_dec old input :
  Decision (valid_update old input).
Proof. unfold valid_update. apply _. Defined.

Lemma valid_update_refl spec :
  valid spec → valid_update spec spec.
Proof.
  intros (Hcreate & _ & Hfixed & Hvalidate).
  unfold valid_update. rewrite Hfixed. done.
Qed.

(** Both relations retain all output fields. Metadata-dependent preparation
    is exposed exactly by [PodV.created]; these projections existentially hide
    its metadata arguments for the generic ObjectSpec interface. *)
Definition created (input stored : t) : Prop :=
  ∃ labels annotations, stored = PodAPI.create_spec labels annotations input.

Definition updated (old input stored : t) : Prop :=
  stored = PodAPI.update_spec old input.

Lemma updated_same_spec old input stored :
  valid old → input = old → updated old input stored → stored = old.
Proof. intros (_ & _ & Hfixed & _) -> Hupdated. by rewrite /updated Hfixed in Hupdated. Qed.

Section ownership.
Context `{hG : !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Local Set Default Proof Using "All".

(** Ownership of every field other than the three fields managed by StatefulSet. *)
Definition deepown_rest (c : v1.PodSpec.t) (v : t) dq : iProp Σ :=
  deepown
    (c <| v1.PodSpec.Volumes' := slice.nil |> <| v1.PodSpec.Hostname' := ""%go |>
      <| v1.PodSpec.Subdomain' := ""%go |>)
    (v <| Volumes' := None |> <| Hostname' := ""%go |> <| Subdomain' := ""%go |>) dq.

Lemma deepown_split c v dq : deepown c v dq ⊣⊢
  "%Hdeepown_volumes_none" ∷ ⌜c.(v1.PodSpec.Volumes') = slice.nil ↔ v.(Volumes') = None⌝ ∗
  "Hdeepown_volumes" ∷ (∃ volumes,
    c.(v1.PodSpec.Volumes') ↦*{dq} volumes ∗
    [∗ list] c;v ∈ volumes;volumes_list v, VolumeV.deepown c v dq) ∗
  "%Hdeepown_hostname" ∷ ⌜c.(v1.PodSpec.Hostname') = v.(Hostname')⌝ ∗
  "%Hdeepown_subdomain" ∷ ⌜c.(v1.PodSpec.Subdomain') = v.(Subdomain')⌝ ∗
  "Hdeepown_volumes_cap" ∷ own_slice_cap v1.Volume.t c.(v1.PodSpec.Volumes') dq ∗
  "Hdeepown_rest" ∷ deepown_rest c v dq.
Proof.
  iSplit.
  - rewrite /deepown. iNamed 1.
    iDestruct "Hdeepown_volumes" as "(%Hnil & %vs & Hsl & Hcap & Hvs)".
    iSplitR; first done. iSplitL "Hsl Hvs".
    { iExists vs. iFrame. }
    iSplitR; first done. iSplitR; first done. iFrame "Hcap".
    rewrite /deepown_rest /deepown /=. iFrame "∗". iFrame "%".
    iSplitL; [iApply deepown_slice_nil|done].
  - iNamed 1.
    iDestruct "Hdeepown_volumes" as (vs) "[Hsl Hvs]".
    iEval (rewrite /deepown_rest /deepown /=) in "Hdeepown_rest".
    iNamedPrefix "Hdeepown_rest" "Hrest_".
    rewrite /deepown. iFrame "∗". iFrame "%".
Qed.
End ownership.
End PodSpecV.
Local Transparent PodSpecV.deepown.

Module PodConditionV := PodView.PodConditionV.

Module PodStatusV.
Include PodView.PodStatusV.
Local Transparent deepown.
(* Status validation and API preparation remain abstract. *)
Axiom valid : t → Prop.
Axiom valid_update : t → t → Prop.
Axiom valid_update_dec : ∀ old input, Decision (valid_update old input).
Global Existing Instance valid_update_dec.
Definition created (_input stored : t) : Prop :=
  ∃ labels annotations spec, PodAPI.create_status labels annotations spec stored.
Axiom updated : t → t → Prop.

Definition conditions_list (s : t) : list PodConditionV.t := default [] s.(Conditions').
Definition ready (s : t) : bool :=
  match list_find (λ c, c.(PodConditionV.Type') = "Ready"%go) (conditions_list s) with
  | Some (_, c) => bool_decide (c.(PodConditionV.Status') = "True"%go)
  | None => false
  end.
End PodStatusV.
Local Transparent PodStatusV.deepown.

Module PodV.
Include PodView.PodV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Definition kind : go_string :=
  "Pod"%go.

Definition meta_key (meta : ObjectMetaV.t) : KKey.t :=
  {|
    KKey.Kind' := kind;
    KKey.Namespace' := meta.(ObjectMetaV.Namespace');
    KKey.Name' := meta.(ObjectMetaV.Name')
  |}.

Definition key (v: t) : KKey.t :=
  meta_key v.(ObjectMeta').

Definition prepared_spec (input : t) : PodSpecV.t :=
  PodAPI.create_spec input.(ObjectMeta').(ObjectMetaV.Labels')
    input.(ObjectMeta').(ObjectMetaV.Annotations') input.(Spec').

Definition prepared_status (input : t) (stored_status : PodStatusV.t) : Prop :=
  PodAPI.create_status input.(ObjectMeta').(ObjectMetaV.Labels')
    input.(ObjectMeta').(ObjectMetaV.Annotations') input.(Spec') stored_status.

Definition valid_body (pod : t) : Prop :=
  PodSpecV.valid pod.(Spec') ∧
  PodAPI.validate_annotations_update pod.(ObjectMeta').(ObjectMetaV.Annotations') pod.(Spec')
    pod.(ObjectMeta').(ObjectMetaV.Annotations') pod.(Spec') = true.

Definition valid (pod: t) : Prop :=
  valid_typemeta kind pod.(TypeMeta') ∧
  valid_resource_version pod.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  ObjectMetaV.valid kind pod.(ObjectMeta') ∧
  valid_body pod ∧
  PodStatusV.valid pod.(Status').

Definition extra_valid (_pod : t) : Prop := True.

Definition valid_update_input request_kind ns (pod : t) : Prop :=
  request_kind = kind ∧
  ns ≠ ""%go ∧
  valid_namespace ns ∧
  valid_create_typemeta kind pod.(TypeMeta') ∧
  ObjectMetaV.valid_create kind ns pod.(ObjectMeta') ∧
  PodSpecV.valid_create pod.(Spec').

Definition valid_create request_kind ns (pod : t) : Prop :=
  request_kind = kind ∧
  ns ≠ ""%go ∧
  valid_namespace ns ∧
  valid_create_typemeta kind pod.(TypeMeta') ∧
  ObjectMetaV.valid_create kind ns pod.(ObjectMeta') ∧
  PodSpecV.valid_create pod.(Spec') ∧
  PodAPI.validate_annotations pod.(ObjectMeta').(ObjectMetaV.Annotations')
    (PodAPI.create_spec pod.(ObjectMeta').(ObjectMetaV.Labels')
      pod.(ObjectMeta').(ObjectMetaV.Annotations') pod.(Spec')) = true ∧
  PodAPI.validate_spec (prepared_spec pod) = true.

Definition valid_update request_kind namespace old_meta old_spec (input : t) : Prop :=
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  valid_update_input request_kind namespace input ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  PodSpecV.valid_update old_spec input.(Spec') ∧
  PodAPI.validate_annotations_update old_meta.(ObjectMetaV.Annotations') old_spec
    input.(ObjectMeta').(ObjectMetaV.Annotations') (PodAPI.update_spec old_spec input.(Spec')) = true.

Definition valid_status_update request_kind namespace old_meta old_status (input : t) : Prop :=
  request_kind = kind ∧
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  PodStatusV.valid_update old_status input.(Status').

Lemma valid_update_input_of_valid request_kind ns pod :
  valid pod →
  request_kind = kind →
  ns = pod.(ObjectMeta').(ObjectMetaV.Namespace') →
  valid_update_input request_kind ns pod.
Proof.
  unfold valid, valid_update_input.
  intros (Htypemeta & _ & Hmeta & Hspec & _) Hkind Hnamespace.
  split_and!.
  - exact Hkind.
  - rewrite Hnamespace. apply Hmeta.
  - rewrite Hnamespace. apply Hmeta.
  - eapply valid_typemeta_valid_create_typemeta. exact Htypemeta.
  - unfold ObjectMetaV.valid in Hmeta.
    unfold ObjectMetaV.valid_create.
    destruct Hmeta as (Hgenerate_name & Hname_nonempty & Hname & Hnamespace_nonempty &
      Hnamespace_valid & Huid & Hlabels & Hannotations & Howner_references & Hfinalizers &
      Hmanaged_fields & Hself_link).
    case_decide; first contradiction.
    split; [split; assumption|].
    split; [right; split; [assumption|symmetry; exact Hnamespace]|].
    repeat split; assumption.
  - exact (proj1 (proj1 Hspec)).
Qed.

Definition valid_without_meta (pod: t) : Prop :=
  PodSpecV.valid pod.(Spec') ∧
  PodStatusV.valid pod.(Status').

Definition created (namespace : go_string) (input stored : t) : Prop :=
  valid_typemeta kind stored.(TypeMeta') ∧
  ObjectMetaV.created
    namespace
      (pod_objectmeta_after_conversion input.(ObjectMeta'))
      stored.(ObjectMeta') ∧
  stored.(ObjectMeta').(ObjectMetaV.Generation') = W64 1 ∧
  PodSpecV.created input.(Spec') stored.(Spec') ∧
  PodStatusV.created input.(Status') stored.(Status') ∧
  stored.(Spec') = prepared_spec input ∧
  prepared_status input stored.(Status').

Definition status_updated (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  ObjectMetaV.updated (pod_objectmeta_after_conversion input.(ObjectMeta')) stored.(ObjectMeta') ∧
  PodStatusV.updated input.(Status') stored.(Status').

Definition updated (old_spec : PodSpecV.t) (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  ObjectMetaV.updated (pod_objectmeta_after_conversion input.(ObjectMeta')) stored.(ObjectMeta') ∧
  PodSpecV.updated old_spec input.(Spec') stored.(Spec').

#[global]
Instance top_level_instance : top_level Σ t :=
  Build_top_level Σ t ObjectMetaV.t PodSpecV.t PodStatusV.t
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
  struct_field_ref v1.Pod.t "TypeMeta" l.

Definition objectmeta_ptr l: loc :=
  struct_field_ref v1.Pod.t "ObjectMeta" l.

Definition spec_ptr l: loc :=
  struct_field_ref v1.Pod.t "Spec" l.

Definition status_ptr l: loc :=
  struct_field_ref v1.Pod.t "Status" l.

Definition update_objectmeta (v: t) (m: ObjectMetaV.t) : t :=
  v <| ObjectMeta' := m |>.

Definition deepown_without_meta (c: v1.Pod.t) (v: t) dq: iProp Σ :=
  "Hdeepown_spec" ∷ PodSpecV.deepown c.(v1.Pod.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ PodStatusV.deepown c.(v1.Pod.Status') v.(Status') dq.

Definition deepown_l_without_meta l v (dq: dfrac): iProp Σ :=
  ∃ c,
    spec_ptr l ↦{dq} c.(v1.Pod.Spec') ∗
    status_ptr l ↦{dq} c.(v1.Pod.Status') ∗
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
    PodSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
    PodStatusV.deepown_l (status_ptr l) v.(Status') dq.
Proof.
  unfold deepown_l, deepown.
  iIntros "H".
  iDestruct "H" as (c) "[Hl Hdeepown]".
  iDestruct "Hdeepown" as "(%Htypemeta & Hobjectmeta & Hspec & Hstatus)".
  iDestruct (struct_fields_split (V:=v1.Pod.t) with "Hl") as "[Hfields %Hnot_null]".
  iNamedPrefix "Hfields" "H".
  iSplitR; first done.
  rewrite -Htypemeta.
  iFrame "HTypeMeta".
  iSplitL "HObjectMeta Hobjectmeta".
  { unfold ObjectMetaV.deepown_l, objectmeta_ptr. iFrame. }
  iSplitL "HSpec Hspec".
  { unfold PodSpecV.deepown_l, spec_ptr. iFrame. }
  unfold PodStatusV.deepown_l, status_ptr. iFrame.
Qed.

Lemma deepown_l_merge l v vm dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) vm dq ∗
  PodSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  PodStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
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
  iAssert (typed_pointsto_def l (v1.Pod.mk v_typemeta cm cspec cstatus) dq)
    with "[HTypeMeta HObjectMeta HSpec HStatus]" as "Hfields".
  { simpl. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.Pod.t)
    l (v1.Pod.mk v_typemeta cm cspec cstatus) dq Hnot_null with "Hfields") as "Hl".
  iExists (v1.Pod.mk v_typemeta cm cspec cstatus).
  iSplitL "Hl"; first iExact "Hl".
  iSplitR "Hobjectmeta Hspec Hstatus"; first done.
  simpl. iFrame.
Qed.

Lemma deepown_l_restore l v dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
  PodSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  PodStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
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
End PodV.

Module PodTemplateSpecV.
Include PodView.PodTemplateSpecV.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/core/validation/validation.go#L6795-L6810 *)
(* This is the projection of Kubernetes' ValidatePodTemplateSpec onto the
   complete PodSpec and represented metadata, with the apps-controller
   restrictions on RestartPolicy and ActiveDeadlineSeconds. In particular,
   Kubernetes does not validate ObjectMeta.Finalizers as part of validating a
   pod template. The imported template validator includes nested fields and Pod-specific
   annotation/field consistency. *)
Definition normalized (template : t) : t :=
  template <| ObjectMeta' := pod_objectmeta_after_conversion template.(ObjectMeta') |>
    <| Spec' := PodAPI.template_defaults template.(ObjectMeta').(ObjectMetaV.Labels')
      (drop_legacy_init_container_annotations template.(ObjectMeta').(ObjectMetaV.Annotations')) template.(Spec') |>.

Definition valid (template : t) : Prop :=
  valid_labels template.(ObjectMeta').(ObjectMetaV.Labels') ∧
  valid_annotations template.(ObjectMeta').(ObjectMetaV.Annotations') ∧
  PodSpecV.valid_create template.(Spec') ∧
  PodAPI.validate_template template.(ObjectMeta').(ObjectMetaV.Labels')
    (drop_legacy_init_container_annotations template.(ObjectMeta').(ObjectMetaV.Annotations'))
    (normalized template).(Spec') = true ∧
  (normalized template).(Spec').(PodSpecV.RestartPolicy') = "Always"%go ∧
  (normalized template).(Spec').(PodSpecV.ActiveDeadlineSeconds') = None.

Global Instance valid_dec template : Decision (valid template).
Proof. unfold valid. apply _. Defined.

Lemma valid_after_conversion template :
  valid template →
  valid (template <| ObjectMeta' := pod_objectmeta_after_conversion template.(ObjectMeta') |>).
Proof.
  intros (Hlabels & Hannotations & Hspec & Htemplate & Hrestart & Hdeadline).
  unfold valid, normalized, pod_objectmeta_after_conversion in *; simpl in *.
  rewrite !drop_legacy_init_container_annotations_idempotent.
  split_and!; try done.
  apply valid_annotations_drop_legacy_init_container_annotations. exact Hannotations.
Qed.

(** Trusted contract of imported template defaulting/validation. Template
    schema defaults and feature-field preparation preserve successful template
    admission; unlike Pod PrepareForCreate, they do not merge affinity labels.
    This is the remaining library proof obligation, not an identity assumption
    about any of the represented PodSpec fields. *)
Axiom normalized_valid : ∀ template, valid template → valid (normalized template).

(** Template preparation has no Pod affinity-label merging. Schema defaults,
    conversion, and dropping disabled fields are idempotent in the model's
    fixed feature configuration. This remains an imported-library contract. *)
Axiom normalized_idempotent : ∀ template, normalized (normalized template) = normalized template.

(** Full-field contract connecting imported template validation to the Pod
    preparation path used by GetPodFromTemplate. Metadata finalizers and name
    generation remain separate preconditions of that helper. *)
Axiom generated_spec_valid : ∀ template,
  valid template →
  let labels := Some (default ∅ template.(ObjectMeta').(ObjectMetaV.Labels')) in
  let annotations := Some (default ∅ template.(ObjectMeta').(ObjectMetaV.Annotations')) in
  PodAPI.validate_annotations annotations (PodAPI.create_spec labels annotations template.(Spec')) = true ∧
  PodAPI.validate_spec (PodAPI.create_spec labels annotations template.(Spec')) = true.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Definition objectmeta_ptr l : loc :=
  struct_field_ref v1.PodTemplateSpec.t "ObjectMeta" l.

Definition spec_ptr l : loc :=
  struct_field_ref v1.PodTemplateSpec.t "Spec" l.

Lemma deepown_l_split l v dq :
  deepown_l l v dq ⊢
    ⌜ l ≠ null ⌝ ∗
    ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
    PodSpecV.deepown_l (spec_ptr l) v.(Spec') dq.
Proof.
  iIntros "H".
  iDestruct "H" as (c) "[Hl [Hmeta Hspec]]".
  iDestruct (struct_fields_split (V:=v1.PodTemplateSpec.t) with "Hl")
    as "[Hfields %Hnot_null]".
  iDestruct "Hfields" as "[HObjectMeta HSpec]".
  iSplitR; first done.
  iSplitL "HObjectMeta Hmeta".
  { iExists c.(v1.PodTemplateSpec.ObjectMeta'). iFrame. }
  iNamed "HSpec".
  iExists c.(v1.PodTemplateSpec.Spec'). iFrame.
Qed.

Lemma deepown_l_restore l v dq :
  l ≠ null →
  ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
  PodSpecV.deepown_l (spec_ptr l) v.(Spec') dq ⊢
    deepown_l l v dq.
Proof.
  intros Hnot_null.
  iIntros "[Hmeta Hspec]".
  iDestruct "Hmeta" as (cmeta) "[HObjectMeta Hmeta]".
  iDestruct "Hspec" as (cspec) "[HSpec Hspec]".
  iAssert (typed_pointsto_def l
      (v1.PodTemplateSpec.mk cmeta cspec) dq)
    with "[HObjectMeta HSpec]" as "Hfields".
  { simpl. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.PodTemplateSpec.t)
      l (v1.PodTemplateSpec.mk cmeta cspec) dq Hnot_null with "Hfields")
    as "Hl".
  iExists (v1.PodTemplateSpec.mk cmeta cspec). iFrame.
Qed.

End proof.

End PodTemplateSpecV.

(* Keep routine proof automation from recursively expanding hundreds of Pod
   fields. Field-level proofs open these predicates explicitly, or use the
   splitting lemmas above; all fields and their ownership remain represented. *)
#[global] Opaque PodSpecV.deepown PodStatusV.deepown.
