From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export objectmeta.

Module VolumeSourceV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Record t := mk {
  PersistentVolumeClaim' : option v1.PersistentVolumeClaimVolumeSource.t;
}.

Definition valid (source : t) : Prop :=
  match source.(PersistentVolumeClaim') with
  | Some pvc => valid_dns1123_subdomain pvc.(v1.PersistentVolumeClaimVolumeSource.ClaimName')
  | None => True
  end.

Definition deepown (c : v1.VolumeSource.t) (v : t) dq : iProp Σ :=
  "%Hdeepown_persistentvolumeclaim_none" ∷
    ⌜c.(v1.VolumeSource.PersistentVolumeClaim') = null ↔ v.(PersistentVolumeClaim') = None⌝ ∗
  "Hdeepown_persistentvolumeclaim_some" ∷
    (match v.(PersistentVolumeClaim') with
    | Some pvc => 
      ∃ c_pvc, c.(v1.VolumeSource.PersistentVolumeClaim') ↦{dq} c_pvc ∗ ⌜c_pvc = pvc⌝
    | None => True%I
    end).

End def.
End VolumeSourceV.

Module VolumeV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Record t := mk {
  Name' : go_string;
  VolumeSource' : VolumeSourceV.t;
}.

Definition valid (volume : t) : Prop :=
  valid_dns1123_label volume.(Name') ∧
  VolumeSourceV.valid volume.(VolumeSource').

Definition deepown (c : v1.Volume.t) (v : t) dq : iProp Σ :=
  "%Hdeepown_name" ∷ ⌜c.(v1.Volume.Name') = v.(Name')⌝ ∗
  "Hdeepown_volumesource" ∷ VolumeSourceV.deepown c.(v1.Volume.VolumeSource') v.(VolumeSource') dq.
End def.
End VolumeV.

Module PodSpecV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Record t :=
mk {
  Volumes' : list VolumeV.t;
  Hostname' : go_string;
  Subdomain' : go_string;

  (* InitContainers' : slice.t; *)
  (* Containers' : slice.t; *)
  (* EphemeralContainers' : slice.t; *)
  (* RestartPolicy' : v1.RestartPolicy.t; *)
  (* TerminationGracePeriodSeconds' : loc; *)
  (* ActiveDeadlineSeconds' : loc; *)
  (* DNSPolicy' : v1.DNSPolicy.t; *)
  (* NodeSelector' : map.t; *)
  (* ServiceAccountName' : go_string; *)
  (* DeprecatedServiceAccount' : go_string; *)
  (* AutomountServiceAccountToken' : loc; *)
  (* NodeName' : go_string; *)
  (* HostNetwork' : bool; *)
  (* HostPID' : bool; *)
  (* HostIPC' : bool; *)
  (* ShareProcessNamespace' : loc; *)
  (* SecurityContext' : loc; *)
  (* ImagePullSecrets' : slice.t; *)
  (* Affinity' : loc; *)
  (* SchedulerName' : go_string; *)
  (* Tolerations' : slice.t; *)
  (* HostAliases' : slice.t; *)
  (* PriorityClassName' : go_string; *)
  (* Priority' : loc; *)
  (* DNSConfig' : loc; *)
  (* ReadinessGates' : slice.t; *)
  (* RuntimeClassName' : loc; *)
  (* EnableServiceLinks' : loc; *)
  (* PreemptionPolicy' : loc; *)
  (* Overhead' : v1.ResourceList.t; *)
  (* TopologySpreadConstraints' : slice.t; *)
  (* SetHostnameAsFQDN' : loc; *)
  (* OS' : loc; *)
  (* HostUsers' : loc; *)
  (* SchedulingGates' : slice.t; *)
  (* ResourceClaims' : slice.t; *)
  (* Resources' : loc; *)
  (* HostnameOverride' : loc; *)
}.

Definition valid (spec : t) : Prop :=
  Forall VolumeV.valid spec.(Volumes') ∧
  (spec.(Hostname') = ""%go ∨ valid_dns1123_label spec.(Hostname')) ∧
  (spec.(Subdomain') = ""%go ∨ valid_dns1123_label spec.(Subdomain')).

Definition valid_create (spec : t) : Prop :=
  valid spec.

Definition deepown (c: v1.PodSpec.t) (v: t) dq: iProp Σ :=
  "Hdeepown_volumes" ∷
    (∃ volumes, deepown_list c.(v1.PodSpec.Volumes') volumes v.(Volumes')
      (λ volume pure_volume, VolumeV.deepown volume pure_volume dq)) ∗
  "%Hdeepown_hostname" ∷ ⌜c.(v1.PodSpec.Hostname') = v.(Hostname')⌝ ∗
  "%Hdeepown_subdomain" ∷ ⌜c.(v1.PodSpec.Subdomain') = v.(Subdomain')⌝.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End PodSpecV.

Module PodStatusV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Axiom t : Type.
Axiom valid: t → Prop.
Axiom deepown : v1.PodStatus.t → t → dfrac → iProp Σ.

(* PodStatus is opaque in this model; expose only the zero value needed when a
   controller constructs a fresh Pod. *)
Axiom zero : t.
Axiom deepown_zero : ∀ dq, ⊢ deepown (zero_val v1.PodStatus.t) zero dq.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End PodStatusV.

Module PodV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : ObjectMetaV.t;
  Spec' : PodSpecV.t;
  Status' : PodStatusV.t;
}.

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

Definition valid (pod: t) : Prop :=
  valid_typemeta kind pod.(TypeMeta') ∧
  valid_resource_version pod.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  ObjectMetaV.valid kind pod.(ObjectMeta') ∧
  PodSpecV.valid pod.(Spec') ∧
  PodStatusV.valid pod.(Status').

Definition valid_nameless_create ns (pod : t) : Prop :=
  valid_create_typemeta kind pod.(TypeMeta') ∧
  ObjectMetaV.valid_nameless_create kind ns pod.(ObjectMeta') ∧
  PodSpecV.valid_create pod.(Spec').

Definition valid_named_create ns (pod : t) : Prop :=
  valid_create_typemeta kind pod.(TypeMeta') ∧
  ObjectMetaV.valid_named_create kind ns pod.(ObjectMeta') ∧
  PodSpecV.valid_create pod.(Spec').

Definition valid_without_meta (pod: t) : Prop :=
  PodSpecV.valid pod.(Spec') ∧
  PodStatusV.valid pod.(Status').

Definition deepown (c: v1.Pod.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.Pod.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.Pod.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_podspec" ∷ PodSpecV.deepown c.(v1.Pod.Spec') v.(Spec') dq ∗
  "Hdeepown_podstatus" ∷ PodStatusV.deepown c.(v1.Pod.Status') v.(Status') dq.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

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
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {
  ObjectMeta' : ObjectMetaV.t;
  Spec' : PodSpecV.t;
}.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/core/validation/validation.go#L6795-L6810 *)
(* This is the projection of Kubernetes' ValidatePodTemplateSpec onto the
   fields represented by PodTemplateSpecV.t and PodSpecV.t.  In particular,
   Kubernetes does not validate ObjectMeta.Finalizers as part of validating a
   pod template.  Checks involving unmodeled PodSpec fields and pod-specific
   annotation/field consistency are likewise outside this projection. *)
Definition valid (template : t) : Prop :=
  valid_labels template.(ObjectMeta').(ObjectMetaV.Labels') ∧
  valid_annotations template.(ObjectMeta').(ObjectMetaV.Annotations') ∧
  PodSpecV.valid template.(Spec').

Definition deepown (c : v1.PodTemplateSpec.t) (v : t) dq : iProp Σ :=
  "Hdeepown_objectmeta" ∷
    ObjectMetaV.deepown c.(v1.PodTemplateSpec.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_spec" ∷
    PodSpecV.deepown c.(v1.PodTemplateSpec.Spec') v.(Spec') dq.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

Definition objectmeta_ptr l : loc :=
  struct_field_ref v1.PodTemplateSpec.t "ObjectMeta" l.

Definition spec_ptr l : loc :=
  struct_field_ref v1.PodTemplateSpec.t "Spec" l.

End def.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

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
