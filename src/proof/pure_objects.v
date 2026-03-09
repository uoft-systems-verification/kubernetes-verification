From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof Require Export time string.
From New.proof Require Import prelude empty_ffi.
Export apimodel.apimodel.

Module TimeV.
Section def.
Context `{hG: !heapGS Σ}.
Axiom t : Type.
Axiom deepown : v1.Time.t → t → iProp Σ.
End def.
End TimeV.

Module OwnerReferenceV.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  APIVersion' : go_string;
  Kind' : go_string;
  Name' : go_string;
  UID' : types.UID.t;
  Controller' : option bool;
  BlockOwnerDeletion' : option bool;
}.

Definition deepown (c: v1.OwnerReference.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_apiversion" ∷ ⌜ c.(v1.OwnerReference.APIVersion') = v.(APIVersion') ⌝ ∗
  "%Hdeepown_kind" ∷ ⌜ c.(v1.OwnerReference.Kind') = v.(Kind') ⌝ ∗
  "%Hdeepown_name" ∷ ⌜ c.(v1.OwnerReference.Name') = v.(Name') ⌝ ∗
  "%Hdeepown_uid" ∷ ⌜ c.(v1.OwnerReference.UID') = v.(UID') ⌝ ∗
  "%Hdeepown_controller_none" ∷ ⌜c.(v1.OwnerReference.Controller') = null ↔ v.(Controller') = None⌝ ∗
  "Hdeepown_controller_some" ∷ (match v.(Controller') with
  | Some vc => ∃ cc, c.(v1.OwnerReference.Controller') ↦{dq} cc ∗ ⌜ cc = vc ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_blockownerdeleton_none" ∷ ⌜c.(v1.OwnerReference.BlockOwnerDeletion') = null ↔ v.(BlockOwnerDeletion') = None⌝ ∗
  "Hdeepown_blockownerdeleton_some" ∷ (match v.(BlockOwnerDeletion') with
  | Some vb => ∃ cb, c.(v1.OwnerReference.BlockOwnerDeletion') ↦{dq} cb ∗ ⌜ cb = vb ⌝
  | None => True%I
  end).

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L69 *)
Axiom valid : t → Prop.

Definition list_valid (os: list t) : Prop :=
  (* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L92 *)
  ∀ i1 o1 i2 o2,
    os !! i1 = Some o1 ∧ o1.(Controller') = Some true ∧
    os !! i2 = Some o2 ∧ o2.(Controller') = Some true →
      i1 = i2.
End def.
End OwnerReferenceV.

Module ManagedFieldsEntryV.
Section def.
Context `{hG: !heapGS Σ}.

Axiom t : Type.

Axiom deepown : v1.ManagedFieldsEntry.t → t → dfrac → iProp Σ.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End ManagedFieldsEntryV.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L169 *)
Axiom valid_name: go_string → Prop.

Definition valid_generate_name generate_name : Prop :=
  (* The generate_name must be a valid name followed by a "-"; this is overly restrict but still practical *)
  ∃ prefix, generate_name = prefix ++ "-"%go ∧ prefix ≠ ""%go ∧ valid_name prefix.

  (* Below is the actual validation logic for generate_name, which is too complex and seems buggy *)
  (* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/generic.go#L37 *)
  (* TODO: there might be a bug in Kubernetes that performs name[:len(name)-2] in generic.go *)
  (* (∃ prefix char, generate_name = prefix ++ [char] ++ "-"%go ∧ valid_name (prefix ++ "a"%go)) ∨
  ¬ (∃ prefix char, generate_name = prefix ++ [char] ++ "-"%go) ∧ valid_name generate_name. *)

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L177 *)
Axiom valid_namespace: go_string → Prop.

Lemma valid_namespace_slash_free ns:
  valid_namespace ns → slash_free ns.
Proof. Admitted.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/generic.go#L82 *)
Axiom valid_generation: w64 → Prop.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/validation/validation.go#L113 *)
Axiom valid_labels: option (gmap go_string go_string) → Prop.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L44 *)
Axiom valid_annotations: option (gmap go_string go_string) → Prop.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L92 *)
Definition valid_owner_references (o: option (list OwnerReferenceV.t)) : Prop :=
  match o with
  | Some os =>
    (∀ i1 i2 or1 or2,
      os !! i1 = Some or1 →
      os !! i2 = Some or2 →
      or1.(OwnerReferenceV.Controller') = Some true →
      or2.(OwnerReferenceV.Controller') = Some true →
      i1 = i2) ∧
    (∀ or, or ∈ os → OwnerReferenceV.valid or)
  | None => True
  end.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L197 *)
Axiom valid_finalizers: option (list go_string) → Prop.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/validation/validation.go#L269 *)
Axiom valid_managed_fields : option (list ManagedFieldsEntryV.t) → Prop.

Module ObjectMetaV.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  Name' : go_string;
  GenerateName' : go_string;
  Namespace' : go_string;
  SelfLink' : go_string;
  UID' : types.UID.t;
  ResourceVersion' : go_string;
  Generation' : w64;
  CreationTimestamp' : TimeV.t;
  DeletionTimestamp' : option TimeV.t;
  DeletionGracePeriodSeconds' : option w64;
  Labels' : option (gmap go_string go_string);
  Annotations' : option (gmap go_string go_string);
  OwnerReferences' : option (list OwnerReferenceV.t);
  Finalizers' : option (list go_string);
  ManagedFields' : option (list ManagedFieldsEntryV.t);
}.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L155 *)
Definition valid (m: t) : Prop :=
  (m.(GenerateName') ≠ ""%go → valid_generate_name m.(GenerateName')) ∧
  m.(Name') ≠ ""%go ∧
  valid_name m.(Name') ∧
  m.(Namespace') ≠ ""%go ∧
  valid_namespace m.(Namespace') ∧
  valid_generation m.(Generation') ∧
  valid_labels m.(Labels') ∧
  valid_annotations m.(Annotations') ∧
  valid_owner_references m.(OwnerReferences') ∧
  valid_finalizers m.(Finalizers') ∧
  valid_managed_fields m.(ManagedFields').

Definition valid_nameless_create ns (m: t) : Prop :=
  valid_generate_name m.(GenerateName') ∧
  (* The max len of generate_name must be 58 so that the suffix can fit in:
    https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/storage/names/generate.go#L46 *)
  length m.(GenerateName') ≤ 58 ∧
  (* The name in the meta must be empty for nameless create *)
  m.(Name') = ""%go ∧
  (* The namespace in the meta is either empty or equal to the provided ns *)
  (m.(Namespace') = ""%go ∨ valid_namespace m.(Namespace') ∧ m.(Namespace') = ns) ∧
  valid_labels m.(Labels') ∧
  valid_annotations m.(Annotations') ∧
  valid_owner_references m.(OwnerReferences') ∧
  valid_finalizers m.(Finalizers') ∧
  valid_managed_fields m.(ManagedFields').

Definition nameless_created ns m m' : Prop :=
  m'.(Namespace') = ns ∧
  m'.(GenerateName') = m.(GenerateName') ∧
  m'.(Annotations') = m.(Annotations') ∧
  m'.(Labels') = m.(Labels') ∧
  m'.(OwnerReferences') = m.(OwnerReferences') ∧
  m'.(Finalizers') = m.(Finalizers').

Definition valid_for_nameless_create (m: t) : Prop :=
  (∃ prefix, m.(GenerateName') = prefix ++ "-"%go ∧ prefix ≠ ""%go ∧ valid_name prefix ∧ ¬ reserved_name prefix) ∧
  (* The max len of generate_name of the pod must be 58 so that the suffix can fit in:
    https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/storage/names/generate.go#L46 *)
  length m.(GenerateName') ≤ 58 ∧
  m.(Name') = ""%go ∧
  (m.(Namespace') = ""%go ∨ valid_namespace m.(Namespace')) ∧
  match m.(OwnerReferences') with
  | None => True
  | Some os => OwnerReferenceV.list_valid os
  end.

Axiom created: go_string → t → t → Prop. (* namespace → input meta → output meta *)

Axiom updated: t → t → t → Prop. (* old meta → input meta → output meta (new meta) *)

Axiom rv_updated: t → t → Prop. (* old meta → output meta (new meta) *)

Axiom deleting: t → t → Prop.

Axiom simple_update: t → t → Prop.

Axiom simple_update_status: t → t → Prop.

Definition deepown (c: v1.ObjectMeta.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_name" ∷ ⌜ c.(v1.ObjectMeta.Name') = v.(Name') ⌝ ∗
  "%Hdeepown_generatename" ∷ ⌜ c.(v1.ObjectMeta.GenerateName') = v.(GenerateName') ⌝ ∗
  "%Hdeepown_namespace" ∷ ⌜ c.(v1.ObjectMeta.Namespace') = v.(Namespace') ⌝ ∗
  "%Hdeepown_selflink" ∷ ⌜ c.(v1.ObjectMeta.SelfLink') = v.(SelfLink') ⌝ ∗
  "%Hdeepown_uid" ∷ ⌜ c.(v1.ObjectMeta.UID') = v.(UID') ⌝ ∗
  "%Hdeepown_resourceversion" ∷ ⌜ c.(v1.ObjectMeta.ResourceVersion') = v.(ResourceVersion') ⌝ ∗
  "%Hdeepown_generation" ∷ ⌜ c.(v1.ObjectMeta.Generation') = v.(Generation') ⌝ ∗
  "Hdeepown_creationtimestamp" ∷ TimeV.deepown c.(v1.ObjectMeta.CreationTimestamp') v.(CreationTimestamp') ∗
  "%Hdeepown_deletiontimestamp_none" ∷ ⌜c.(v1.ObjectMeta.DeletionTimestamp') = null ↔ v.(DeletionTimestamp') = None⌝ ∗
  "Hdeepown_deletiontimestamp_some" ∷ (match v.(DeletionTimestamp') with
  | Some vd => ∃ cd, c.(v1.ObjectMeta.DeletionTimestamp') ↦{dq} cd ∗ TimeV.deepown cd vd
  | None => True%I
  end) ∗
  "%Hdeepown_deletiongraceperiodseconds_none" ∷ ⌜c.(v1.ObjectMeta.DeletionGracePeriodSeconds') = null ↔ v.(DeletionGracePeriodSeconds') = None⌝ ∗
  "Hdeepown_deletiongraceperiodseconds_some" ∷ (match v.(DeletionGracePeriodSeconds') with
  | Some vd => ∃ cd, c.(v1.ObjectMeta.DeletionGracePeriodSeconds') ↦{dq} cd ∗ ⌜ cd = vd ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_labels_none" ∷ ⌜c.(v1.ObjectMeta.Labels') = null ↔ v.(Labels') = None⌝ ∗
  "Hdeepown_labels_some" ∷ (match v.(Labels') with
  | Some vl => ∃ cl, c.(v1.ObjectMeta.Labels') ↦${dq} cl ∗ ⌜ cl = vl ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_annotations_none" ∷ ⌜c.(v1.ObjectMeta.Annotations') = null ↔ v.(Annotations') = None⌝ ∗
  "Hdeepown_annotations_some" ∷ (match v.(Annotations') with
  | Some va => ∃ ca, c.(v1.ObjectMeta.Annotations') ↦${dq} ca ∗ ⌜ ca = va ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_ownerreferences_none" ∷ ⌜c.(v1.ObjectMeta.OwnerReferences') = slice.nil ↔ v.(OwnerReferences') = None⌝ ∗
  "Hdeepown_ownerreferences_some" ∷ (match v.(OwnerReferences') with
  | Some vos => ∃ cos, c.(v1.ObjectMeta.OwnerReferences') ↦*{dq} cos ∗
                        [∗list] co;vo ∈ cos;vos, OwnerReferenceV.deepown co vo dq
  | None => True%I
  end) ∗
  "%Hdeepown_finalizers_none" ∷ ⌜c.(v1.ObjectMeta.Finalizers') = slice.nil ↔ v.(Finalizers') = None⌝ ∗
  "Hdeepown_finalizers_some" ∷ (match v.(Finalizers') with
  | Some vfs => ∃ cfs, c.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_managedfields_none" ∷ ⌜c.(v1.ObjectMeta.ManagedFields') = slice.nil ↔ v.(ManagedFields') = None⌝ ∗
  "Hdeepown_managedfields_some" ∷ (match v.(ManagedFields') with
  | Some vms => ∃ cms, c.(v1.ObjectMeta.ManagedFields') ↦*{dq} cms ∗
                        [∗list] cm;vm ∈ cms;vms, ManagedFieldsEntryV.deepown cm vm dq
  | None => True%I
  end).

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End ObjectMetaV.

Module PodSpecV.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {}.
Axiom valid: t → Prop.
Axiom deepown : v1.PodSpec.t → t → iProp Σ.
End def.
End PodSpecV.

Module PodStatusV.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  Phase' : go_string;
  (* ObservedGeneration' : w64;
  Phase' : PodPhase.t;
  Conditions' : slice.t;
  Message' : go_string;
  Reason' : go_string;
  NominatedNodeName' : go_string;
  HostIP' : go_string;
  HostIPs' : slice.t;
  PodIP' : go_string;
  PodIPs' : slice.t;
  StartTime' : loc;
  InitContainerStatuses' : slice.t;
  ContainerStatuses' : slice.t;
  QOSClass' : PodQOSClass.t;
  EphemeralContainerStatuses' : slice.t;
  Resize' : PodResizeStatus.t;
  ResourceClaimStatuses' : slice.t;
  ExtendedResourceClaimStatus' : loc; *)
}.

Axiom valid: t → Prop.

Definition deepown (c: v1.PodStatus.t) (v: t): iProp Σ :=
  "%Hdeepown_phase" ∷ ⌜ c.(v1.PodStatus.Phase') = v.(Phase') ⌝ ∗
  "%true" ∷ True.

End def.
End PodStatusV.

Module PodV.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : ObjectMetaV.t;
  Spec' : PodSpecV.t;
  Status' : PodStatusV.t;
}.

Definition kind : go_string :=
  "Pod"%go.

Definition key (v: t) : KKey.t :=
  {|
    KKey.Kind' := kind;
    KKey.Namespace' := v.(ObjectMeta').(ObjectMetaV.Namespace');
    KKey.Name' := v.(ObjectMeta').(ObjectMetaV.Name')
  |}.

Definition valid (pod: t) : Prop :=
  ObjectMetaV.valid pod.(ObjectMeta') ∧
  PodSpecV.valid pod.(Spec') ∧
  PodStatusV.valid pod.(Status').

Definition valid_without_meta (pod: t) : Prop :=
  PodSpecV.valid pod.(Spec') ∧
  PodStatusV.valid pod.(Status').

Definition valid_for_nameless_create (pod: t) : Prop :=
  ObjectMetaV.valid_for_nameless_create pod.(ObjectMeta') ∧
  (* TODO: should we have valid_for_nameless_create for pod spec and pod status? *)
  PodSpecV.valid pod.(Spec') ∧
  PodStatusV.valid pod.(Status').

Definition valid_for_nameless_create_without_meta (pod: t) : Prop :=
  PodSpecV.valid pod.(Spec') ∧
  PodStatusV.valid pod.(Status').

Definition deepown (c: v1.Pod.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.Pod.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.Pod.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_podspec" ∷ PodSpecV.deepown c.(v1.Pod.Spec') v.(Spec') ∗
  "Hdeepown_podstatus" ∷ PodStatusV.deepown c.(v1.Pod.Status') v.(Status').

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

Definition deepown_without_meta (c: v1.Pod.t) (v: t): iProp Σ :=
  "Hdeepown_spec" ∷ PodSpecV.deepown c.(v1.Pod.Spec') v.(Spec') ∗
  "Hdeepown_status" ∷ PodStatusV.deepown c.(v1.Pod.Status') v.(Status').

Definition deepown_l_without_meta l v (dq: dfrac): iProp Σ :=
  ∃ c,
  l ↦s[ v1.Pod :: "Spec" ]{dq} c.(v1.Pod.Spec') ∗
  l ↦s[ v1.Pod :: "Status" ]{dq} c.(v1.Pod.Status') ∗
  deepown_without_meta c v.

End def.
End PodV.

Module PodTemplateSpecV.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  ObjectMeta' : ObjectMetaV.t;
  Spec' : PodSpecV.t;
}.

Axiom meta_valid: ObjectMetaV.t → Prop.

Definition valid (v: t) : Prop :=
  meta_valid v.(ObjectMeta') ∧
  PodSpecV.valid v.(Spec').

Definition deepown (c: v1.PodTemplateSpec.t) (v: t) dq: iProp Σ :=
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.PodTemplateSpec.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_podspec" ∷ PodSpecV.deepown c.(v1.PodTemplateSpec.Spec') v.(Spec').

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End PodTemplateSpecV.

Module ReplicaSetSpecV.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  Replicas' : option w32;
  MinReadySeconds' : w32;
  (* Selector' : loc; *)
  Template' : PodTemplateSpecV.t;
}.

Definition valid (v: t) : Prop :=
  (∃ (i: w32), v.(Replicas') = Some i ∧ 0 ≤ sint.Z i) ∧
  PodTemplateSpecV.valid v.(Template').

Definition deepown (c: v1.ReplicaSetSpec.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_replicas_none" ∷ ⌜c.(v1.ReplicaSetSpec.Replicas') = null ↔ v.(Replicas') = None⌝ ∗
  "Hdeepown_replicas_some" ∷ (match v.(Replicas') with
  | Some i => ∃ replicas, c.(v1.ReplicaSetSpec.Replicas') ↦{dq} replicas ∗ ⌜ replicas = i ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_minreadyseconds" ∷ ⌜ c.(v1.ReplicaSetSpec.MinReadySeconds') = v.(MinReadySeconds') ⌝ ∗
  "Hdeepown_template" ∷ PodTemplateSpecV.deepown c.(v1.ReplicaSetSpec.Template') v.(Template') dq.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End ReplicaSetSpecV.

Module ReplicaSetStatusV.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {}.
Axiom valid : t → Prop.
Axiom deepown : v1.ReplicaSetStatus.t → t → iProp Σ.
End def.
End ReplicaSetStatusV.

Module ReplicaSetV.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : ObjectMetaV.t;
  Spec' : ReplicaSetSpecV.t;
  Status' : ReplicaSetStatusV.t;
}.

Definition kind : go_string :=
   "ReplicaSet"%go.

Definition key (v: t) : KKey.t :=
  {|
    KKey.Kind' := kind;
    KKey.Namespace' := v.(ObjectMeta').(ObjectMetaV.Namespace');
    KKey.Name' := v.(ObjectMeta').(ObjectMetaV.Name')
  |}.

Definition valid (rs: t) : Prop :=
  ObjectMetaV.valid rs.(ObjectMeta') ∧
  ReplicaSetSpecV.valid rs.(Spec') ∧
  ReplicaSetStatusV.valid rs.(Status').

Definition valid_without_meta (rs: t) : Prop :=
  ReplicaSetSpecV.valid rs.(Spec') ∧
  ReplicaSetStatusV.valid rs.(Status').

Definition valid_for_nameless_create (rs: t) : Prop :=
  ObjectMetaV.valid_for_nameless_create rs.(ObjectMeta') ∧
  (* TODO: should we have valid_for_nameless_create for rs spec and rs status? *)
  ReplicaSetSpecV.valid rs.(Spec') ∧
  ReplicaSetStatusV.valid rs.(Status').

Definition valid_for_nameless_create_without_meta (rs: t) : Prop :=
  ReplicaSetSpecV.valid rs.(Spec') ∧
  ReplicaSetStatusV.valid rs.(Status').

Definition deepown (c: v1.ReplicaSet.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.ReplicaSet.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.ReplicaSet.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_spec" ∷ ReplicaSetSpecV.deepown c.(v1.ReplicaSet.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ ReplicaSetStatusV.deepown c.(v1.ReplicaSet.Status') v.(Status').

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

Definition deepown_without_meta (c: v1.ReplicaSet.t) (v: t) dq: iProp Σ :=
  "Hdeepown_spec" ∷ ReplicaSetSpecV.deepown c.(v1.ReplicaSet.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ ReplicaSetStatusV.deepown c.(v1.ReplicaSet.Status') v.(Status').

Definition deepown_l_without_meta l v (dq: dfrac): iProp Σ :=
  ∃ c,
  l ↦s[ v1.ReplicaSet :: "Spec" ]{dq} c.(v1.ReplicaSet.Spec') ∗
  l ↦s[ v1.ReplicaSet :: "Status" ]{dq} c.(v1.ReplicaSet.Status') ∗
  deepown_without_meta c v dq.

End def.
End ReplicaSetV.

Module KObject.
Section def.
Inductive t :=
| Pod (p : v1.Pod.t)
| ReplicaSet (rs : v1.ReplicaSet.t).

Definition typemeta o : v1.TypeMeta.t :=
  match o with
  | Pod p => p.(v1.Pod.TypeMeta')
  | ReplicaSet rs => rs.(v1.ReplicaSet.TypeMeta')
  end.

Definition objectmeta o : v1.ObjectMeta.t :=
  match o with
  | Pod p => p.(v1.Pod.ObjectMeta')
  | ReplicaSet rs => rs.(v1.ReplicaSet.ObjectMeta')
  end.

Definition update_objectmeta o m: t :=
  match o with
  | Pod pod => Pod (pod <| v1.Pod.ObjectMeta' := m |>)
  | ReplicaSet rs => ReplicaSet (rs <| v1.ReplicaSet.ObjectMeta' := m |>)
  end.

End def.
End KObject.

Module ObjectSpecV.
Section def.
Inductive t :=
| PodSpec (p : PodSpecV.t)
| ReplicaSetSpec (rs : ReplicaSetSpecV.t).
Axiom valid: t → Prop.
Axiom valid_create: t → Prop.
Axiom defaulted: t → t → Prop.
Axiom created: t → t → Prop. (* input spec → output spec *)
Axiom updated: t → t → t → Prop. (* old spec → input spec → output spec *)
End def.
End ObjectSpecV.

Module ObjectStatusV.
Section def.
Inductive t :=
| PodStatus (p : PodStatusV.t)
| ReplicaSetStatus (rs : ReplicaSetStatusV.t).
Axiom valid: t → Prop.
Axiom valid_create: t → Prop.
Axiom created: t → t → Prop. (* input status → output status *)
Axiom updated: t → t → t → Prop. (* old status → input status → output status *)
End def.
End ObjectStatusV.

Module KObjectV.
Section def.
Context `{hG: !heapGS Σ}.
Inductive t :=
| Pod (p : PodV.t)
| ReplicaSet (rs : ReplicaSetV.t).

Definition typemeta o : v1.TypeMeta.t :=
  match o with
  | Pod p => p.(PodV.TypeMeta')
  | ReplicaSet rs => rs.(ReplicaSetV.TypeMeta')
  end.

Definition objectmeta o : ObjectMetaV.t :=
  match o with
  | Pod p => p.(PodV.ObjectMeta')
  | ReplicaSet rs => rs.(ReplicaSetV.ObjectMeta')
  end.

Axiom spec: t → ObjectSpecV.t.

Axiom status: t → ObjectStatusV.t.

Definition update_objectmeta o m: t :=
  match o with
  | Pod pod => Pod (pod <| PodV.ObjectMeta' := m |>)
  | ReplicaSet rs => ReplicaSet (rs <| ReplicaSetV.ObjectMeta' := m |>)
  end.

Axiom spec_update_objectmeta :
  ∀ o m, spec (update_objectmeta o m) = spec o.

Axiom status_update_objectmeta :
  ∀ o m, status (update_objectmeta o m) = status o.

Definition kind o : go_string :=
  match o with
  | Pod _ => PodV.kind
  | ReplicaSet _ => ReplicaSetV.kind
  end.

Definition key o : KKey.t :=
  {|
    KKey.Kind' := (kind o);
    KKey.Namespace' := (objectmeta o).(ObjectMetaV.Namespace');
    KKey.Name' := (objectmeta o).(ObjectMetaV.Name')
  |}.

Axiom valid_create: go_string → go_string → t → Prop.

Axiom valid_update: go_string → go_string → t → t → Prop.

Axiom valid_update_status: go_string → go_string → t → t → Prop.

Definition valid o : Prop :=
  kind o = (typemeta o).(v1.TypeMeta.Kind') ∧
  ObjectMetaV.valid (objectmeta o) ∧
  ObjectSpecV.valid (spec o) ∧
  ObjectStatusV.valid (status o).

Definition valid_nameless_create knd ns o : Prop :=
  knd = kind o ∧
  knd = (typemeta o).(v1.TypeMeta.Kind') ∧
  ObjectMetaV.valid_nameless_create ns (objectmeta o) ∧
  ObjectSpecV.valid_create (spec o) ∧
  ObjectStatusV.valid_create (status o).

Definition same_kind (o1 o2 : t) : Prop :=
  match o1, o2 with
  | Pod _, Pod _ => True
  | ReplicaSet _, ReplicaSet _ => True
  | _, _ => False
  end.

Definition defaulted o o' : Prop :=
  typemeta o = typemeta o' ∧
  objectmeta o = objectmeta o' ∧
  ObjectSpecV.defaulted (spec o) (spec o') ∧
  status o = status o'.

Definition nameless_created ns o o' : Prop :=
  same_kind o o' ∧ (* A shortcut for proving same kind; it can be derived by conditions below *)
  typemeta o = typemeta o' ∧
  ObjectMetaV.nameless_created ns (objectmeta o) (objectmeta o') ∧
  ObjectSpecV.created (spec o) (spec o') ∧
  ObjectStatusV.created (status o) (status o').

Definition valid_old o : Prop :=
  match o with
  | Pod p => PodV.valid p
  | ReplicaSet rs => ReplicaSetV.valid rs
  end.

Definition valid_without_meta o : Prop :=
  match o with
  | Pod p => PodV.valid_without_meta p
  | ReplicaSet rs => ReplicaSetV.valid_without_meta rs
  end.

Definition valid_for_nameless_create o : Prop :=
  match o with
  | Pod p => PodV.valid_for_nameless_create p
  | ReplicaSet rs => ReplicaSetV.valid_for_nameless_create rs
  end.

Definition valid_for_nameless_create_without_meta o : Prop :=
  match o with
  | Pod p => PodV.valid_for_nameless_create_without_meta p
  | ReplicaSet rs => ReplicaSetV.valid_for_nameless_create_without_meta rs
  end.

Definition deepown_l l v dq: iProp Σ :=
  match v with
  | Pod v => PodV.deepown_l l v dq
  | ReplicaSet v => ReplicaSetV.deepown_l l v dq
  end.

Definition deepown_l_without_meta l v dq: iProp Σ :=
  match v with
  | Pod v => PodV.deepown_l_without_meta l v dq
  | ReplicaSet v => ReplicaSetV.deepown_l_without_meta l v dq
  end.

Definition valid_interface i (l: loc) v: Prop :=
  match v with
  | Pod _ => i = interface.mk (ptrT.id v1.Pod.id) #l
  | ReplicaSet _ => i = interface.mk (ptrT.id v1.ReplicaSet.id) #l
  end.

Definition deepown_i i v dq: iProp Σ :=
  ∃ l, ⌜ valid_interface i l v ⌝ ∗ deepown_l l v dq.

Definition typemeta_ptr l v: loc :=
  match v with
  | Pod _ => struct.field_ref_f v1.Pod "TypeMeta" l
  | ReplicaSet _ => struct.field_ref_f v1.ReplicaSet "TypeMeta" l
  end.

Definition objectmeta_ptr l v: loc :=
  match v with
  | Pod _ => struct.field_ref_f v1.Pod "ObjectMeta" l
  | ReplicaSet _ => struct.field_ref_f v1.ReplicaSet "ObjectMeta" l
  end.

End def.

Section proof.
Context `{hG: !heapGS Σ}.

Lemma valid_for_nameless_create_split o:
  valid_for_nameless_create o →
    ObjectMetaV.valid_for_nameless_create (objectmeta o) ∧ valid_for_nameless_create_without_meta o.
Proof.
  destruct o as [p|rs]; simpl.
  - unfold PodV.valid_for_nameless_create, PodV.valid_for_nameless_create_without_meta.
    intros (Hmeta & Hspec & Hstatus). split; [done | split; done].
  - unfold ReplicaSetV.valid_for_nameless_create, ReplicaSetV.valid_for_nameless_create_without_meta.
    intros (Hmeta & Hspec & Hstatus). split; [done | split; done].
Qed.

Lemma valid_merge o m:
  ObjectMetaV.valid m ∧ valid_without_meta o →
    valid_old (update_objectmeta o m).
Proof. destruct o; done. Qed.

(* TODO: this lemma is a temporary workaround before we implement initialization logics in the model *)
Lemma valid_implies o:
  valid_for_nameless_create_without_meta o →
    valid_without_meta o.
Proof. destruct o; done. Qed.

Lemma pod_deepown_l l pure_pod dq:
  deepown_l l (Pod pure_pod) dq ⊢
    PodV.deepown_l l pure_pod dq.
Proof. done. Qed.

Lemma replicaset_deepown_l l pure_rs dq:
  deepown_l l (ReplicaSet pure_rs) dq ⊢
    ReplicaSetV.deepown_l l pure_rs dq.
Proof. done. Qed.

Lemma deepown_l_split l v dq:
  deepown_l l v dq ⊢
    (typemeta_ptr l v) ↦{dq} (typemeta v) ∗
    ObjectMetaV.deepown_l (objectmeta_ptr l v) (objectmeta v) dq ∗
    deepown_l_without_meta l v dq.
Proof.
  destruct v as [p|rs]; simpl;
    [unfold PodV.deepown_l, PodV.deepown, PodV.deepown_l_without_meta, PodV.deepown_without_meta
    |unfold ReplicaSetV.deepown_l, ReplicaSetV.deepown, ReplicaSetV.deepown_l_without_meta, ReplicaSetV.deepown_without_meta].
  all: iIntros "H";
    iDestruct "H" as (c) "[Hl Hdeepown]";
    iDestruct "Hdeepown" as "(%Htypemeta & Hobjectmeta & Hspec & Hstatus)";
    first
      [iDestruct (struct_fields_split (V:=v1.Pod.t) with "Hl") as "Hfields"
      |iDestruct (struct_fields_split (V:=v1.ReplicaSet.t) with "Hl") as "Hfields"];
    iNamed "Hfields";
    rewrite -Htypemeta;
    iFrame "HTypeMeta";
    iSplitL "HObjectMeta Hobjectmeta";
    [unfold ObjectMetaV.deepown_l; iFrame|];
    iExists c;
    iFrame.
Qed.

(* TODO: deepown_l_merge is only used for merging updated objectmeta; generalize it later *)
Lemma deepown_l_merge l v vm dq:
  (typemeta_ptr l v) ↦{dq} (typemeta v) ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l v) vm dq ∗
  deepown_l_without_meta l v dq ⊢
    deepown_l l (update_objectmeta v vm) dq.
Proof.
  destruct v as [p|rs]; simpl;
    [destruct p as [p_typemeta p_objectmeta p_spec p_status];
     unfold PodV.deepown_l_without_meta, PodV.deepown_without_meta, PodV.deepown_l, PodV.deepown
    |destruct rs as [rs_typemeta rs_objectmeta rs_spec rs_status];
     unfold ReplicaSetV.deepown_l_without_meta, ReplicaSetV.deepown_without_meta, ReplicaSetV.deepown_l, ReplicaSetV.deepown].
  all: iIntros "(HTypeMeta & Hobjectmeta & Hwithout_meta)".
  all: iDestruct "Hobjectmeta" as (cm) "(HObjectMeta & Hobjectmeta)".
  all: iDestruct "Hwithout_meta" as (c) "(HSpec & HStatus & Hspec & Hstatus)".
  all: first
    [destruct c as [c_typemeta c_objectmeta c_spec c_status];
     iDestruct (struct_fields_combine
       (v:= v1.Pod.mk p_typemeta cm c_spec c_status)
       with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "Hl";
     iExists (v1.Pod.mk p_typemeta cm c_spec c_status)
    |destruct c as [c_typemeta c_objectmeta c_spec c_status];
     iDestruct (struct_fields_combine
       (v:= v1.ReplicaSet.mk rs_typemeta cm c_spec c_status)
       with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "Hl";
     iExists (v1.ReplicaSet.mk rs_typemeta cm c_spec c_status)].
  all: iSplitL "Hl"; first iExact "Hl".
  all: iSplitR "Hobjectmeta Hspec Hstatus"; first (iPureIntro; done).
  all: simpl.
  all: iFrame.
Qed.

Lemma deepown_l_restore l v dq:
  (typemeta_ptr l v) ↦{dq} (typemeta v) ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l v) (objectmeta v) dq ∗
  deepown_l_without_meta l v dq ⊢
    deepown_l l v dq.
Proof.
  iIntros "H".
  iPoseProof (deepown_l_merge with "H") as "H".
  assert (update_objectmeta v (objectmeta v) = v) as ->.
  { destruct v as [p|rs]; [destruct p | destruct rs]; done. }
  iFrame.
Qed.

End proof.
End KObjectV.

Global Instance key_eq_dec : EqDecision KKey.t.
Proof. solve_decision. Qed.
  
Global Instance key_countable : Countable KKey.t.
Proof.
  refine (inj_countable'
            (λ k, (KKey.Kind' k,
                   KKey.Name' k,
                   KKey.Namespace' k))
            (λ '(kind, name, namespace),
              KKey.mk kind name namespace)
            _).
  intros []; reflexivity.
Qed.

Global Instance key_uid_eq_dec : EqDecision (KKey.t * types.UID.t).
Proof. solve_decision. Qed.

Global Instance key_uid_countable : Countable (KKey.t * types.UID.t).
Proof.
  refine (inj_countable'
            (λ '(k, uid), (KKey.Kind' k,
                           KKey.Name' k,
                           KKey.Namespace' k,
                           uid))
            (λ '(kind, name, namespace, uid),
              (KKey.mk kind name namespace, uid))
            _).
  intros [[] ?]; reflexivity.
Qed.

Definition meta_parent_ref meta : option (KKey.t * types.UID.t) :=
  match meta.(ObjectMetaV.OwnerReferences') with
  | Some orefs => match list_find (λ oref, oref.(OwnerReferenceV.Controller') = Some true) orefs with
    | Some (_, oref) => Some (
                          {|
                            KKey.Kind' := oref.(OwnerReferenceV.Kind');
                            KKey.Namespace' := meta.(ObjectMetaV.Namespace');
                            KKey.Name' := oref.(OwnerReferenceV.Name');
                          |},
                          oref.(OwnerReferenceV.UID')
                        )
    | None => None
    end
  | None => None
  end.


Definition meta_parent_ref_is meta kind name uid : Prop :=
  meta_parent_ref meta = Some ({|
                                KKey.Kind' := kind;
                                KKey.Namespace' := meta.(ObjectMetaV.Namespace');
                                KKey.Name' := name;
                              |}, uid).

Definition obj_parent_ref obj : option (KKey.t * types.UID.t) :=
  meta_parent_ref (KObjectV.objectmeta obj).

Definition obj_parent_ref_is obj kind name uid : Prop :=
  meta_parent_ref_is (KObjectV.objectmeta obj) kind name uid.

Definition obj_ref k obj : KKey.t * types.UID.t :=
  (k, (KObjectV.objectmeta obj).(ObjectMetaV.UID')).

Definition is_controller_parent_of (o: OwnerReferenceV.t) kind name uid : Prop :=
  o.(OwnerReferenceV.Controller') = Some true ∧
  o.(OwnerReferenceV.Kind') = kind ∧
  o.(OwnerReferenceV.Name') = name ∧
  o.(OwnerReferenceV.UID') = uid.

Global Instance is_controller_parent_of_dec o kind name uid :
  Decision (is_controller_parent_of o kind name uid).
Proof.
  unfold is_controller_parent_of.
  repeat apply and_dec; apply _.
Qed.

Definition os_has_controller_parent_of (os: list OwnerReferenceV.t) kind name uid : Prop :=
  ∃ o, o ∈ os ∧ is_controller_parent_of o kind name uid.

Global Instance os_has_controller_parent_of_dec os kind name uid :
  Decision (os_has_controller_parent_of os kind name uid).
Proof.
  unfold os_has_controller_parent_of.
  apply list_exist_dec. intros o.
  apply and_dec; apply _.
Qed.

Definition obj_has_controller_parent_of child kind name uid: Prop :=
  match (KObjectV.objectmeta child).(ObjectMetaV.OwnerReferences') with
  | Some os => os_has_controller_parent_of os kind name uid
  | None => False
  end.

Global Instance obj_has_controller_parent_of_dec child kind name uid :
  Decision (obj_has_controller_parent_of child kind name uid).
Proof.
  unfold obj_has_controller_parent_of.
  destruct ((KObjectV.objectmeta child).(ObjectMetaV.OwnerReferences')); apply _.
Qed.

Lemma valid_object_has_valid_objectmeta obj:
  KObjectV.valid_old obj → ObjectMetaV.valid (KObjectV.objectmeta obj).
Proof. destruct obj; simpl; intros [H _]; done. Qed.

Lemma valid_object_has_valid_key key obj:
  key = KObjectV.key obj →
  KObjectV.valid_old obj →
    key.(KKey.Name') ≠ ""%go ∧
    valid_name key.(KKey.Name') ∧
    key.(KKey.Namespace') ≠ ""%go ∧
    valid_namespace key.(KKey.Namespace').
Proof.
  intros Hkey Hwf.
  apply valid_object_has_valid_objectmeta in Hwf.
  destruct obj; simpl in *; subst key; simpl;
  destruct Hwf as [_ [Hname_ne [Hname_valid [Hns_ne Hns_valid]]]];
  repeat split; intuition.
Qed.

Lemma valid_owner_references_has_at_most_one_controller_parent os:
  OwnerReferenceV.list_valid os →
    ∀ kind1 name1 uid1 kind2 name2 uid2,
      os_has_controller_parent_of os kind1 name1 uid1 →
        os_has_controller_parent_of os kind2 name2 uid2 →
          kind1 = kind2 ∧ name1 = name2 ∧ uid1 = uid2.
Proof.
  intros Hwf kind1 name1 uid1 kind2 name2 uid2 H1 H2.
  unfold os_has_controller_parent_of in H1, H2.
  destruct H1 as (o1 & Hin1 & Hctrl1).
  destruct H2 as (o2 & Hin2 & Hctrl2).
  unfold is_controller_parent_of in Hctrl1, Hctrl2.
  destruct Hctrl1 as (Hctrl1_c & Hkind1 & Hname1 & Huid1).
  destruct Hctrl2 as (Hctrl2_c & Hkind2 & Hname2 & Huid2).
  apply list_elem_of_lookup_1 in Hin1 as [i1 Hlookup1].
  apply list_elem_of_lookup_1 in Hin2 as [i2 Hlookup2].
  unfold OwnerReferenceV.list_valid in Hwf.
  assert (i1 = i2) as Heq.
  { apply (Hwf i1 o1 i2 o2).
    split; [|split; [|split]]; assumption. }
  subst i2.
  rewrite Hlookup1 in Hlookup2.
  injection Hlookup2 as ->.
  split.
  - rewrite <- Hkind1. exact Hkind2.
  - split.
    + rewrite <- Hname1. exact Hname2.
    + rewrite <- Huid1. exact Huid2.
Qed.

Lemma valid_obj_has_at_most_one_controller_parent obj:
  KObjectV.valid_old obj →
    ∀ kind1 name1 uid1 kind2 name2 uid2,
      obj_has_controller_parent_of obj kind1 name1 uid1 →
        obj_has_controller_parent_of obj kind2 name2 uid2 →
          kind1 = kind2 ∧ name1 = name2 ∧ uid1 = uid2.
Proof.
  intros Hwf kind1 name1 uid1 kind2 name2 uid2 H1 H2.
  unfold obj_has_controller_parent_of in H1, H2.
  apply valid_object_has_valid_objectmeta in Hwf.
  unfold ObjectMetaV.valid in Hwf.
  destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & Hwf_ownerref & _ & _).
  destruct (ObjectMetaV.OwnerReferences' (KObjectV.objectmeta obj)) as [os|]; simpl in H1, H2, Hwf_ownerref.
  - unfold valid_owner_references in Hwf_ownerref. simpl in Hwf_ownerref.
    assert (OwnerReferenceV.list_valid os) as Hwf_list.
    { intros i1 o1 i2 o2 (Hlookup1 & Hctrl1 & Hlookup2 & Hctrl2).
      destruct Hwf_ownerref as [Hunique _].
      eauto.
    }
    apply valid_owner_references_has_at_most_one_controller_parent with (os := os); assumption.
  - contradiction.
Qed.

(* Use this when the goal is to prove [KObjectV.valid] for an object obtained by
   [KObjectV.update_objectmeta]. The parameters are expected to be:
   - [Hvalid_meta]: validity of the replacement objectmeta.
   - [Htypemeta_eq]: the updated object has the same typemeta as the pre-update
     object.
   - [Hkind_typemeta]: the pre-update object's kind agrees with its typemeta
     kind field.
   - [Hkind_eq]: the pre-update object's [KObjectV.kind] is the expected kind of
     the concrete constructor branch.
   - [Hvalid_spec]: validity of the object's spec before the objectmeta update.
   - [Hvalid_status]: validity of the object's status before the objectmeta
     update.
   The tactic combines these to rebuild [KObjectV.valid] for the updated object,
   reusing [KObjectV.spec_update_objectmeta] and
   [KObjectV.status_update_objectmeta]. In practice this is most convenient
   after destructing the concrete object constructors so [simpl] exposes the
   required equalities. *)
Ltac solve_update_objectmeta_valid
    Hvalid_meta Htypemeta_eq Hkind_typemeta Hkind_eq Hvalid_spec Hvalid_status :=
  destruct Hvalid_meta as
    (Hgenerate_name_valid & Hname_nonempty & Hname_valid & Hns_nonempty' & Hns_valid' &
      Hgeneration_valid & Hlabels_valid & Hannotations_valid &
      Hownerrefs_valid & Hfinalizers_valid & Hmanagedfields_valid);
  split_and!;
    [ rewrite <- Htypemeta_eq in Hkind_typemeta;
      exact (eq_trans (eq_sym Hkind_eq) Hkind_typemeta)
    | split_and!; done
    | rewrite KObjectV.spec_update_objectmeta; exact Hvalid_spec
    | rewrite KObjectV.status_update_objectmeta; exact Hvalid_status
    ].
