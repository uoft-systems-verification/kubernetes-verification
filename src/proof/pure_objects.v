From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof Require Export time string.
From New.proof Require Import prelude empty_ffi.
Export apimodel.apimodel.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L169 *)
Axiom valid_name: go_string → Prop.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L177 *)
Axiom valid_namespace: go_string → Prop.

Lemma valid_namespace_slash_free ns:
  valid_namespace ns → slash_free ns.
Proof. Admitted.

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

Definition deepown_l l c v dq: iProp Σ :=
  l ↦{dq} c ∗ deepown c v dq.

Definition list_well_formed (os: list t) : Prop :=
  (* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L92 *)
  ∀ i1 o1 i2 o2,
    os !! i1 = Some o1 ∧ o1.(Controller') = Some true ∧
    os !! i2 = Some o2 ∧ o2.(Controller') = Some true →
      i1 = i2.
End def.
End OwnerReferenceV.

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
  (* ManagedFields' : slice.t; *)
}.

(* TODO: translate https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go to spec *)
Definition well_formed (m: t) : Prop :=
  (m.(GenerateName') ≠ ""%go → (∃ prefix, m.(GenerateName') = prefix ++ "-"%go ∧ valid_name prefix) ∨ valid_name m.(GenerateName')) ∧
  m.(Name') ≠ ""%go ∧
  valid_name m.(Name') ∧
  m.(Namespace') ≠ ""%go ∧
  valid_namespace m.(Namespace') ∧
  match m.(OwnerReferences') with
  | None => True
  | Some os => OwnerReferenceV.list_well_formed os
  end.

Definition well_formed_for_nameless_create (m: t) : Prop :=
  (∃ prefix, m.(GenerateName') = prefix ++ "-"%go ∧ prefix ≠ ""%go ∧ valid_name prefix ∧ ¬ reserved_name prefix) ∧
  (* The max len of generate_name of the pod must be 58 so that the suffix can fit int:
    https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/storage/names/generate.go#L46 *)
  length m.(GenerateName') ≤ 58 ∧
  m.(Name') = ""%go ∧
  (m.(Namespace') = ""%go ∨ valid_namespace m.(Namespace')) ∧
  match m.(OwnerReferences') with
  | None => True
  | Some os => OwnerReferenceV.list_well_formed os
  end.

Axiom created: go_string → t → t → Prop. (* namespace → input meta → output meta *)

Axiom nameless_created: go_string → t → t → Prop. (* namespace → input meta → output meta *)

Axiom updated: t → t → t → Prop. (* old meta → input meta → output meta (new meta) *)

Axiom deleting: t → t → Prop.

Axiom simple_update: t → t → Prop.

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
  | Some vos => ∃ cos, c.(v1.ObjectMeta.OwnerReferences') ↦*{dq} cos ∗ [∗list] co;vo ∈ cos;vos, OwnerReferenceV.deepown co vo dq
  | None => True%I
  end) ∗
  "%Hdeepown_finalizers_none" ∷ ⌜c.(v1.ObjectMeta.Finalizers') = slice.nil ↔ v.(Finalizers') = None⌝ ∗
  "Hdeepown_finalizers_some" ∷ (match v.(Finalizers') with
  | Some vfs => ∃ cfs, c.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
  | None => True%I
  end).

Definition deepown_l l c v dq: iProp Σ :=
  l ↦{dq} c ∗ deepown c v dq.

End def.
End ObjectMetaV.

Module PodSpecV.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {}.
Axiom well_formed: t → Prop.
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

Axiom well_formed: t → Prop.

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

Definition well_formed (pod: t) : Prop :=
  ObjectMetaV.well_formed pod.(ObjectMeta') ∧
  PodSpecV.well_formed pod.(Spec') ∧
  PodStatusV.well_formed pod.(Status').

Definition well_formed_without_meta (pod: t) : Prop :=
  PodSpecV.well_formed pod.(Spec') ∧
  PodStatusV.well_formed pod.(Status').

Definition well_formed_for_nameless_create (pod: t) : Prop :=
  ObjectMetaV.well_formed_for_nameless_create pod.(ObjectMeta') ∧
  (* TODO: should we have well_formed_for_nameless_create for pod spec and pod status? *)
  PodSpecV.well_formed pod.(Spec') ∧
  PodStatusV.well_formed pod.(Status').

Definition well_formed_for_nameless_create_without_meta (pod: t) : Prop :=
  PodSpecV.well_formed pod.(Spec') ∧
  PodStatusV.well_formed pod.(Status').

Definition deepown (c: v1.Pod.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.Pod.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.Pod.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_podspec" ∷ PodSpecV.deepown c.(v1.Pod.Spec') v.(Spec') ∗
  "Hdeepown_podstatus" ∷ PodStatusV.deepown c.(v1.Pod.Status') v.(Status').

Definition deepown_l l c v dq: iProp Σ :=
  l ↦{dq} c ∗ deepown c v dq.

Definition deepown_without_meta (c: v1.Pod.t) (v: t): iProp Σ :=
  "Hdeepown_spec" ∷ PodSpecV.deepown c.(v1.Pod.Spec') v.(Spec') ∗
  "Hdeepown_status" ∷ PodStatusV.deepown c.(v1.Pod.Status') v.(Status').

Definition deepown_l_without_meta l c v (dq: dfrac): iProp Σ :=
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

Axiom meta_well_formed: ObjectMetaV.t → Prop.

Definition well_formed (v: t) : Prop :=
  meta_well_formed v.(ObjectMeta') ∧
  PodSpecV.well_formed v.(Spec').

Definition deepown (c: v1.PodTemplateSpec.t) (v: t) dq: iProp Σ :=
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.PodTemplateSpec.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_podspec" ∷ PodSpecV.deepown c.(v1.PodTemplateSpec.Spec') v.(Spec').

Definition deepown_l l c v dq: iProp Σ :=
  l ↦{dq} c ∗ deepown c v dq.

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

Definition well_formed (v: t) : Prop :=
  (∃ (i: w32), v.(Replicas') = Some i ∧ 0 ≤ sint.Z i) ∧
  PodTemplateSpecV.well_formed v.(Template').

Definition deepown (c: v1.ReplicaSetSpec.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_replicas_none" ∷ ⌜c.(v1.ReplicaSetSpec.Replicas') = null ↔ v.(Replicas') = None⌝ ∗
  "Hdeepown_replicas_some" ∷ (match v.(Replicas') with
  | Some i => ∃ replicas, c.(v1.ReplicaSetSpec.Replicas') ↦{dq} replicas ∗ ⌜ replicas = i ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_minreadyseconds" ∷ ⌜ c.(v1.ReplicaSetSpec.MinReadySeconds') = v.(MinReadySeconds') ⌝ ∗
  "Hdeepown_template" ∷ PodTemplateSpecV.deepown c.(v1.ReplicaSetSpec.Template') v.(Template') dq.

Definition deepown_l l c v dq: iProp Σ :=
  l ↦{dq} c ∗ deepown c v dq.

End def.
End ReplicaSetSpecV.

Module ReplicaSetStatusV.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {}.
Axiom well_formed : t → Prop.
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

Definition well_formed (rs: t) : Prop :=
  ObjectMetaV.well_formed rs.(ObjectMeta') ∧
  ReplicaSetSpecV.well_formed rs.(Spec') ∧
  ReplicaSetStatusV.well_formed rs.(Status').

Definition well_formed_without_meta (rs: t) : Prop :=
  ReplicaSetSpecV.well_formed rs.(Spec') ∧
  ReplicaSetStatusV.well_formed rs.(Status').

Definition well_formed_for_nameless_create (rs: t) : Prop :=
  ObjectMetaV.well_formed_for_nameless_create rs.(ObjectMeta') ∧
  (* TODO: should we have well_formed_for_nameless_create for rs spec and rs status? *)
  ReplicaSetSpecV.well_formed rs.(Spec') ∧
  ReplicaSetStatusV.well_formed rs.(Status').

Definition well_formed_for_nameless_create_without_meta (rs: t) : Prop :=
  ReplicaSetSpecV.well_formed rs.(Spec') ∧
  ReplicaSetStatusV.well_formed rs.(Status').

Definition deepown (c: v1.ReplicaSet.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.ReplicaSet.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.ReplicaSet.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_spec" ∷ ReplicaSetSpecV.deepown c.(v1.ReplicaSet.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ ReplicaSetStatusV.deepown c.(v1.ReplicaSet.Status') v.(Status').

Definition deepown_l l c v dq: iProp Σ :=
  l ↦{dq} c ∗ deepown c v dq.

Definition deepown_without_meta (c: v1.ReplicaSet.t) (v: t) dq: iProp Σ :=
  "Hdeepown_spec" ∷ ReplicaSetSpecV.deepown c.(v1.ReplicaSet.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ ReplicaSetStatusV.deepown c.(v1.ReplicaSet.Status') v.(Status').

Definition deepown_l_without_meta l c v (dq: dfrac): iProp Σ :=
  l ↦s[ v1.ReplicaSet :: "Spec" ]{dq} c.(v1.ReplicaSet.Spec') ∗
  l ↦s[ v1.ReplicaSet :: "Status" ]{dq} c.(v1.ReplicaSet.Status') ∗
  deepown_without_meta c v dq.

End def.
End ReplicaSetV.

Module KKey.
Global Instance eq_dec : EqDecision KKey.t.
Proof. solve_decision. Qed.

Global Instance countable : Countable KKey.t.
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
End KKey.

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
Axiom created: t → t → Prop. (* input spec → output spec *)
Axiom updated: t → t → t → Prop. (* old spec → input spec → output spec *)
End def.
End ObjectSpecV.

Module ObjectStatusV.
Section def.
Inductive t :=
| PodStatus (p : PodStatusV.t)
| ReplicaSetStatus (rs : ReplicaSetStatusV.t).
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

(* TODO: replace well_formed *)
Axiom valid: t → Prop.

Axiom valid_create: go_string → t → Prop.

Axiom valid_nameless_create: go_string → t → Prop.

Axiom valid_update: go_string → t → t → Prop.

Definition well_formed o : Prop :=
  match o with
  | Pod p => PodV.well_formed p
  | ReplicaSet rs => ReplicaSetV.well_formed rs
  end.

Definition well_formed_without_meta o : Prop :=
  match o with
  | Pod p => PodV.well_formed_without_meta p
  | ReplicaSet rs => ReplicaSetV.well_formed_without_meta rs
  end.

Definition well_formed_for_nameless_create o : Prop :=
  match o with
  | Pod p => PodV.well_formed_for_nameless_create p
  | ReplicaSet rs => ReplicaSetV.well_formed_for_nameless_create rs
  end.

Definition well_formed_for_nameless_create_without_meta o : Prop :=
  match o with
  | Pod p => PodV.well_formed_for_nameless_create_without_meta p
  | ReplicaSet rs => ReplicaSetV.well_formed_for_nameless_create_without_meta rs
  end.

Lemma well_formed_for_nameless_create_split o:
  well_formed_for_nameless_create o →
    ObjectMetaV.well_formed_for_nameless_create (objectmeta o) ∧ well_formed_for_nameless_create_without_meta o.
Proof.
  destruct o as [p|rs]; simpl.
  - unfold PodV.well_formed_for_nameless_create, PodV.well_formed_for_nameless_create_without_meta.
    intros (Hmeta & Hspec & Hstatus). split; [done | split; done].
  - unfold ReplicaSetV.well_formed_for_nameless_create, ReplicaSetV.well_formed_for_nameless_create_without_meta.
    intros (Hmeta & Hspec & Hstatus). split; [done | split; done].
Qed.

Lemma well_formed_merge o m:
  ObjectMetaV.well_formed m ∧ well_formed_without_meta o →
    well_formed (update_objectmeta o m).
Proof. destruct o; done. Qed.

(* TODO: this lemma is a temporary workaround before we implement initialization logics in the model *)
Lemma well_formed_implies o: 
  well_formed_for_nameless_create_without_meta o →
    well_formed_without_meta o.
Proof. destruct o; done. Qed.

Definition same_constructor (o1 o2 : t) : Prop :=
  match o1, o2 with
  | Pod _, Pod _ => True
  | ReplicaSet _, ReplicaSet _ => True
  | _, _ => False
  end.

Definition deepown_l l c v dq: iProp Σ :=
  match (c, v) with
  | (KObject.Pod c, Pod v) => PodV.deepown_l l c v dq
  | (KObject.ReplicaSet c, ReplicaSet v) => ReplicaSetV.deepown_l l c v dq
  | (_, _) => False
  end.

Definition interface_agree i (l: loc) v: Prop :=
  match v with
  | Pod _ => i = interface.mk (ptrT.id v1.Pod.id) #l
  | ReplicaSet _ => i = interface.mk (ptrT.id v1.ReplicaSet.id) #l
  end.

Definition deepown_i i v dq: iProp Σ :=
  ∃ l c, ⌜ interface_agree i l v ⌝ ∗ deepown_l l c v dq.

Lemma pod_deepown_l l obj pure_pod dq:
  deepown_l l obj (Pod pure_pod) dq ⊢
    ∃ pod, ⌜ obj = KObject.Pod pod ⌝ ∗ PodV.deepown_l l pod pure_pod dq.
Proof.
  destruct obj; simpl.
  - iIntros "H". iExists _. iFrame. done.
  - iIntros "Hfalse". done.
Qed.

Lemma replicaset_deepown_l l obj pure_rs dq:
  deepown_l l obj (ReplicaSet pure_rs) dq ⊢
    ∃ rs, ⌜ obj = KObject.ReplicaSet rs ⌝ ∗ ReplicaSetV.deepown_l l rs pure_rs dq.
Proof.
  destruct obj; simpl.
  - iIntros "Hfalse". done.
  - iIntros "H". iExists _. iFrame. done.
Qed.

Definition deepown_l_without_meta l c v dq: iProp Σ :=
  match (c, v) with
  | (KObject.Pod c, Pod v) => PodV.deepown_l_without_meta l c v dq
  | (KObject.ReplicaSet c, ReplicaSet v) => ReplicaSetV.deepown_l_without_meta l c v dq
  | (_, _) => False
  end.

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

Lemma deepown_l_type_match l c v dq:
  deepown_l l c v dq ⊢
  ⌜ match v with
    | Pod _ => ∃ pod, c = KObject.Pod pod
    | ReplicaSet _ => ∃ rs, c = KObject.ReplicaSet rs
    end ⌝.
Proof. destruct c, v; iIntros "H"; eauto. Qed.

Lemma deepown_l_without_meta_type_match l c v dq:
  deepown_l_without_meta l c v dq ⊢
  ⌜ match v with
    | Pod _ => ∃ pod, c = KObject.Pod pod
    | ReplicaSet _ => ∃ rs, c = KObject.ReplicaSet rs
    end ⌝.
Proof. destruct c, v; iIntros "H"; eauto. Qed.

Lemma deepown_l_split l c v dq:
  deepown_l l c v dq ⊢
    (typemeta_ptr l v) ↦{dq} (KObject.typemeta c) ∗ ⌜ (KObject.typemeta c) = (typemeta v) ⌝ ∗
    ObjectMetaV.deepown_l (objectmeta_ptr l v) (KObject.objectmeta c) (objectmeta v) dq ∗
    deepown_l_without_meta l c v dq.
Proof.
  iIntros "H".
  iDestruct (deepown_l_type_match with "H") as %Hagree.
  destruct c as [p|rs].
  - destruct v as [p0|rs0]; simpl in Hagree; try done.
    simpl.
    unfold PodV.deepown_l, PodV.deepown.
    iDestruct "H" as "[Hl Hdeepown]".
    iDestruct "Hdeepown" as "(%Htypemeta & Hobjectmeta & Hspec & Hstatus)".
    iDestruct (struct_fields_split with "Hl") as "Hfields".
    iNamed "Hfields".
    iFrame "HTypeMeta".
    iSplitR; first (iPureIntro; done).
    iSplitL "HObjectMeta Hobjectmeta".
    { unfold ObjectMetaV.deepown_l. iFrame. }
    unfold PodV.deepown_l_without_meta, PodV.deepown_without_meta.
    iFrame.
  - destruct v as [p0|rs0]; simpl in Hagree; try done.
    simpl.
    unfold ReplicaSetV.deepown_l, ReplicaSetV.deepown.
    iDestruct "H" as "[Hl Hdeepown]".
    iDestruct "Hdeepown" as "(%Htypemeta & Hobjectmeta & Hspec & Hstatus)".
    iDestruct (struct_fields_split with "Hl") as "Hfields".
    iNamed "Hfields".
    iFrame "HTypeMeta".
    iSplitR; first (iPureIntro; done).
    iSplitL "HObjectMeta Hobjectmeta".
    { unfold ObjectMetaV.deepown_l. iFrame. }
    unfold ReplicaSetV.deepown_l_without_meta, ReplicaSetV.deepown_without_meta.
    iFrame.
Qed.

(* TODO: deepown_l_merge is only used for merging updated objectmeta; generalize it later *)
Lemma deepown_l_merge l c v cm vm dq:
  (typemeta_ptr l v) ↦{dq} (KObject.typemeta c) ∗ ⌜ (KObject.typemeta c) = (typemeta v) ⌝ ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l v) cm vm dq ∗
  deepown_l_without_meta l c v dq ⊢
    deepown_l l (KObject.update_objectmeta c cm) (update_objectmeta v vm) dq.
Proof.
  iIntros "(HTypeMeta & %Htypemeta & Hobjectmeta & Hwithout_meta)".
  iDestruct (deepown_l_without_meta_type_match with "Hwithout_meta") as %Hagree.
  destruct c as [p|rs].
  - destruct v as [p0|rs0]; try done.
    iDestruct "Hobjectmeta" as "[HObjectMeta Hdeepown_objectmeta]".
    iDestruct "Hwithout_meta" as "(HSpec & HStatus & Hspec & Hstatus)".
    set (updated_pod := p <| v1.Pod.ObjectMeta' := cm |>).
    iDestruct (struct_fields_combine (v:=updated_pod) with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "Hl".
    iFrame. iPureIntro. done.
  - destruct v as [p0|rs0]; try done.
    iDestruct "Hobjectmeta" as "[HObjectMeta Hdeepown_objectmeta]".
    iDestruct "Hwithout_meta" as "(HSpec & HStatus & Hspec & Hstatus)".
    set (updated_rs := rs <| v1.ReplicaSet.ObjectMeta' := cm |>).
    iDestruct (struct_fields_combine (v:=updated_rs) with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "Hl".
    iFrame. iPureIntro. done.
Qed.

Lemma deepown_l_restore l c v dq:
  (typemeta_ptr l v) ↦{dq} (KObject.typemeta c) ∗ ⌜ (KObject.typemeta c) = (typemeta v) ⌝ ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l v) (KObject.objectmeta c) (objectmeta v) dq ∗
  deepown_l_without_meta l c v dq ⊢
    deepown_l l c v dq.
Proof.
  iIntros "H".
  iPoseProof (deepown_l_merge with "H") as "H".
  assert (KObject.update_objectmeta c (KObject.objectmeta c) = c) as ->.
  { destruct c as [p|rs]; [destruct p | destruct rs]; done. }
  assert (update_objectmeta v (objectmeta v) = v) as ->.
  { destruct v as [p|rs]; [destruct p | destruct rs]; done. }
  iFrame.
Qed.

End def.
End KObjectV.

Global Existing Instance KKey.eq_dec.
Global Existing Instance KKey.countable.

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

Lemma well_formed_object_has_well_formed_objectmeta obj:
  KObjectV.well_formed obj → ObjectMetaV.well_formed (KObjectV.objectmeta obj).
Proof. destruct obj; simpl; intros [H _]; done. Qed.

Lemma well_formed_object_has_well_formed_key key obj:
  key = KObjectV.key obj →
  KObjectV.well_formed obj →
    key.(KKey.Name') ≠ ""%go ∧
    valid_name key.(KKey.Name') ∧
    key.(KKey.Namespace') ≠ ""%go ∧
    valid_namespace key.(KKey.Namespace').
Proof.
  intros Hkey Hwf.
  apply well_formed_object_has_well_formed_objectmeta in Hwf.
  destruct obj; simpl in *; subst key; simpl;
  destruct Hwf as [_ [Hname_ne [Hname_valid [Hns_ne Hns_valid]]]];
  repeat split; intuition.
Qed.

Lemma well_formed_owner_references_has_at_most_one_controller_parent os:
  OwnerReferenceV.list_well_formed os →
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
  unfold OwnerReferenceV.list_well_formed in Hwf.
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

Lemma well_formed_obj_has_at_most_one_controller_parent obj:
  KObjectV.well_formed obj →
    ∀ kind1 name1 uid1 kind2 name2 uid2,
      obj_has_controller_parent_of obj kind1 name1 uid1 →
        obj_has_controller_parent_of obj kind2 name2 uid2 →
          kind1 = kind2 ∧ name1 = name2 ∧ uid1 = uid2.
Proof.
  intros Hwf kind1 name1 uid1 kind2 name2 uid2 H1 H2.
  unfold obj_has_controller_parent_of in H1, H2.
  destruct obj as [pod | rs].
  - (* Pod case *)
    unfold KObjectV.well_formed in Hwf.
    unfold PodV.well_formed in Hwf.
    destruct Hwf as (Hwf_meta & _).
    unfold ObjectMetaV.well_formed in Hwf_meta.
    destruct Hwf_meta as (_ & _ & _ & _ & _ & Hwf_ownerref).
    simpl in H1, H2.
    destruct (ObjectMetaV.OwnerReferences' (PodV.ObjectMeta' pod)) as [os|]; [|contradiction].
    apply well_formed_owner_references_has_at_most_one_controller_parent with (os := os); assumption.
  - (* ReplicaSet case *)
    unfold KObjectV.well_formed in Hwf.
    unfold ReplicaSetV.well_formed in Hwf.
    destruct Hwf as (Hwf_meta & _).
    unfold ObjectMetaV.well_formed in Hwf_meta.
    destruct Hwf_meta as (_ & _ & _ & _ & _ & Hwf_ownerref).
    simpl in H1, H2.
    destruct (ObjectMetaV.OwnerReferences' (ReplicaSetV.ObjectMeta' rs)) as [os|]; [|contradiction].
    apply well_formed_owner_references_has_at_most_one_controller_parent with (os := os); assumption.
Qed.
