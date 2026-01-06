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

Module PureTime.
Section def.
Context `{hG: !heapGS Σ}.
Axiom t : Type.
Axiom deepown : v1.Time.t → t → iProp Σ.
End def.
End PureTime.

Module PureOwnerReference.
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
End PureOwnerReference.

Module PureObjectMeta.
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
  CreationTimestamp' : PureTime.t;
  DeletionTimestamp' : option PureTime.t;
  DeletionGracePeriodSeconds' : option w64;
  Labels' : option (gmap go_string go_string);
  Annotations' : option (gmap go_string go_string);
  OwnerReferences' : option (list PureOwnerReference.t);
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
  | Some os => PureOwnerReference.list_well_formed os
  end.

Definition well_formed_for_create_without_name (m: t) : Prop :=
  (∃ prefix, m.(GenerateName') = prefix ++ "-"%go ∧ prefix ≠ ""%go ∧ valid_name prefix ∧ ¬ reserved_name prefix) ∧
  (* The max len of generate_name of the pod must be 58 so that the suffix can fit int:
    https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/storage/names/generate.go#L46 *)
  length m.(GenerateName') ≤ 58 ∧
  m.(Name') = ""%go ∧
  (m.(Namespace') = ""%go ∨ valid_namespace m.(Namespace')) ∧
  match m.(OwnerReferences') with
  | None => True
  | Some os => PureOwnerReference.list_well_formed os
  end.

Definition deepown (c: v1.ObjectMeta.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_name" ∷ ⌜ c.(v1.ObjectMeta.Name') = v.(Name') ⌝ ∗
  "%Hdeepown_generatename" ∷ ⌜ c.(v1.ObjectMeta.GenerateName') = v.(GenerateName') ⌝ ∗
  "%Hdeepown_namespace" ∷ ⌜ c.(v1.ObjectMeta.Namespace') = v.(Namespace') ⌝ ∗
  "%Hdeepown_selflink" ∷ ⌜ c.(v1.ObjectMeta.SelfLink') = v.(SelfLink') ⌝ ∗
  "%Hdeepown_uid" ∷ ⌜ c.(v1.ObjectMeta.UID') = v.(UID') ⌝ ∗
  "%Hdeepown_resourceversion" ∷ ⌜ c.(v1.ObjectMeta.ResourceVersion') = v.(ResourceVersion') ⌝ ∗
  "%Hdeepown_generation" ∷ ⌜ c.(v1.ObjectMeta.Generation') = v.(Generation') ⌝ ∗
  "Hdeepown_creationtimestamp" ∷ PureTime.deepown c.(v1.ObjectMeta.CreationTimestamp') v.(CreationTimestamp') ∗
  "%Hdeepown_deletiontimestamp_none" ∷ ⌜c.(v1.ObjectMeta.DeletionTimestamp') = null ↔ v.(DeletionTimestamp') = None⌝ ∗
  "Hdeepown_deletiontimestamp_some" ∷ (match v.(DeletionTimestamp') with
  | Some vd => ∃ cd, c.(v1.ObjectMeta.DeletionTimestamp') ↦{dq} cd ∗ PureTime.deepown cd vd
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
  | Some vos => ∃ cos, c.(v1.ObjectMeta.OwnerReferences') ↦*{dq} cos ∗ [∗list] co;vo ∈ cos;vos, PureOwnerReference.deepown co vo dq
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
End PureObjectMeta.

Module PurePodSpec.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {}.
Axiom well_formed: t → Prop.
Axiom deepown : v1.PodSpec.t → t → iProp Σ.
End def.
End PurePodSpec.

Module PurePodStatus.
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
End PurePodStatus.

Module PurePod.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : PureObjectMeta.t;
  Spec' : PurePodSpec.t;
  Status' : PurePodStatus.t;
}.

Definition kind : go_string :=
  "Pod"%go.

Definition key (v: t) : KKey.t :=
  {|
    KKey.Kind' := kind;
    KKey.Namespace' := v.(ObjectMeta').(PureObjectMeta.Namespace');
    KKey.Name' := v.(ObjectMeta').(PureObjectMeta.Name')
  |}.

Definition well_formed (pod: t) : Prop :=
  PureObjectMeta.well_formed pod.(ObjectMeta') ∧
  PurePodSpec.well_formed pod.(Spec') ∧
  PurePodStatus.well_formed pod.(Status').

Definition well_formed_for_create_without_name (pod: t) : Prop :=
  PureObjectMeta.well_formed_for_create_without_name pod.(ObjectMeta') ∧
  (* TODO: should we have well_formed_for_create_without_name for pod spec and pod status? *)
  PurePodSpec.well_formed pod.(Spec') ∧
  PurePodStatus.well_formed pod.(Status').

Definition deepown (c: v1.Pod.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.Pod.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ PureObjectMeta.deepown c.(v1.Pod.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_podspec" ∷ PurePodSpec.deepown c.(v1.Pod.Spec') v.(Spec') ∗
  "Hdeepown_podstatus" ∷ PurePodStatus.deepown c.(v1.Pod.Status') v.(Status').

Definition deepown_l l c v dq: iProp Σ :=
  l ↦{dq} c ∗ deepown c v dq.

End def.
End PurePod.

Module PurePodTemplateSpec.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  ObjectMeta' : PureObjectMeta.t;
  Spec' : PurePodSpec.t;
}.

Axiom meta_well_formed: PureObjectMeta.t → Prop.

Definition well_formed (v: t) : Prop :=
  meta_well_formed v.(ObjectMeta') ∧
  PurePodSpec.well_formed v.(Spec').

Definition deepown (c: v1.PodTemplateSpec.t) (v: t) dq: iProp Σ :=
  "Hdeepown_objectmeta" ∷ PureObjectMeta.deepown c.(v1.PodTemplateSpec.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_podspec" ∷ PurePodSpec.deepown c.(v1.PodTemplateSpec.Spec') v.(Spec').

Definition deepown_l l c v dq: iProp Σ :=
  l ↦{dq} c ∗ deepown c v dq.

End def.
End PurePodTemplateSpec.

Module PureReplicaSetSpec.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  Replicas' : option w32;
  MinReadySeconds' : w32;
  (* Selector' : loc; *)
  Template' : PurePodTemplateSpec.t;
}.

Definition well_formed (v: t) : Prop :=
  (∃ (i: w32), v.(Replicas') = Some i ∧ 0 ≤ sint.Z i) ∧
  PurePodTemplateSpec.well_formed v.(Template').

Definition deepown (c: v1.ReplicaSetSpec.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_replicas_none" ∷ ⌜c.(v1.ReplicaSetSpec.Replicas') = null ↔ v.(Replicas') = None⌝ ∗
  "Hdeepown_replicas_some" ∷ (match v.(Replicas') with
  | Some i => ∃ replicas, c.(v1.ReplicaSetSpec.Replicas') ↦{dq} replicas ∗ ⌜ replicas = i ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_minreadyseconds" ∷ ⌜ c.(v1.ReplicaSetSpec.MinReadySeconds') = v.(MinReadySeconds') ⌝ ∗
  "Hdeepown_template" ∷ PurePodTemplateSpec.deepown c.(v1.ReplicaSetSpec.Template') v.(Template') dq.

Definition deepown_l l c v dq: iProp Σ :=
  l ↦{dq} c ∗ deepown c v dq.

End def.
End PureReplicaSetSpec.

Module PureReplicaSetStatus.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {}.
Axiom well_formed : t → Prop.
Axiom deepown : v1.ReplicaSetStatus.t → t → iProp Σ.
End def.
End PureReplicaSetStatus.

Module PureReplicaSet.
Section def.
Context `{hG: !heapGS Σ}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : PureObjectMeta.t;
  Spec' : PureReplicaSetSpec.t;
  Status' : PureReplicaSetStatus.t;
}.

Definition kind : go_string :=
   "ReplicaSet"%go.

Definition key (v: t) : KKey.t :=
  {|
    KKey.Kind' := kind;
    KKey.Namespace' := v.(ObjectMeta').(PureObjectMeta.Namespace');
    KKey.Name' := v.(ObjectMeta').(PureObjectMeta.Name')
  |}.

Definition well_formed (rs: t) : Prop :=
  PureObjectMeta.well_formed rs.(ObjectMeta') ∧
  PureReplicaSetSpec.well_formed rs.(Spec') ∧
  PureReplicaSetStatus.well_formed rs.(Status').

Definition deepown (c: v1.ReplicaSet.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.ReplicaSet.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ PureObjectMeta.deepown c.(v1.ReplicaSet.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_spec" ∷ PureReplicaSetSpec.deepown c.(v1.ReplicaSet.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ PureReplicaSetStatus.deepown c.(v1.ReplicaSet.Status') v.(Status').

Definition deepown_l l c v dq: iProp Σ :=
  l ↦{dq} c ∗ deepown c v dq.

End def.
End PureReplicaSet.

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

Module PureKObject.
Inductive t :=
| Pod (p : PurePod.t)
| ReplicaSet (rs : PureReplicaSet.t).

Definition well_formed kobj : Prop :=
  match kobj with
  | Pod p => PurePod.well_formed p
  | ReplicaSet rs => PureReplicaSet.well_formed rs
  end.

Definition metadata kobj : PureObjectMeta.t :=
  match kobj with
  | Pod p => p.(PurePod.ObjectMeta')
  | ReplicaSet rs => rs.(PureReplicaSet.ObjectMeta')
  end.

Definition kind kobj : go_string :=
  match kobj with
  | Pod _ => PurePod.kind
  | ReplicaSet _ => PureReplicaSet.kind
  end.

Definition key kobj : KKey.t :=
  match kobj with
  | Pod p => PurePod.key p
  | ReplicaSet rs => PureReplicaSet.key rs
  end.

(* Definition agree_with_key key kobj : Prop :=
  key.(KKey.Kind') = kind kobj ∧
  key.(KKey.Namespace') = (metadata kobj).(PureObjectMeta.Namespace') ∧
  key.(KKey.Name') = (metadata kobj).(PureObjectMeta.Name'). *)

End PureKObject.

Global Existing Instance KKey.eq_dec.
Global Existing Instance KKey.countable.

Definition os_has_controller_parent_of (os: list PureOwnerReference.t) kind name uid : Prop :=
  ∃ i o, os !! i = Some o ∧
    o.(PureOwnerReference.Controller') = Some true ∧
    o.(PureOwnerReference.Kind') = kind ∧
    o.(PureOwnerReference.Name') = name ∧
    o.(PureOwnerReference.UID') = uid.

Definition obj_has_controller_parent_of child kind name uid: Prop :=
  ∃ os, (PureKObject.metadata child).(PureObjectMeta.OwnerReferences') = Some os ∧
    os_has_controller_parent_of os kind name uid.

Lemma well_formed_owner_references_has_at_most_one_controller_parent os:
  PureOwnerReference.list_well_formed os →
    ∀ kind1 name1 uid1 kind2 name2 uid2,
      os_has_controller_parent_of os kind1 name1 uid1 →
        os_has_controller_parent_of os kind2 name2 uid2 →
          kind1 = kind2 ∧ name1 = name2 ∧ uid1 = uid2.
Proof.
  intros Hwf kind1 name1 uid1 kind2 name2 uid2 H1 H2.
  unfold os_has_controller_parent_of in H1, H2.
  destruct H1 as (i1 & o1 & Hlookup1 & Hctrl1 & Hkind1 & Hname1 & Huid1).
  destruct H2 as (i2 & o2 & Hlookup2 & Hctrl2 & Hkind2 & Hname2 & Huid2).
  unfold PureOwnerReference.list_well_formed in Hwf.
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
  PureKObject.well_formed obj →
    ∀ kind1 name1 uid1 kind2 name2 uid2,
      obj_has_controller_parent_of obj kind1 name1 uid1 →
        obj_has_controller_parent_of obj kind2 name2 uid2 →
          kind1 = kind2 ∧ name1 = name2 ∧ uid1 = uid2.
Proof.
  intros Hwf kind1 name1 uid1 kind2 name2 uid2 H1 H2.
  unfold obj_has_controller_parent_of in H1, H2.
  destruct H1 as (os1 & Hownerref1 & Hhas_ctrl1).
  destruct H2 as (os2 & Hownerref2 & Hhas_ctrl2).
  rewrite Hownerref1 in Hownerref2.
  injection Hownerref2 as Hos_eq.
  subst os2.
  destruct obj as [pod | rs].
  - (* Pod case *)
    unfold PureKObject.well_formed in Hwf.
    unfold PurePod.well_formed in Hwf.
    destruct Hwf as (Hwf_meta & _).
    unfold PureObjectMeta.well_formed in Hwf_meta.
    destruct Hwf_meta as (_ & _ & _ & _ & _ & Hwf_ownerref).
    simpl in Hownerref1.
    destruct (PureObjectMeta.OwnerReferences' (PurePod.ObjectMeta' pod)) as [os|]; [|discriminate].
    injection Hownerref1 as <-.
    apply well_formed_owner_references_has_at_most_one_controller_parent with (os := os); assumption.
  - (* ReplicaSet case *)
    unfold PureKObject.well_formed in Hwf.
    unfold PureReplicaSet.well_formed in Hwf.
    destruct Hwf as (Hwf_meta & _).
    unfold PureObjectMeta.well_formed in Hwf_meta.
    destruct Hwf_meta as (_ & _ & _ & _ & _ & Hwf_ownerref).
    simpl in Hownerref1.
    destruct (PureObjectMeta.OwnerReferences' (PureReplicaSet.ObjectMeta' rs)) as [os|]; [|discriminate].
    injection Hownerref1 as <-.
    apply well_formed_owner_references_has_at_most_one_controller_parent with (os := os); assumption.
Qed.
