From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export pod persistentvolumeclaim replicaset statefulset.

Module KObject.
Section def.
Inductive t :=
| Pod (p : v1.Pod.t)
| ReplicaSet (rs : v1.ReplicaSet.t)
| PersistentVolumeClaim (pvc : v1.PersistentVolumeClaim.t)
| StatefulSet (sts : v1.StatefulSet.t).

Definition typemeta o : v1.TypeMeta.t :=
  match o with
  | Pod p => p.(v1.Pod.TypeMeta')
  | ReplicaSet rs => rs.(v1.ReplicaSet.TypeMeta')
  | PersistentVolumeClaim pvc => pvc.(v1.PersistentVolumeClaim.TypeMeta')
  | StatefulSet sts => sts.(v1.StatefulSet.TypeMeta')
  end.

Definition objectmeta o : v1.ObjectMeta.t :=
  match o with
  | Pod p => p.(v1.Pod.ObjectMeta')
  | ReplicaSet rs => rs.(v1.ReplicaSet.ObjectMeta')
  | PersistentVolumeClaim pvc => pvc.(v1.PersistentVolumeClaim.ObjectMeta')
  | StatefulSet sts => sts.(v1.StatefulSet.ObjectMeta')
  end.

Definition update_objectmeta o m: t :=
  match o with
  | Pod pod => Pod (pod <| v1.Pod.ObjectMeta' := m |>)
  | ReplicaSet rs => ReplicaSet (rs <| v1.ReplicaSet.ObjectMeta' := m |>)
  | PersistentVolumeClaim pvc =>
      PersistentVolumeClaim (pvc <| v1.PersistentVolumeClaim.ObjectMeta' := m |>)
  | StatefulSet sts => StatefulSet (sts <| v1.StatefulSet.ObjectMeta' := m |>)
  end.

End def.
End KObject.

Module ObjectSpecV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Inductive t :=
| PodSpec (p : PodSpecV.t)
| ReplicaSetSpec (rs : ReplicaSetSpecV.t)
| PersistentVolumeClaimSpec (pvc : PersistentVolumeClaimSpecV.t)
| StatefulSetSpec (sts : StatefulSetSpecV.t).

Definition valid (v : t) : Prop :=
  match v with
  | PodSpec p => PodSpecV.valid p
  | ReplicaSetSpec rs => ReplicaSetSpecV.valid rs
  | PersistentVolumeClaimSpec pvc => PersistentVolumeClaimSpecV.valid pvc
  | StatefulSetSpec sts => StatefulSetSpecV.valid sts
  end.

Definition valid_create (v : t) : Prop :=
  match v with
  | PodSpec p => PodSpecV.valid_create p
  | ReplicaSetSpec rs => ReplicaSetSpecV.valid_create rs
  | PersistentVolumeClaimSpec pvc => PersistentVolumeClaimSpecV.valid_create pvc
  | StatefulSetSpec sts => StatefulSetSpecV.valid_create sts
  end.

Definition valid_update (old new : t) : Prop :=
  match old, new with
  | PodSpec old, PodSpec new => PodSpecV.valid_update old new
  | ReplicaSetSpec old, ReplicaSetSpec new =>
      ReplicaSetSpecV.valid_update old new
  | PersistentVolumeClaimSpec old, PersistentVolumeClaimSpec new =>
      PersistentVolumeClaimSpecV.valid_update old new
  | StatefulSetSpec old, StatefulSetSpec new =>
      StatefulSetSpecV.valid_update old new
  | _, _ => False
  end.

Global Instance valid_update_dec old new :
  Decision (valid_update old new).
Proof.
  destruct old, new; simpl; apply _.
Defined.
Axiom defaulted: t → t → Prop.

Definition created (input stored : t) : Prop :=
  match input, stored with
  | PodSpec input, PodSpec stored => PodSpecV.created input stored
  | ReplicaSetSpec input, ReplicaSetSpec stored =>
      ReplicaSetSpecV.created input stored
  | PersistentVolumeClaimSpec input, PersistentVolumeClaimSpec stored =>
      PersistentVolumeClaimSpecV.created input stored
  | StatefulSetSpec input, StatefulSetSpec stored =>
      StatefulSetSpecV.created input stored
  | _, _ => False
  end.

(* The API server's update-defaulting relation from the submitted spec to the
   stored spec. Keeping this dispatch resource-specific prevents facts about a
   fully modeled resource, such as exact preservation of the represented Pod
   fields, from being lost behind one unconstrained global axiom. *)
Definition updated (input stored : t) : Prop :=
  match input, stored with
  | PodSpec input, PodSpec stored => PodSpecV.updated input stored
  | ReplicaSetSpec input, ReplicaSetSpec stored =>
      ReplicaSetSpecV.updated input stored
  | PersistentVolumeClaimSpec input, PersistentVolumeClaimSpec stored =>
      PersistentVolumeClaimSpecV.updated input stored
  | StatefulSetSpec input, StatefulSetSpec stored =>
      StatefulSetSpecV.updated input stored
  | _, _ => False
  end.

Definition deepown_l l v dq: iProp Σ :=
  match v with
  | PodSpec p =>
      ∃ c, l ↦{dq} c ∗ PodSpecV.deepown c p dq
  | ReplicaSetSpec rs =>
      ∃ c, l ↦{dq} c ∗ ReplicaSetSpecV.deepown c rs dq
  | PersistentVolumeClaimSpec pvc =>
      ∃ c, l ↦{dq} c ∗ PersistentVolumeClaimSpecV.deepown c pvc dq
  | StatefulSetSpec sts =>
      ∃ c, l ↦{dq} c ∗ StatefulSetSpecV.deepown c sts dq
  end.

End def.
End ObjectSpecV.

Module ObjectStatusV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Inductive t :=
| PodStatus (p : PodStatusV.t)
| ReplicaSetStatus (rs : ReplicaSetStatusV.t)
| PersistentVolumeClaimStatus (pvc : PersistentVolumeClaimStatusV.t)
| StatefulSetStatus (sts : StatefulSetStatusV.t).

Definition valid (v : t) : Prop :=
  match v with
  | PodStatus p => PodStatusV.valid p
  | ReplicaSetStatus rs => ReplicaSetStatusV.valid rs
  | PersistentVolumeClaimStatus pvc => PersistentVolumeClaimStatusV.valid pvc
  | StatefulSetStatus sts => StatefulSetStatusV.valid sts
  end.

Axiom valid_create: t → Prop.
Axiom valid_update: t → t → Prop.
Axiom valid_update_dec: ∀ s1 s2, Decision (valid_update s1 s2).
Global Existing Instance valid_update_dec.
Definition created (input stored : t) : Prop :=
  match input, stored with
  | PodStatus input, PodStatus stored => PodStatusV.created input stored
  | ReplicaSetStatus input, ReplicaSetStatus stored =>
      ReplicaSetStatusV.created input stored
  | PersistentVolumeClaimStatus input, PersistentVolumeClaimStatus stored =>
      PersistentVolumeClaimStatusV.created input stored
  | StatefulSetStatus input, StatefulSetStatus stored =>
      StatefulSetStatusV.created input stored
  | _, _ => False
  end.

Definition updated (input stored : t) : Prop :=
  match input, stored with
  | PodStatus input, PodStatus stored => PodStatusV.updated input stored
  | ReplicaSetStatus input, ReplicaSetStatus stored =>
      ReplicaSetStatusV.updated input stored
  | PersistentVolumeClaimStatus input, PersistentVolumeClaimStatus stored =>
      PersistentVolumeClaimStatusV.updated input stored
  | StatefulSetStatus input, StatefulSetStatus stored =>
      StatefulSetStatusV.updated input stored
  | _, _ => False
  end.

Definition deepown_l l v dq: iProp Σ :=
  match v with
  | PodStatus p =>
      ∃ c, l ↦{dq} c ∗ PodStatusV.deepown c p dq
  | ReplicaSetStatus rs =>
      ∃ c, l ↦{dq} c ∗ ReplicaSetStatusV.deepown c rs dq
  | PersistentVolumeClaimStatus pvc =>
      ∃ c, l ↦{dq} c ∗ PersistentVolumeClaimStatusV.deepown c pvc dq
  | StatefulSetStatus sts =>
      ∃ c, l ↦{dq} c ∗ StatefulSetStatusV.deepown c sts dq
  end.

End def.
End ObjectStatusV.

Module KObjectV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Inductive t :=
| Pod (p : PodV.t)
| ReplicaSet (rs : ReplicaSetV.t)
| PersistentVolumeClaim (pvc : PersistentVolumeClaimV.t)
| StatefulSet (sts : StatefulSetV.t).

Definition typemeta o : v1.TypeMeta.t :=
  match o with
  | Pod p => p.(PodV.TypeMeta')
  | ReplicaSet rs => rs.(ReplicaSetV.TypeMeta')
  | PersistentVolumeClaim pvc => pvc.(PersistentVolumeClaimV.TypeMeta')
  | StatefulSet sts => sts.(StatefulSetV.TypeMeta')
  end.

Definition objectmeta o : ObjectMetaV.t :=
  match o with
  | Pod p => p.(PodV.ObjectMeta')
  | ReplicaSet rs => rs.(ReplicaSetV.ObjectMeta')
  | PersistentVolumeClaim pvc => pvc.(PersistentVolumeClaimV.ObjectMeta')
  | StatefulSet sts => sts.(StatefulSetV.ObjectMeta')
  end.

Definition spec o: ObjectSpecV.t :=
  match o with
  | Pod p => ObjectSpecV.PodSpec p.(PodV.Spec')
  | ReplicaSet rs => ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')
  | PersistentVolumeClaim pvc =>
      ObjectSpecV.PersistentVolumeClaimSpec pvc.(PersistentVolumeClaimV.Spec')
  | StatefulSet sts => ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')
  end.

Definition status o: ObjectStatusV.t :=
  match o with
  | Pod p => ObjectStatusV.PodStatus p.(PodV.Status')
  | ReplicaSet rs => ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status')
  | PersistentVolumeClaim pvc =>
      ObjectStatusV.PersistentVolumeClaimStatus pvc.(PersistentVolumeClaimV.Status')
  | StatefulSet sts => ObjectStatusV.StatefulSetStatus sts.(StatefulSetV.Status')
  end.

Definition kind o : go_string :=
  match o with
  | Pod _ => PodV.kind
  | ReplicaSet _ => ReplicaSetV.kind
  | PersistentVolumeClaim _ => PersistentVolumeClaimV.kind
  | StatefulSet _ => StatefulSetV.kind
  end.

Definition key o : KKey.t :=
  {|
    KKey.Kind' := (kind o);
    KKey.Namespace' := (objectmeta o).(ObjectMetaV.Namespace');
    KKey.Name' := (objectmeta o).(ObjectMetaV.Name')
  |}.

Definition update_objectmeta o m: t :=
  match o with
  | Pod pod => Pod (pod <| PodV.ObjectMeta' := m |>)
  | ReplicaSet rs => ReplicaSet (rs <| ReplicaSetV.ObjectMeta' := m |>)
  | PersistentVolumeClaim pvc =>
      PersistentVolumeClaim (pvc <| PersistentVolumeClaimV.ObjectMeta' := m |>)
  | StatefulSet sts => StatefulSet (sts <| StatefulSetV.ObjectMeta' := m |>)
  end.

Lemma kind_update_objectmeta :
  ∀ o m, kind (update_objectmeta o m) = kind o.
Proof. destruct o; done. Qed.

Lemma typemeta_update_objectmeta :
  ∀ o m, typemeta (update_objectmeta o m) = typemeta o.
Proof. destruct o; done. Qed.

Lemma spec_update_objectmeta :
  ∀ o m, spec (update_objectmeta o m) = spec o.
Proof. destruct o; done. Qed.

Lemma status_update_objectmeta :
  ∀ o m, status (update_objectmeta o m) = status o.
Proof. destruct o; done. Qed.

(* [valid] is the complete invariant guaranteed for an object stored by the
   API server. It combines Kubernetes validity with the normalization facts
   represented by this model; request predicates such as
   [valid_named_create] remain weaker and describe admission before storage. *)
Definition valid o : Prop :=
  valid_typemeta (kind o) (typemeta o) ∧
  valid_resource_version (objectmeta o).(ObjectMetaV.ResourceVersion') ∧
  ObjectMetaV.valid (kind o) (objectmeta o) ∧
  ObjectSpecV.valid (spec o) ∧
  ObjectStatusV.valid (status o).

(** The create strategies for every resource currently represented by [t]
    (Pod, PersistentVolumeClaim, ReplicaSet, and StatefulSet) reset the
    submitted status before validation, so their create predicates impose no
    condition on the input status. If a resource such as Node is added here,
    revisit this: Kubernetes permits and validates a Node's status on create.
    See https://github.com/kubernetes/kubernetes/blob/master/pkg/registry/core/node/strategy.go. *)
Definition valid_nameless_create knd ns o : Prop :=
  knd = kind o ∧
  (* Empty TypeMeta kind/apiVersion fields are valid here: the create request
     decoder defaults them from the REST endpoint before validation. *)
  valid_create_typemeta (kind o) (typemeta o) ∧
  ObjectMetaV.valid_nameless_create (kind o) ns (objectmeta o) ∧
  ObjectSpecV.valid_create (spec o).

Definition valid_named_create knd ns o : Prop :=
  knd = kind o ∧
  (* See [valid_nameless_create]: TypeMeta fields may be omitted on create. *)
  valid_create_typemeta (kind o) (typemeta o) ∧
  ObjectMetaV.valid_named_create (kind o) ns (objectmeta o) ∧
  ObjectSpecV.valid_create (spec o).

Definition same_kind (o1 o2 : t) : Prop :=
  match o1, o2 with
  | Pod _, Pod _ => True
  | ReplicaSet _, ReplicaSet _ => True
  | PersistentVolumeClaim _, PersistentVolumeClaim _ => True
  | StatefulSet _, StatefulSet _ => True
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

Definition named_created ns o o' : Prop :=
  same_kind o o' ∧ (* A shortcut for proving same kind; it can be derived by conditions below *)
  typemeta o = typemeta o' ∧
  ObjectMetaV.named_created ns (objectmeta o) (objectmeta o') ∧
  ObjectSpecV.created (spec o) (spec o') ∧
  ObjectStatusV.created (status o) (status o').

Definition valid2 o : Prop :=
  match o with
  | Pod p => PodV.valid p
  | ReplicaSet rs => ReplicaSetV.valid rs
  | PersistentVolumeClaim pvc => PersistentVolumeClaimV.valid pvc
  | StatefulSet sts => StatefulSetV.valid sts
  end.

Lemma valid_eq_valid2 o :
  valid o = valid2 o.
Proof.
  destruct o as [[tm meta spec status]|[tm meta spec status]|[tm meta spec status]|[tm meta spec status]];
    rewrite /valid /valid2 /PodV.valid /ReplicaSetV.valid
      /PersistentVolumeClaimV.valid /StatefulSetV.valid
      /ObjectSpecV.valid /ObjectStatusV.valid /=; done.
Qed.

Definition valid_nameless_create2 knd ns o : Prop :=
  match o with
  | Pod p => knd = PodV.kind ∧ PodV.valid_nameless_create ns p
  | ReplicaSet rs =>
      knd = ReplicaSetV.kind ∧ ReplicaSetV.valid_nameless_create ns rs
  | PersistentVolumeClaim pvc =>
      knd = PersistentVolumeClaimV.kind ∧
      PersistentVolumeClaimV.valid_nameless_create ns pvc
  | StatefulSet sts =>
      knd = StatefulSetV.kind ∧ StatefulSetV.valid_nameless_create ns sts
  end.

Lemma valid_nameless_create_eq_valid_nameless_create2 knd ns o :
  valid_nameless_create knd ns o = valid_nameless_create2 knd ns o.
Proof. destruct o; reflexivity. Qed.

Definition valid_named_create2 knd ns o : Prop :=
  match o with
  | Pod p => knd = PodV.kind ∧ PodV.valid_named_create ns p
  | ReplicaSet rs =>
      knd = ReplicaSetV.kind ∧ ReplicaSetV.valid_named_create ns rs
  | PersistentVolumeClaim pvc =>
      knd = PersistentVolumeClaimV.kind ∧
      PersistentVolumeClaimV.valid_named_create ns pvc
  | StatefulSet sts =>
      knd = StatefulSetV.kind ∧ StatefulSetV.valid_named_create ns sts
  end.

Lemma valid_named_create_eq_valid_named_create2 knd ns o :
  valid_named_create knd ns o = valid_named_create2 knd ns o.
Proof. destruct o; reflexivity. Qed.

Definition valid_without_meta o : Prop :=
  match o with
  | Pod p => PodV.valid_without_meta p
  | ReplicaSet rs => ReplicaSetV.valid_without_meta rs
  | PersistentVolumeClaim pvc => PersistentVolumeClaimV.valid_without_meta pvc
  | StatefulSet sts => StatefulSetV.valid_without_meta sts
  end.

Definition deepown_l l v dq: iProp Σ :=
  match v with
  | Pod v => PodV.deepown_l l v dq
  | ReplicaSet v => ReplicaSetV.deepown_l l v dq
  | PersistentVolumeClaim v => PersistentVolumeClaimV.deepown_l l v dq
  | StatefulSet v => StatefulSetV.deepown_l l v dq
  end.

Definition deepown_l_without_meta l v dq: iProp Σ :=
  match v with
  | Pod v => PodV.deepown_l_without_meta l v dq
  | ReplicaSet v => ReplicaSetV.deepown_l_without_meta l v dq
  | PersistentVolumeClaim v => PersistentVolumeClaimV.deepown_l_without_meta l v dq
  | StatefulSet v => StatefulSetV.deepown_l_without_meta l v dq
  end.

Definition valid_interface i (l: loc) v: Prop :=
  match v with
  | Pod _ => i = interface.mk (go.PointerType v1.Pod) #l
  | ReplicaSet _ => i = interface.mk (go.PointerType v1.ReplicaSet) #l
  | PersistentVolumeClaim _ => i = interface.mk (go.PointerType v1.PersistentVolumeClaim) #l
  | StatefulSet _ => i = interface.mk (go.PointerType v1.StatefulSet) #l
  end.

Definition deepown_i i v dq: iProp Σ :=
  ∃ l, ⌜ valid_interface i l v ⌝ ∗ deepown_l l v dq.

Definition typemeta_ptr l v: loc :=
  match v with
  | Pod _ => struct_field_ref v1.Pod.t "TypeMeta" l
  | ReplicaSet _ => struct_field_ref v1.ReplicaSet.t "TypeMeta" l
  | PersistentVolumeClaim _ => struct_field_ref v1.PersistentVolumeClaim.t "TypeMeta" l
  | StatefulSet _ => struct_field_ref v1.StatefulSet.t "TypeMeta" l
  end.

Definition objectmeta_ptr l v: loc :=
  match v with
  | Pod _ => struct_field_ref v1.Pod.t "ObjectMeta" l
  | ReplicaSet _ => struct_field_ref v1.ReplicaSet.t "ObjectMeta" l
  | PersistentVolumeClaim _ => struct_field_ref v1.PersistentVolumeClaim.t "ObjectMeta" l
  | StatefulSet _ => struct_field_ref v1.StatefulSet.t "ObjectMeta" l
  end.

Definition spec_ptr l v: loc :=
  match v with
  | Pod _ => struct_field_ref v1.Pod.t "Spec" l
  | ReplicaSet _ => struct_field_ref v1.ReplicaSet.t "Spec" l
  | PersistentVolumeClaim _ => struct_field_ref v1.PersistentVolumeClaim.t "Spec" l
  | StatefulSet _ => struct_field_ref v1.StatefulSet.t "Spec" l
  end.

Definition status_ptr l v: loc :=
  match v with
  | Pod _ => struct_field_ref v1.Pod.t "Status" l
  | ReplicaSet _ => struct_field_ref v1.ReplicaSet.t "Status" l
  | PersistentVolumeClaim _ => struct_field_ref v1.PersistentVolumeClaim.t "Status" l
  | StatefulSet _ => struct_field_ref v1.StatefulSet.t "Status" l
  end.

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
    (typemeta_ptr l v) ↦{dq} (typemeta v) ∗
    ObjectMetaV.deepown_l (objectmeta_ptr l v) (objectmeta v) dq ∗
    ObjectSpecV.deepown_l (spec_ptr l v) (spec v) dq ∗
    ObjectStatusV.deepown_l (status_ptr l v) (status v) dq.
Proof.
  destruct v as [p|rs|pvc|sts]; simpl.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply PodV.deepown_l_split.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply ReplicaSetV.deepown_l_split.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply PersistentVolumeClaimV.deepown_l_split.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply StatefulSetV.deepown_l_split.
Qed.

(* TODO: deepown_l_merge is only used for merging updated objectmeta; generalize it later *)
Lemma deepown_l_merge l v vm dq:
  l ≠ null →
  (typemeta_ptr l v) ↦{dq} (typemeta v) ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l v) vm dq ∗
  ObjectSpecV.deepown_l (spec_ptr l v) (spec v) dq ∗
  ObjectStatusV.deepown_l (status_ptr l v) (status v) dq ⊢
    deepown_l l (update_objectmeta v vm) dq.
Proof.
  intros Hnot_null.
  destruct v as [p|rs|pvc|sts]; simpl.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (PodV.deepown_l_merge l p vm dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (ReplicaSetV.deepown_l_merge l rs vm dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (PersistentVolumeClaimV.deepown_l_merge l pvc vm dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (StatefulSetV.deepown_l_merge l sts vm dq Hnot_null).
Qed.

Lemma deepown_l_restore l v dq:
  l ≠ null →
  (typemeta_ptr l v) ↦{dq} (typemeta v) ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l v) (objectmeta v) dq ∗
  ObjectSpecV.deepown_l (spec_ptr l v) (spec v) dq ∗
  ObjectStatusV.deepown_l (status_ptr l v) (status v) dq ⊢
    deepown_l l v dq.
Proof.
  intros Hnot_null.
  destruct v as [p|rs|pvc|sts]; simpl.
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (PodV.deepown_l_restore l p dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (ReplicaSetV.deepown_l_restore l rs dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (PersistentVolumeClaimV.deepown_l_restore l pvc dq Hnot_null).
  - rewrite /ObjectSpecV.deepown_l /ObjectStatusV.deepown_l.
    iApply (StatefulSetV.deepown_l_restore l sts dq Hnot_null).
Qed.

Lemma deepown_i_yields_deepown_l i l v dq:
  deepown_i i v dq ∗ ⌜ valid_interface i l v ⌝ -∗
    deepown_l l v dq.
Proof.
  iIntros "[Hdeepown_i %Hvalid]".
  iDestruct "Hdeepown_i" as (l') "[%Hvalid' Hdeepown_l]".
  destruct v; simpl in *;
  subst i;
  simplify_eq;
  done.
Qed.

Lemma valid_nameless_pod_set_name pod namespace name :
  valid_nameless_create PodV.kind namespace (Pod pod) →
  name ≠ ""%go →
  valid_name PodV.kind name →
  valid_named_create PodV.kind namespace
    (Pod (PodV.update_objectmeta pod
      (pod.(PodV.ObjectMeta') <| ObjectMetaV.Name' := name |>))).
Proof.
  rewrite /valid_nameless_create /valid_named_create /=.
  intros (Hkind & Htypemeta & Hmeta & Hspec)
    Hname_nonempty Hname_valid.
  assert (Hmeta_named : ObjectMetaV.valid_named_create PodV.kind namespace
      (pod.(PodV.ObjectMeta') <| ObjectMetaV.Name' := name |>)).
  { rewrite /ObjectMetaV.valid_nameless_create in Hmeta.
    rewrite /ObjectMetaV.valid_named_create /=.
    destruct Hmeta as (Hgenerate_name & _ & _ & Hnamespace & Hlabels &
      Hannotations & Howner_references & Hfinalizers & Hmanaged_fields).
    split_and!; done. }
  split_and!; done.
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

Definition no_speculative_parent_reference meta (used_uid: gset types.UID.t): Prop :=
  ∀ kind name uid, meta_parent_ref_is meta kind name uid → uid ∈ used_uid.

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
  KObjectV.valid2 obj →
    ObjectMetaV.valid (KObjectV.kind obj) (KObjectV.objectmeta obj).
Proof.
  rewrite -KObjectV.valid_eq_valid2.
  intros (_ & _ & Hmeta & _ & _). exact Hmeta.
Qed.

Lemma valid_object_has_valid_key key obj:
  key = KObjectV.key obj →
  KObjectV.valid2 obj →
    key.(KKey.Name') ≠ ""%go ∧
    valid_name key.(KKey.Kind') key.(KKey.Name') ∧
    key.(KKey.Namespace') ≠ ""%go ∧
    valid_namespace key.(KKey.Namespace').
Proof.
  intros Hkey Hwf.
  apply valid_object_has_valid_objectmeta in Hwf.
  destruct obj; simpl in *; subst key; simpl;
  destruct Hwf as [_ [Hname_ne [Hname_valid [Hns_ne Hns_valid]]]];
  destruct Hns_valid as [Hns_valid _];
  exact (conj Hname_ne (conj Hname_valid (conj Hns_ne Hns_valid))).
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
  KObjectV.valid2 obj →
    ∀ kind1 name1 uid1 kind2 name2 uid2,
      obj_has_controller_parent_of obj kind1 name1 uid1 →
        obj_has_controller_parent_of obj kind2 name2 uid2 →
          kind1 = kind2 ∧ name1 = name2 ∧ uid1 = uid2.
Proof.
  intros Hwf kind1 name1 uid1 kind2 name2 uid2 H1 H2.
  unfold obj_has_controller_parent_of in H1, H2.
  apply valid_object_has_valid_objectmeta in Hwf.
  pose proof (ObjectMetaV.valid_owner_references_of_valid _ Hwf) as Hwf_ownerref.
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
   - [Hvalid_typemeta]: typemeta validity of the pre-update object.
   - [Hvalid_rv]: validity of the replacement metadata's resource version.
   - [Hvalid_meta]: validity of the replacement objectmeta.
   - [Hvalid_spec]: validity of the object's spec before the objectmeta update.
   - [Hvalid_status]: validity of the object's status before the objectmeta
     update.
   The tactic combines these to rebuild [KObjectV.valid] for the updated object,
   reusing [KObjectV.spec_update_objectmeta] and
   [KObjectV.status_update_objectmeta]. In practice this is most convenient
   after destructing the concrete object constructors so [simpl] exposes the
   required equalities. *)
Ltac solve_update_objectmeta_valid
    Hvalid_typemeta Hvalid_rv Hvalid_meta Hvalid_spec Hvalid_status :=
  split_and!;
    [ rewrite KObjectV.kind_update_objectmeta;
      rewrite KObjectV.typemeta_update_objectmeta;
      exact Hvalid_typemeta
    | simpl; exact Hvalid_rv
    | rewrite KObjectV.kind_update_objectmeta; exact Hvalid_meta
    | rewrite KObjectV.spec_update_objectmeta; exact Hvalid_spec
    | rewrite KObjectV.status_update_objectmeta; exact Hvalid_status
    ].
