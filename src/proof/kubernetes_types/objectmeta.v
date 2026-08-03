From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export common.

Module OwnerReferenceV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Record t := mk {
  APIVersion' : go_string;
  Kind' : go_string;
  Name' : go_string;
  UID' : types.UID.t;
  Controller' : option bool;
  BlockOwnerDeletion' : option bool;
}.

Global Instance eq_dec : EqDecision t.
Proof. solve_decision. Qed.

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

Definition refers_to_controller v kind name uid : Prop :=
  v.(Kind') = kind ∧
  v.(Name') = name ∧
  v.(UID') = uid ∧
  v.(BlockOwnerDeletion') = Some true ∧
  v.(Controller') = Some true.

End OwnerReferenceV.

Module ManagedFieldsEntryV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.

Axiom t : Type.
Axiom eq_dec : EqDecision t.
Global Existing Instance eq_dec.

Axiom deepown : v1.ManagedFieldsEntry.t → t → dfrac → iProp Σ.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End ManagedFieldsEntryV.

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
Definition valid_finalizers (finalizers : option (list go_string)) : Prop :=
  match finalizers with
  | None => True
  | Some finalizers => Forall valid_label_name finalizers
  end.

#[global] Instance valid_finalizers_dec fs : Decision (valid_finalizers fs).
Proof.
  destruct fs as [finalizers|]; simpl; last (left; done).
  induction finalizers as [|finalizer finalizers IH]; first (left; constructor).
  destruct (decide (valid_label_name finalizer)) as [Hvalid|Hnot_valid].
  - destruct IH as [Hvalid_tail|Hnot_valid_tail].
    + left. by constructor.
    + right. intros Hvalid_finalizers. inversion Hvalid_finalizers. contradiction.
  - right. intros Hvalid_finalizers. inversion Hvalid_finalizers. contradiction.
Defined.

(* Materializing a nil finalizer slice as an allocated empty slice preserves
   Kubernetes finalizer validation. *)
Lemma valid_finalizers_default : ∀ finalizers,
  valid_finalizers finalizers →
  valid_finalizers (Some (default [] finalizers)).
Proof.
  intros [finalizers|] Hvalid; first exact Hvalid.
  constructor.
Qed.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/validation/validation.go#L269 *)
Axiom valid_managed_fields : option (list ManagedFieldsEntryV.t) → Prop.
Axiom valid_managed_fields_none : valid_managed_fields None.

Module ObjectMetaV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
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

Global Instance eq_dec : EqDecision t.
Proof. solve_decision. Defined.

(* [valid] is the complete invariant for metadata stored by the API server:
   it includes both validation and resource-independent normalization.
   Kubernetes clears the deprecated SelfLink field before storage.
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L155

   We intentionally don't put valid_resource_version here because kview's
   meta fragment needs [valid] and the fragment doesn't carry the resource
   version. The fragment does carry a KKey, which supplies the kind argument. *)
Definition valid kind (m: t) : Prop :=
  (m.(GenerateName') ≠ ""%go → valid_generate_name kind m.(GenerateName')) ∧
  m.(Name') ≠ ""%go ∧
  valid_name kind m.(Name') ∧
  m.(Namespace') ≠ ""%go ∧
  valid_namespace m.(Namespace') ∧
  (* Kubernetes does not really pose any requirement on uid, but
     we want to ensure the uid does not contain special characters like
     slash. This holds in practice because uuid does not contain slash. *)
  valid_uid m.(UID') ∧
  (* Kubernetes validates generation as non-negative on create/update, but
     generation is an int64 and some server-side increments do not guard
     against overflow. Do not make non-negativity a persistent object
     invariant. *)
  (* valid_generation m.(Generation') ∧ *)
  valid_labels m.(Labels') ∧
  valid_annotations m.(Annotations') ∧
  valid_owner_references m.(OwnerReferences') ∧
  valid_finalizers m.(Finalizers') ∧
  valid_managed_fields m.(ManagedFields') ∧
  m.(SelfLink') = ""%go.

Definition valid_nameless_create kind ns (m: t) : Prop :=
  valid_generate_name kind m.(GenerateName') ∧
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

Definition valid_named_create kind ns (m: t) : Prop :=
  (m.(GenerateName') ≠ ""%go → valid_generate_name kind m.(GenerateName')) ∧
  m.(Name') ≠ ""%go ∧
  valid_name kind m.(Name') ∧
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
  m'.(DeletionTimestamp') = None ∧
  m'.(Annotations') = m.(Annotations') ∧
  m'.(Labels') = m.(Labels') ∧
  m'.(OwnerReferences') = m.(OwnerReferences') ∧
  m'.(Finalizers') = m.(Finalizers').

Definition named_created ns m m' : Prop :=
  m'.(Namespace') = ns ∧
  m'.(Name') = m.(Name') ∧
  m'.(GenerateName') = m.(GenerateName') ∧
  m'.(DeletionTimestamp') = None ∧
  m'.(Annotations') = m.(Annotations') ∧
  m'.(Labels') = m.(Labels') ∧
  m'.(OwnerReferences') = m.(OwnerReferences') ∧
  m'.(Finalizers') = m.(Finalizers').

(* m is the existing meta and m' is the meta passed to update.
   valid_simple_update states the precondition for a simple update to succeed.
   It essentially states that everything except Annotations and Labels remains unchanged.
   Note that it does not mention ResourceVersion because the meta frag doesn't carry the
   ResourceVersion. *)
Definition valid_simple_update m m' : Prop :=
  m'.(Name') = m.(Name') ∧
  m'.(GenerateName') = m.(GenerateName') ∧
  m'.(Namespace') = m.(Namespace') ∧
  m'.(SelfLink') = m.(SelfLink') ∧
  m'.(UID') = m.(UID') ∧
  m'.(Generation') = m.(Generation') ∧
  m'.(CreationTimestamp') = m.(CreationTimestamp') ∧
  m'.(DeletionTimestamp') = m.(DeletionTimestamp') ∧
  m'.(DeletionGracePeriodSeconds') = m.(DeletionGracePeriodSeconds') ∧
  m'.(OwnerReferences') = m.(OwnerReferences') ∧
  m'.(Finalizers') = m.(Finalizers') ∧
  m'.(ManagedFields') = m.(ManagedFields').

Global Instance valid_simple_update_dec m m' :
  Decision (valid_simple_update m m').
Proof.
  unfold valid_simple_update.
  solve_decision.
Qed.

(* m is the meta passed to update and m' is the new meta after update.
   updated doesn't mention Generation and ResourceVersion because
   these two fields will increment after update, and the client doesn't
   need to know their exact values. *)
Definition updated m m' : Prop :=
  m'.(Name') = m.(Name') ∧
  m'.(GenerateName') = m.(GenerateName') ∧
  m'.(Namespace') = m.(Namespace') ∧
  m'.(SelfLink') = m.(SelfLink') ∧
  m'.(UID') = m.(UID') ∧
  m'.(CreationTimestamp') = m.(CreationTimestamp') ∧
  m'.(DeletionTimestamp') = m.(DeletionTimestamp') ∧
  m'.(DeletionGracePeriodSeconds') = m.(DeletionGracePeriodSeconds') ∧
  m'.(Labels') = m.(Labels') ∧
  m'.(Annotations') = m.(Annotations') ∧
  m'.(OwnerReferences') = m.(OwnerReferences') ∧
  m'.(Finalizers') = m.(Finalizers') ∧
  m'.(ManagedFields') = m.(ManagedFields').

Definition deepown (c: v1.ObjectMeta.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_name" ∷ ⌜ c.(v1.ObjectMeta.Name') = v.(Name') ⌝ ∗
  "%Hdeepown_generatename" ∷ ⌜ c.(v1.ObjectMeta.GenerateName') = v.(GenerateName') ⌝ ∗
  "%Hdeepown_namespace" ∷ ⌜ c.(v1.ObjectMeta.Namespace') = v.(Namespace') ⌝ ∗
  "%Hdeepown_selflink" ∷ ⌜ c.(v1.ObjectMeta.SelfLink') = v.(SelfLink') ⌝ ∗
  "%Hdeepown_uid" ∷ ⌜ c.(v1.ObjectMeta.UID') = v.(UID') ⌝ ∗
  "%Hdeepown_resourceversion" ∷ ⌜ c.(v1.ObjectMeta.ResourceVersion') = v.(ResourceVersion') ⌝ ∗
  "%Hdeepown_generation" ∷ ⌜ c.(v1.ObjectMeta.Generation') = v.(Generation') ⌝ ∗
  "Hdeepown_creationtimestamp" ∷ TimeV.deepown c.(v1.ObjectMeta.CreationTimestamp') v.(CreationTimestamp') dq ∗
  (* TODO: define this repeated pattern to reduce the code below *)
  "%Hdeepown_deletiontimestamp_none" ∷ ⌜c.(v1.ObjectMeta.DeletionTimestamp') = null ↔ v.(DeletionTimestamp') = None⌝ ∗
  "Hdeepown_deletiontimestamp_some" ∷ (match v.(DeletionTimestamp') with
  | Some vd => ∃ cd, c.(v1.ObjectMeta.DeletionTimestamp') ↦{dq} cd ∗ TimeV.deepown cd vd dq
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

Section proof.

Lemma valid_generate_name_of_valid {kind} m:
  valid kind m →
  m.(GenerateName') ≠ ""%go →
  valid_generate_name kind m.(GenerateName').
Proof. unfold valid. tauto. Qed.

Lemma valid_name_nonempty_of_valid {kind} m:
  valid kind m →
  m.(Name') ≠ ""%go.
Proof. unfold valid. tauto. Qed.

Lemma valid_name_of_valid {kind} m:
  valid kind m →
  valid_name kind m.(Name').
Proof. unfold valid. tauto. Qed.

Lemma valid_namespace_nonempty_of_valid {kind} m:
  valid kind m →
  m.(Namespace') ≠ ""%go.
Proof. unfold valid. tauto. Qed.

Lemma valid_namespace_of_valid {kind} m:
  valid kind m →
  valid_namespace m.(Namespace').
Proof. unfold valid. tauto. Qed.

Lemma valid_uid_of_valid {kind} m:
  valid kind m →
  valid_uid m.(UID').
Proof. unfold valid. tauto. Qed.

Lemma valid_labels_of_valid {kind} m:
  valid kind m →
  valid_labels m.(Labels').
Proof. unfold valid. tauto. Qed.

Lemma valid_annotations_of_valid {kind} m:
  valid kind m →
  valid_annotations m.(Annotations').
Proof. unfold valid. tauto. Qed.

Lemma valid_owner_references_of_valid {kind} m:
  valid kind m →
  valid_owner_references m.(OwnerReferences').
Proof. unfold valid. tauto. Qed.

Lemma valid_finalizers_of_valid {kind} m:
  valid kind m →
  valid_finalizers m.(Finalizers').
Proof. unfold valid. tauto. Qed.

Lemma valid_managed_fields_of_valid {kind} m:
  valid kind m →
  valid_managed_fields m.(ManagedFields').
Proof. unfold valid. tauto. Qed.

Definition without_resource_version (m : t) : t :=
  m <| ResourceVersion' := ""%go |>.

Definition equiv_except_resource_version (m1 m2 : t) : Prop :=
  without_resource_version m1 = without_resource_version m2.

(* Metadata updates accepted by the current model. The first branch covers
   ordinary label/annotation updates; the second covers controller release,
   whose request differs from the stored metadata only in ownerReferences
   (and may omit the server-managed resourceVersion). *)
(* TODO: generalize valid_update *)
Definition valid_update m m' : Prop :=
  valid_simple_update m m' ∨
  equiv_except_resource_version
    (m <| OwnerReferences' := m'.(OwnerReferences') |>) m'.

Lemma equiv_except_resource_version_name m1 m2 :
  equiv_except_resource_version m1 m2 →
  m1.(Name') = m2.(Name').
Proof.
  destruct m1, m2; simpl. intros H. inversion H. done.
Qed.

Lemma equiv_except_resource_version_namespace m1 m2 :
  equiv_except_resource_version m1 m2 →
  m1.(Namespace') = m2.(Namespace').
Proof.
  destruct m1, m2; simpl. intros H. inversion H. done.
Qed.

Lemma equiv_except_resource_version_uid m1 m2 :
  equiv_except_resource_version m1 m2 →
  m1.(UID') = m2.(UID').
Proof.
  destruct m1, m2; simpl. intros H. inversion H. done.
Qed.

Lemma equiv_except_resource_version_valid {kind} m1 m2 :
  equiv_except_resource_version m1 m2 →
  valid kind m1 →
  valid kind m2.
Proof.
  destruct m1, m2; simpl. intros H Heq. inversion H; subst.
  unfold valid in *. tauto.
Qed.

Lemma equiv_except_resource_version_sym m1 m2 :
  equiv_except_resource_version m1 m2 →
  equiv_except_resource_version m2 m1.
Proof.
  unfold equiv_except_resource_version. intros H. symmetry. done.
Qed.

Lemma equiv_except_resource_version_deletion_timestamp m1 m2 :
  equiv_except_resource_version m1 m2 →
  m1.(DeletionTimestamp') = m2.(DeletionTimestamp').
Proof.
  destruct m1, m2; simpl. intros H. inversion H. done.
Qed.

Lemma equiv_except_resource_version_finalizers m1 m2 :
  equiv_except_resource_version m1 m2 →
  m1.(Finalizers') = m2.(Finalizers').
Proof.
  rewrite /equiv_except_resource_version /without_resource_version.
  destruct m1, m2; simpl.
  intros Hmeta_eq. injection Hmeta_eq. done.
Qed.

End proof.
End ObjectMetaV.
