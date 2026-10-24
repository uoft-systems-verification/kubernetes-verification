From New.generatedviews Require Export objectmeta.
From New.object_specs Require Export typemeta.
From New.proof Require Import prelude empty_ffi util.
From New.object_specs Require Export common.

Module OwnerReferenceV.
Include ObjectMetaView.OwnerReferenceV.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L69-L90
   Kubernetes requires an owner reference to have a nonempty API version,
   kind, name, and UID, and rejects Event as an owner. [valid_api_version]
   restricts the first two fields to the concrete, non-Event kinds supported
   by this model. *)
Definition valid (v : t) : Prop :=
  valid_api_version v.(Kind') v.(APIVersion') ∧
  v.(Name') ≠ ""%go ∧
  v.(UID') ≠ ""%go.

Definition list_valid (os: list t) : Prop :=
  (* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L92 *)
  ∀ i1 o1 i2 o2,
    os !! i1 = Some o1 ∧ o1.(Controller') = Some true ∧
    os !! i2 = Some o2 ∧ o2.(Controller') = Some true →
      i1 = i2.

Definition refers_to_controller v kind name uid : Prop :=
  v.(Kind') = kind ∧
  v.(Name') = name ∧
  v.(UID') = uid ∧
  v.(BlockOwnerDeletion') = Some true ∧
  v.(Controller') = Some true.

End OwnerReferenceV.

Module FieldsV1V := ObjectMetaView.FieldsV1V.

Module ManagedFieldsEntryV := ObjectMetaView.ManagedFieldsEntryV.

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
Include ObjectMetaView.ObjectMetaV.

Local Transparent deepown.
Definition without_resource_version (m : t) : t :=
  m <| ResourceVersion' := ""%go |>.

Definition equiv_except_resource_version (m1 m2 : t) : Prop :=
  without_resource_version m1 = without_resource_version m2.

Lemma equiv_except_resource_version_eq m1 m2 :
  equiv_except_resource_version m1 m2 →
  m2 = m1 <| ResourceVersion' := m2.(ResourceVersion') |>.
Proof.
  destruct m1, m2.
  rewrite /equiv_except_resource_version /without_resource_version /=.
  intros H. injection H; intros; subst; done.
Qed.

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

Definition valid_create kind ns (m : t) : Prop :=
  (if decide (m.(Name') = ""%go)
   then
     valid_generate_name kind m.(GenerateName') ∧
     (* The generated suffix requires [generateName] to contain at most 58 bytes:
        https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/storage/names/generate.go#L46 *)
     length m.(GenerateName') ≤ 58
   else
     (m.(GenerateName') ≠ ""%go → valid_generate_name kind m.(GenerateName')) ∧
     valid_name kind m.(Name')) ∧
  (* The namespace in the meta is either empty or equal to the provided ns *)
  (m.(Namespace') = ""%go ∨ valid_namespace m.(Namespace') ∧ m.(Namespace') = ns) ∧
  valid_labels m.(Labels') ∧
  valid_annotations m.(Annotations') ∧
  valid_owner_references m.(OwnerReferences') ∧
  valid_finalizers m.(Finalizers') ∧
  valid_managed_fields m.(ManagedFields').

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

(** A sufficient request-shape condition for the controller updates currently
    supported by the model. It is a top-level predicate over the existing and
    submitted metadata and abstracts away preparation of unrepresented fields.
    The first branch covers ordinary label/annotation updates. The second
    covers controller release, whose request differs from the stored metadata
    only in owner references and may omit the server-managed resource version.
    [old] is the existing stored metadata.
    [input] is the metadata submitted in the update request. *)
Definition valid_update old input : Prop :=
  (valid_simple_update old input ∨
   equiv_except_resource_version
     (old <| OwnerReferences' := input.(OwnerReferences') |>) input) ∧
  valid_labels input.(Labels') ∧
  valid_annotations input.(Annotations') ∧
  valid_owner_references input.(OwnerReferences') ∧
  valid_finalizers input.(Finalizers') ∧
  valid_managed_fields input.(ManagedFields').

(** [expected] is the request metadata after resource-specific create
    preparation. [stored] is the metadata stored by a successful create.
    The server-generated UID, creation timestamp, and resource version are not
    related to values supplied in the request. Generation is also omitted
    because its create-time behavior is determined by each resource's strategy. *)
Definition created ns expected stored : Prop :=
  (if decide (expected.(Name') = ""%go)
   then stored.(Name') ≠ ""%go
   else stored.(Name') = expected.(Name')) ∧
  stored.(Namespace') = ns ∧
  stored.(GenerateName') = expected.(GenerateName') ∧
  stored.(DeletionTimestamp') = None ∧
  stored.(Annotations') = expected.(Annotations') ∧
  stored.(Labels') = expected.(Labels') ∧
  stored.(OwnerReferences') = expected.(OwnerReferences') ∧
  stored.(Finalizers') = expected.(Finalizers') ∧
  stored.(DeletionGracePeriodSeconds') = None ∧
  stored.(SelfLink') = ""%go.

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

End ObjectMetaV.
