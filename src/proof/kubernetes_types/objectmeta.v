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

Definition without_resource_version (m : t) : t :=
  m <| ResourceVersion' := ""%go |>.

Definition equiv_except_resource_version (m1 m2 : t) : Prop :=
  without_resource_version m1 = without_resource_version m2.

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

Lemma valid_name_of_valid {kind} m:
  valid kind m →
  valid_name kind m.(Name').
Proof. unfold valid. tauto. Qed.

Lemma valid_name_nonempty_of_valid {kind} m:
  valid kind m →
  m.(Name') ≠ ""%go.
Proof. unfold valid. tauto. Qed.

Lemma valid_namespace_of_valid {kind} m:
  valid kind m →
  valid_namespace m.(Namespace').
Proof. unfold valid. tauto. Qed.

Lemma valid_namespace_nonempty_of_valid {kind} m:
  valid kind m →
  m.(Namespace') ≠ ""%go.
Proof. unfold valid. tauto. Qed.

Lemma valid_uid_of_valid {kind} m:
  valid kind m →
  valid_uid m.(UID').
Proof. unfold valid. tauto. Qed.

(* A stored object's metadata is admissible as a create request into its own
   namespace: [valid] is strictly stronger than [valid_create] except for the
   namespace agreement, which the caller supplies. *)
Lemma valid_create_of_valid {kind ns} m :
  valid kind m →
  ns = m.(Namespace') →
  valid_create kind ns m.
Proof.
  unfold valid, valid_create.
  intros (Hgenerate_name & Hname_nonempty & Hname & _ & Hnamespace_valid &
    _ & Hlabels & Hannotations & Howner_references & Hfinalizers &
    Hmanaged_fields & _) Hnamespace.
  case_decide; first contradiction.
  split; [split; assumption|].
  split; [right; split; [assumption|symmetry; exact Hnamespace]|].
  repeat split; assumption.
Qed.

Lemma equiv_except_resource_version_uid m1 m2 :
  equiv_except_resource_version m1 m2 →
  m1.(UID') = m2.(UID').
Proof.
  destruct m1, m2; simpl. intros H. inversion H. done.
Qed.

Lemma equiv_except_resource_version_deletion_timestamp m1 m2 :
  equiv_except_resource_version m1 m2 →
  m1.(DeletionTimestamp') = m2.(DeletionTimestamp').
Proof.
  destruct m1, m2; simpl. intros H. inversion H. done.
Qed.

End proof.
End ObjectMetaV.
