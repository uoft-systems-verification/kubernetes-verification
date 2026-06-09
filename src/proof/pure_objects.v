From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof Require Export time string.
From New.proof Require Import prelude empty_ffi.
Export apimodel.apimodel.
Module KKey := code.kubernetes_model.apimodel.apimodel.KKey.

(* This predicate is intentionally axiomatized. The concrete definition is
   irrelevant here; the model only relies on API-server generated names never
   forming keys that satisfy it. *)
Axiom reserved_key_pred : KKey.t → Prop.

Lemma struct_fields_split `{hG: heapGS Σ} {V} `{!TypedPointsto (Σ:=Σ) V} l (v : V) dq :
  l ↦{dq} v ⊢@{iProp Σ} typed_pointsto_def l v dq ∗ ⌜l ≠ null⌝.
Proof. rewrite typed_pointsto_unseal /typed_pointsto_wrap. iIntros "[$ $]". Qed.

Lemma struct_fields_combine `{hG: heapGS Σ} {V} `{!TypedPointsto (Σ:=Σ) V} l (v : V) dq :
  l ≠ null →
  typed_pointsto_def l v dq ⊢@{iProp Σ} l ↦{dq} v.
Proof. intros Hnot_null. iApply (typed_pointsto_combine l v dq Hnot_null). Qed.

Module TimeV.
Section def.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Axiom t : Type.
Axiom eq_dec : EqDecision t.
Global Existing Instance eq_dec.
Axiom deepown : v1.Time.t → t → iProp Σ.
End def.
End TimeV.

Axiom valid_kind: go_string → Prop.

(* Upstream reference: Kubernetes validates CRD `spec.names.kind` by
   lowercasing it and checking it as a DNS-1035 label, which excludes `/`.
   See:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiextensions-apiserver/pkg/apis/apiextensions/validation/validation.go#L762-L763 *)
Lemma valid_kind_slash_free kind:
  valid_kind kind → slash_free kind.
Proof. Admitted.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L169 *)
Axiom valid_name: go_string → Prop.

Lemma valid_name_slash_free name:
  valid_name name → slash_free name.
Proof. Admitted.

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

Axiom valid_uid: go_string → Prop.

Lemma valid_uid_non_empty uid:
  valid_uid uid → uid ≠ ""%go.
Proof. Admitted.

(* This holds in practice because uuid does not contain slash *)
Lemma valid_uid_slash_free uid:
  valid_uid uid → slash_free uid.
Proof. Admitted.

(* A valid resource version should be parsable to a int64, which implies it's not empty *)
Axiom valid_resource_version: go_string → Prop.

Lemma valid_resource_version_non_empty rv:
  valid_resource_version rv → rv ≠ ""%go.
Proof. Admitted.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/generic.go#L82 *)
Definition valid_generation (generation: w64) : Prop :=
  (0 <= sint.Z generation)%Z.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/validation/validation.go#L113 *)
Axiom valid_labels: option (gmap go_string go_string) → Prop.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L44 *)
Axiom valid_annotations: option (gmap go_string go_string) → Prop.

Module OwnerReferenceV.
Section def.
Context `{hG: !heapGS Σ}.
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
Context `{hG: !heapGS Σ}.
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
Axiom valid_finalizers: option (list go_string) → Prop.
Axiom valid_finalizers_dec : ∀ fs, Decision (valid_finalizers fs).
Global Existing Instance valid_finalizers_dec.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/validation/validation.go#L269 *)
Axiom valid_managed_fields : option (list ManagedFieldsEntryV.t) → Prop.

Module ObjectMetaV.
Section def.
Context `{hG: !heapGS Σ}.
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

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L155 *)
Definition valid (m: t) : Prop :=
  (m.(GenerateName') ≠ ""%go → valid_generate_name m.(GenerateName')) ∧
  m.(Name') ≠ ""%go ∧
  valid_name m.(Name') ∧
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

Definition valid_named_create ns (m: t) : Prop :=
  (m.(GenerateName') ≠ ""%go → valid_generate_name m.(GenerateName')) ∧
  m.(Name') ≠ ""%go ∧
  valid_name m.(Name') ∧
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
  "Hdeepown_creationtimestamp" ∷ TimeV.deepown c.(v1.ObjectMeta.CreationTimestamp') v.(CreationTimestamp') ∗
  (* TODO: define this repeated pattern to reduce the code below *)
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

Section proof.

Lemma valid_generate_name_of_valid m:
  valid m →
  m.(GenerateName') ≠ ""%go →
  valid_generate_name m.(GenerateName').
Proof. unfold valid. tauto. Qed.

Lemma valid_name_nonempty_of_valid m:
  valid m →
  m.(Name') ≠ ""%go.
Proof. unfold valid. tauto. Qed.

Lemma valid_name_of_valid m:
  valid m →
  valid_name m.(Name').
Proof. unfold valid. tauto. Qed.

Lemma valid_namespace_nonempty_of_valid m:
  valid m →
  m.(Namespace') ≠ ""%go.
Proof. unfold valid. tauto. Qed.

Lemma valid_namespace_of_valid m:
  valid m →
  valid_namespace m.(Namespace').
Proof. unfold valid. tauto. Qed.

Lemma valid_uid_of_valid m:
  valid m →
  valid_uid m.(UID').
Proof. unfold valid. tauto. Qed.

Lemma valid_labels_of_valid m:
  valid m →
  valid_labels m.(Labels').
Proof. unfold valid. tauto. Qed.

Lemma valid_annotations_of_valid m:
  valid m →
  valid_annotations m.(Annotations').
Proof. unfold valid. tauto. Qed.

Lemma valid_owner_references_of_valid m:
  valid m →
  valid_owner_references m.(OwnerReferences').
Proof. unfold valid. tauto. Qed.

Lemma valid_finalizers_of_valid m:
  valid m →
  valid_finalizers m.(Finalizers').
Proof. unfold valid. tauto. Qed.

Lemma valid_managed_fields_of_valid m:
  valid m →
  valid_managed_fields m.(ManagedFields').
Proof. unfold valid. tauto. Qed.

Definition without_resource_version (m : t) : t :=
  m <| ResourceVersion' := ""%go |>.

Definition equiv_except_resource_version (m1 m2 : t) : Prop :=
  without_resource_version m1 = without_resource_version m2.

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

Lemma equiv_except_resource_version_valid m1 m2 :
  equiv_except_resource_version m1 m2 →
  valid m1 →
  valid m2.
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

Module PodSpecV.
Section def.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Axiom t : Type.
Axiom valid: t → Prop.
Axiom deepown : v1.PodSpec.t → t → iProp Σ.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v.

End def.
End PodSpecV.

Module PodStatusV.
Section def.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Axiom t : Type.
Axiom valid: t → Prop.
Axiom deepown : v1.PodStatus.t → t → iProp Σ.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v.

End def.
End PodStatusV.

Module PodV.
Section def.
Context `{hG: !heapGS Σ}.
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
  ObjectMetaV.valid pod.(ObjectMeta') ∧
  PodSpecV.valid pod.(Spec') ∧
  PodStatusV.valid pod.(Status').

Definition valid_without_meta (pod: t) : Prop :=
  PodSpecV.valid pod.(Spec') ∧
  PodStatusV.valid pod.(Status').

Definition deepown (c: v1.Pod.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.Pod.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.Pod.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_podspec" ∷ PodSpecV.deepown c.(v1.Pod.Spec') v.(Spec') ∗
  "Hdeepown_podstatus" ∷ PodStatusV.deepown c.(v1.Pod.Status') v.(Status').

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

Definition deepown_without_meta (c: v1.Pod.t) (v: t): iProp Σ :=
  "Hdeepown_spec" ∷ PodSpecV.deepown c.(v1.Pod.Spec') v.(Spec') ∗
  "Hdeepown_status" ∷ PodStatusV.deepown c.(v1.Pod.Status') v.(Status').

Definition deepown_l_without_meta l v (dq: dfrac): iProp Σ :=
  ∃ c,
  spec_ptr l ↦{dq} c.(v1.Pod.Spec') ∗
  status_ptr l ↦{dq} c.(v1.Pod.Status') ∗
  deepown_without_meta c v.

End def.

Section proof.
Context `{hG: !heapGS Σ}.
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
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {
  ObjectMeta' : ObjectMetaV.t;
  Spec' : PodSpecV.t;
}.

Axiom meta_valid: ObjectMetaV.t → Prop.

Definition valid (v: t) : Prop :=
  meta_valid v.(ObjectMeta') ∧
  PodSpecV.valid v.(Spec').

Axiom deepown : v1.PodTemplateSpec.t → t → dfrac → iProp Σ.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End PodTemplateSpecV.

Module ReplicaSetSpecV.
Section def.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {
  Replicas' : option w32;
  MinReadySeconds' : w32;
  (* Selector' : loc; *)
  Template' : PodTemplateSpecV.t;
}.

Axiom valid : t → Prop.

Axiom valid_replicas v :
  ∀ v, valid v →
  ∃ (i: w32), v.(Replicas') = Some i ∧ 0 ≤ sint.Z i.

Axiom valid_template :
  ∀ v, valid v →
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
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {}.
Axiom valid : t → Prop.
Axiom deepown : v1.ReplicaSetStatus.t → t → iProp Σ.

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v.

End def.
End ReplicaSetStatusV.

Module ReplicaSetV.
Section def.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  ObjectMeta' : ObjectMetaV.t;
  Spec' : ReplicaSetSpecV.t;
  Status' : ReplicaSetStatusV.t;
}.

Definition kind : go_string :=
   "ReplicaSet"%go.

Definition meta_key (meta : ObjectMetaV.t) : KKey.t :=
  {|
    KKey.Kind' := kind;
    KKey.Namespace' := meta.(ObjectMetaV.Namespace');
    KKey.Name' := meta.(ObjectMetaV.Name')
  |}.

Definition key (v: t) : KKey.t :=
  meta_key v.(ObjectMeta').

Definition valid (rs: t) : Prop :=
  ObjectMetaV.valid rs.(ObjectMeta') ∧
  ReplicaSetSpecV.valid rs.(Spec') ∧
  ReplicaSetStatusV.valid rs.(Status').

Definition valid_without_meta (rs: t) : Prop :=
  ReplicaSetSpecV.valid rs.(Spec') ∧
  ReplicaSetStatusV.valid rs.(Status').

Definition deepown (c: v1.ReplicaSet.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.ReplicaSet.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷ ObjectMetaV.deepown c.(v1.ReplicaSet.ObjectMeta') v.(ObjectMeta') dq ∗
  "Hdeepown_spec" ∷ ReplicaSetSpecV.deepown c.(v1.ReplicaSet.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ ReplicaSetStatusV.deepown c.(v1.ReplicaSet.Status') v.(Status').

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

Definition typemeta_ptr l: loc :=
  struct_field_ref v1.ReplicaSet.t "TypeMeta" l.

Definition objectmeta_ptr l: loc :=
  struct_field_ref v1.ReplicaSet.t "ObjectMeta" l.

Definition spec_ptr l: loc :=
  struct_field_ref v1.ReplicaSet.t "Spec" l.

Definition status_ptr l: loc :=
  struct_field_ref v1.ReplicaSet.t "Status" l.

Definition update_objectmeta (v: t) (m: ObjectMetaV.t) : t :=
  v <| ObjectMeta' := m |>.

Definition deepown_without_meta (c: v1.ReplicaSet.t) (v: t) dq: iProp Σ :=
  "Hdeepown_spec" ∷ ReplicaSetSpecV.deepown c.(v1.ReplicaSet.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ ReplicaSetStatusV.deepown c.(v1.ReplicaSet.Status') v.(Status').

Definition deepown_l_without_meta l v (dq: dfrac): iProp Σ :=
  ∃ c,
  spec_ptr l ↦{dq} c.(v1.ReplicaSet.Spec') ∗
  status_ptr l ↦{dq} c.(v1.ReplicaSet.Status') ∗
  deepown_without_meta c v dq.

End def.

Section proof.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Lemma deepown_l_split l v dq:
  deepown_l l v dq ⊢
    ⌜ l ≠ null ⌝ ∗
    (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
    ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
    ReplicaSetSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
    ReplicaSetStatusV.deepown_l (status_ptr l) v.(Status') dq.
Proof.
  unfold deepown_l, deepown.
  iIntros "H".
  iDestruct "H" as (c) "[Hl Hdeepown]".
  iDestruct "Hdeepown" as "(%Htypemeta & Hobjectmeta & Hspec & Hstatus)".
  iDestruct (struct_fields_split (V:=v1.ReplicaSet.t) with "Hl") as "[Hfields %Hnot_null]".
  iNamedPrefix "Hfields" "H".
  iSplitR; first done.
  rewrite -Htypemeta.
  iFrame "HTypeMeta".
  iSplitL "HObjectMeta Hobjectmeta".
  { unfold ObjectMetaV.deepown_l, objectmeta_ptr. iFrame. }
  iSplitL "HSpec Hspec".
  { unfold ReplicaSetSpecV.deepown_l, spec_ptr. iFrame. }
  unfold ReplicaSetStatusV.deepown_l, status_ptr. iFrame.
Qed.

Lemma deepown_l_merge l v vm dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) vm dq ∗
  ReplicaSetSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  ReplicaSetStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
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
  iAssert (typed_pointsto_def l (v1.ReplicaSet.mk v_typemeta cm cspec cstatus) dq)
    with "[HTypeMeta HObjectMeta HSpec HStatus]" as "Hfields".
  { simpl. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.ReplicaSet.t)
    l (v1.ReplicaSet.mk v_typemeta cm cspec cstatus) dq Hnot_null with "Hfields") as "Hl".
  iExists (v1.ReplicaSet.mk v_typemeta cm cspec cstatus).
  iSplitL "Hl"; first iExact "Hl".
  iSplitR "Hobjectmeta Hspec Hstatus"; first done.
  simpl. iFrame.
Qed.

Lemma deepown_l_restore l v dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
  ReplicaSetSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  ReplicaSetStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
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
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Inductive t :=
| PodSpec (p : PodSpecV.t)
| ReplicaSetSpec (rs : ReplicaSetSpecV.t).
Axiom valid: t → Prop.
Axiom valid_create: t → Prop.
Axiom valid_update: t → t → Prop.
Axiom valid_update_dec: ∀ s1 s2, Decision (valid_update s1 s2).
Global Existing Instance valid_update_dec.
Axiom defaulted: t → t → Prop.
Axiom created: t → t → Prop. (* input spec → output spec *)
Axiom updated: t → t → Prop. (* old spec → input spec → output spec *)

Definition deepown_l l v dq: iProp Σ :=
  match v with
  | PodSpec p =>
      ∃ c, l ↦{dq} c ∗ PodSpecV.deepown c p
  | ReplicaSetSpec rs =>
      ∃ c, l ↦{dq} c ∗ ReplicaSetSpecV.deepown c rs dq
  end.

End def.
End ObjectSpecV.

Module ObjectStatusV.
Section def.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Inductive t :=
| PodStatus (p : PodStatusV.t)
| ReplicaSetStatus (rs : ReplicaSetStatusV.t).
Axiom valid: t → Prop.
Axiom valid_create: t → Prop.
Axiom valid_update: t → t → Prop.
Axiom valid_update_dec: ∀ s1 s2, Decision (valid_update s1 s2).
Global Existing Instance valid_update_dec.
Axiom created: t → t → Prop. (* input status → output status *)
Axiom updated: t → t → Prop. (* old status → input status → output status *)

Definition deepown_l l v dq: iProp Σ :=
  match v with
  | PodStatus p =>
      ∃ c, l ↦{dq} c ∗ PodStatusV.deepown c p
  | ReplicaSetStatus rs =>
      ∃ c, l ↦{dq} c ∗ ReplicaSetStatusV.deepown c rs
  end.

End def.
End ObjectStatusV.

Module KObjectV.
Section def.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
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

Definition spec o: ObjectSpecV.t :=
  match o with
  | Pod p => ObjectSpecV.PodSpec p.(PodV.Spec')
  | ReplicaSet rs => ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')
  end.

Definition status o: ObjectStatusV.t :=
  match o with
  | Pod p => ObjectStatusV.PodStatus p.(PodV.Status')
  | ReplicaSet rs => ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status')
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

Definition update_objectmeta o m: t :=
  match o with
  | Pod pod => Pod (pod <| PodV.ObjectMeta' := m |>)
  | ReplicaSet rs => ReplicaSet (rs <| ReplicaSetV.ObjectMeta' := m |>)
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

Axiom valid_create: go_string → go_string → t → Prop.

Axiom valid_update_status: go_string → go_string → t → t → Prop.

(* TODO: this definition is incomplete but for now we only care about kind *)
Definition valid_typemeta kind tm : Prop :=
  kind = tm.(v1.TypeMeta.Kind') ∧ valid_kind kind.

Definition valid o : Prop :=
  valid_typemeta (kind o) (typemeta o) ∧
  (* We intentionally don't put valid_resource_version inside ObjectMetaV.valid
     because kview's meta frag needs to be ObjectMetaV.valid and the frag doesn't
     carry the resource version. *)
  valid_resource_version (objectmeta o).(ObjectMetaV.ResourceVersion') ∧
  ObjectMetaV.valid (objectmeta o) ∧
  ObjectSpecV.valid (spec o) ∧
  ObjectStatusV.valid (status o).

Definition valid_nameless_create knd ns o : Prop :=
  knd = kind o ∧
  valid_typemeta (kind o) (typemeta o) ∧
  ObjectMetaV.valid_nameless_create ns (objectmeta o) ∧
  ObjectSpecV.valid_create (spec o) ∧
  ObjectStatusV.valid_create (status o).

Definition valid_named_create knd ns o : Prop :=
  knd = kind o ∧
  valid_typemeta (kind o) (typemeta o) ∧
  ObjectMetaV.valid_named_create ns (objectmeta o) ∧
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

Definition named_created ns o o' : Prop :=
  same_kind o o' ∧ (* A shortcut for proving same kind; it can be derived by conditions below *)
  typemeta o = typemeta o' ∧
  ObjectMetaV.named_created ns (objectmeta o) (objectmeta o') ∧
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
  | Pod _ => i = interface.mk (go.PointerType v1.Pod) #l
  | ReplicaSet _ => i = interface.mk (go.PointerType v1.ReplicaSet) #l
  end.

Definition deepown_i i v dq: iProp Σ :=
  ∃ l, ⌜ valid_interface i l v ⌝ ∗ deepown_l l v dq.

Definition typemeta_ptr l v: loc :=
  match v with
  | Pod _ => struct_field_ref v1.Pod.t "TypeMeta" l
  | ReplicaSet _ => struct_field_ref v1.ReplicaSet.t "TypeMeta" l
  end.

Definition objectmeta_ptr l v: loc :=
  match v with
  | Pod _ => struct_field_ref v1.Pod.t "ObjectMeta" l
  | ReplicaSet _ => struct_field_ref v1.ReplicaSet.t "ObjectMeta" l
  end.

Definition spec_ptr l v: loc :=
  match v with
  | Pod _ => struct_field_ref v1.Pod.t "Spec" l
  | ReplicaSet _ => struct_field_ref v1.ReplicaSet.t "Spec" l
  end.

Definition status_ptr l v: loc :=
  match v with
  | Pod _ => struct_field_ref v1.Pod.t "Status" l
  | ReplicaSet _ => struct_field_ref v1.ReplicaSet.t "Status" l
  end.

End def.

Section proof.
Context `{hG: !heapGS Σ}.
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
  destruct v as [p|rs]; simpl;
    [unfold PodV.deepown_l, PodV.deepown, ObjectSpecV.deepown_l, ObjectStatusV.deepown_l
    |unfold ReplicaSetV.deepown_l, ReplicaSetV.deepown, ObjectSpecV.deepown_l, ObjectStatusV.deepown_l].
  all: iIntros "H";
    iDestruct "H" as (c) "[Hl Hdeepown]";
    iDestruct "Hdeepown" as "(%Htypemeta & Hobjectmeta & Hspec & Hstatus)";
    first
      [iDestruct (struct_fields_split (V:=v1.Pod.t) with "Hl") as "[Hfields %Hnot_null]"
      |iDestruct (struct_fields_split (V:=v1.ReplicaSet.t) with "Hl") as "[Hfields %Hnot_null]"];
    iNamedPrefix "Hfields" "H";
    iSplitR; first done;
    rewrite -Htypemeta;
    iFrame "HTypeMeta";
    iSplitL "HObjectMeta Hobjectmeta";
    [unfold ObjectMetaV.deepown_l; iFrame|];
    iSplitL "HSpec Hspec";
    [iFrame|];
    iFrame.
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
  destruct v as [p|rs]; simpl;
    [destruct p as [p_typemeta p_objectmeta p_spec p_status];
     unfold ObjectSpecV.deepown_l, ObjectStatusV.deepown_l, PodV.deepown_l, PodV.deepown
    |destruct rs as [rs_typemeta rs_objectmeta rs_spec rs_status];
     unfold ObjectSpecV.deepown_l, ObjectStatusV.deepown_l, ReplicaSetV.deepown_l, ReplicaSetV.deepown].
  all: iIntros "(HTypeMeta & Hobjectmeta & Hspec_l & Hstatus_l)".
  all: iDestruct "Hobjectmeta" as (cm) "(HObjectMeta & Hobjectmeta)".
  all: iDestruct "Hspec_l" as (cspec) "(HSpec & Hspec)".
  all: iDestruct "Hstatus_l" as (cstatus) "(HStatus & Hstatus)".
  all: first
    [iAssert (typed_pointsto_def l (v1.Pod.mk p_typemeta cm cspec cstatus) dq)
       with "[HTypeMeta HObjectMeta HSpec HStatus]" as "Hfields";
     [simpl; iFrame|];
     iDestruct (struct_fields_combine (V:=v1.Pod.t)
       l (v1.Pod.mk p_typemeta cm cspec cstatus) dq Hnot_null with "Hfields") as "Hl";
     iExists (v1.Pod.mk p_typemeta cm cspec cstatus)
    |iAssert (typed_pointsto_def l (v1.ReplicaSet.mk rs_typemeta cm cspec cstatus) dq)
       with "[HTypeMeta HObjectMeta HSpec HStatus]" as "Hfields";
     [simpl; iFrame|];
     iDestruct (struct_fields_combine (V:=v1.ReplicaSet.t)
       l (v1.ReplicaSet.mk rs_typemeta cm cspec cstatus) dq Hnot_null with "Hfields") as "Hl";
     iExists (v1.ReplicaSet.mk rs_typemeta cm cspec cstatus)].
  all: iSplitL "Hl"; first iExact "Hl".
  all: iSplitR "Hobjectmeta Hspec Hstatus"; first (iPureIntro; done).
  all: simpl.
  all: iFrame.
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
  iIntros "H".
  iPoseProof (deepown_l_merge l v (objectmeta v) dq Hnot_null with "H") as "H".
  assert (update_objectmeta v (objectmeta v) = v) as ->.
  { destruct v as [p|rs]; [destruct p | destruct rs]; done. }
  iFrame.
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

End proof.
End KObjectV.

Module PreconditionsV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Record t := mk {
  UID' : option types.UID.t;
  ResourceVersion' : option go_string;
}.

Definition deepown (c: v1.Preconditions.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_uid_none" ∷ ⌜ c.(v1.Preconditions.UID') = null ↔ v.(UID') = None⌝ ∗
  "Hdeepown_uid_some" ∷ (match v.(UID') with
  | Some vu => ∃ cu, c.(v1.Preconditions.UID') ↦{dq} cu ∗ ⌜ cu = vu ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_resourceversion_none" ∷ ⌜ c.(v1.Preconditions.ResourceVersion') = null ↔ v.(ResourceVersion') = None⌝ ∗
  "Hdeepown_resourceversion_some" ∷ (match v.(ResourceVersion') with
  | Some vrv => ∃ crv, c.(v1.Preconditions.ResourceVersion') ↦{dq} crv ∗ ⌜ crv = vrv ⌝
  | None => True%I
  end).

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

Definition valid_interface i (l : loc) : Prop :=
  i = interface.mk (go.PointerType v1.Preconditions) #l.

Definition deepown_i i v dq: iProp Σ :=
  ∃ l, ⌜ valid_interface i l ⌝ ∗ deepown_l l v dq.
End def.
End PreconditionsV.

Module DeleteOptionsV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  GracePeriodSeconds' : option w64;
  Preconditions' : option PreconditionsV.t;
  OrphanDependents' : option bool;
  PropagationPolicy' : option go_string;
  (* DryRun' : slice.t; *)
  (* IgnoreStoreReadErrorWithClusterBreakingPotential' : loc; *)
}.

Definition deepown (c: v1.DeleteOptions.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.DeleteOptions.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "%Hdeepown_graceperiodseconds_none" ∷ ⌜ c.(v1.DeleteOptions.GracePeriodSeconds') = null ↔ v.(GracePeriodSeconds') = None⌝ ∗
  "Hdeepown_graceperiodseconds_some" ∷ (match v.(GracePeriodSeconds') with
  | Some vgps => ∃ cgps, c.(v1.DeleteOptions.GracePeriodSeconds') ↦{dq} cgps ∗ ⌜ cgps = vgps ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_preconditions_none" ∷ ⌜ c.(v1.DeleteOptions.Preconditions') = null ↔ v.(Preconditions') = None⌝ ∗
  "Hdeepown_preconditions_some" ∷ (match v.(Preconditions') with
  | Some vp => ∃ cp, c.(v1.DeleteOptions.Preconditions') ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
  | None => True%I
  end) ∗
  "%Hdeepown_orphandependents_none" ∷ ⌜ c.(v1.DeleteOptions.OrphanDependents') = null ↔ v.(OrphanDependents') = None⌝ ∗
  "Hdeepown_orphandependents_some" ∷ (match v.(OrphanDependents') with
  | Some vod => ∃ cod, c.(v1.DeleteOptions.OrphanDependents') ↦{dq} cod ∗ ⌜ cod = vod ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_propagationpolicy_none" ∷ ⌜ c.(v1.DeleteOptions.PropagationPolicy') = null ↔ v.(PropagationPolicy') = None⌝ ∗
  "Hdeepown_propagationpolicy_some" ∷ (match v.(PropagationPolicy') with
  | Some vpp => ∃ cpp, c.(v1.DeleteOptions.PropagationPolicy') ↦{dq} cpp ∗ ⌜ cpp = vpp ⌝
  | None => True%I
  end).

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

Definition valid_interface i (l : loc) : Prop :=
  i = interface.mk (go.PointerType v1.DeleteOptions) #l.

Definition deepown_i i v dq: iProp Σ :=
  ∃ l, ⌜ valid_interface i l ⌝ ∗ deepown_l l v dq.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/validation/validation.go#L157 *)
Axiom valid : t -> Prop.

End def.
End DeleteOptionsV.

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
    | exact Hvalid_meta
    | rewrite KObjectV.spec_update_objectmeta; exact Hvalid_spec
    | rewrite KObjectV.status_update_objectmeta; exact Hvalid_status
    ].
