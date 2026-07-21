From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.api.core Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof Require Export time.
From New.proof.string Require Export prefix_suffix.
From New.proof Require Export struct.
From New.proof Require Import prelude empty_ffi.
Export apimodel.apimodel.
Module KKey := code.kubernetes_model.apimodel.apimodel.KKey.

Definition deepown_list `{hG: heapGS Σ} `{!ffi_semantics _ _}
    {sem : go.Semantics} {C V} `{!ZeroVal C} `{!TypedPointsto (Σ:=Σ) C}
    (c_slice : slice.t) (cs : list C) (vs : list V) (deepown : C → V → iProp Σ) : iProp Σ :=
  c_slice ↦* cs ∗ ([∗ list] c;v ∈ cs;vs, deepown c v).

Module TimeV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Axiom t : Type.
Axiom eq_dec : EqDecision t.
Global Existing Instance eq_dec.
Axiom deepown : v1.Time.t → t → dfrac → iProp Σ.

(* The pure model intentionally leaves Time opaque.  This distinguished value
   is the model of a zero-initialized metav1.Time. *)
Axiom zero : t.
Axiom deepown_zero : ∀ dq, ⊢ deepown (zero_val v1.Time.t) zero dq.
End def.
End TimeV.

Definition byte_dot : w8 := W8 46.  (* ASCII '.' *)
Definition byte_a : w8 := W8 97.  (* ASCII 'a' *)

Definition dns1123_lower_alphanumeric (b : w8) : Prop :=
  (48 ≤ uint.Z b ≤ 57)%Z ∨ (97 ≤ uint.Z b ≤ 122)%Z.

Definition dns1123_label_byte (b : w8) : Prop :=
  dns1123_lower_alphanumeric b ∨ b = byte_dash.

Fixpoint dns1123_label_tail (previous : w8) (suffix : go_string) : Prop :=
  match suffix with
  | [] => dns1123_lower_alphanumeric previous
  | b :: suffix' =>
      dns1123_label_byte b ∧ dns1123_label_tail b suffix'
  end.

Definition dns1123_label_syntax (s : go_string) : Prop :=
  match s with
  | [] => False
  | first :: suffix =>
      dns1123_lower_alphanumeric first ∧
      dns1123_label_tail first suffix
  end.

(* Kubernetes' DNS-1123 label validator applies this ASCII syntax and a
   63-byte length limit. Callers that allow an empty field handle that case
   separately:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/util/validation/validation.go#L176-L202 *)
Definition valid_dns1123_label (s : go_string) : Prop :=
  dns1123_label_syntax s ∧ length s ≤ 63.

Definition dns1123_subdomain_byte (b : w8) : Prop :=
  dns1123_label_byte b ∨ b = byte_dot.

Fixpoint dns1123_subdomain_tail
    (previous : w8) (suffix : go_string) : Prop :=
  match suffix with
  | [] => dns1123_lower_alphanumeric previous
  | b :: suffix' =>
      dns1123_subdomain_byte b ∧
      (previous = byte_dot → dns1123_lower_alphanumeric b) ∧
      (b = byte_dot → dns1123_lower_alphanumeric previous) ∧
      dns1123_subdomain_tail b suffix'
  end.

Definition dns1123_subdomain_syntax (s : go_string) : Prop :=
  match s with
  | [] => False
  | first :: suffix =>
      dns1123_lower_alphanumeric first ∧
      dns1123_subdomain_tail first suffix
  end.

(* Kubernetes limits the complete subdomain to 253 bytes. Its regexp uses the
   label syntax for dot-separated components without separately imposing the
   63-byte standalone-label bound on each component:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/util/validation/validation.go#L205-L231 *)
Definition valid_dns1123_subdomain (s : go_string) : Prop :=
  dns1123_subdomain_syntax s ∧ length s ≤ 253.

Axiom valid_kind: go_string → Prop.

(* Upstream reference: Kubernetes validates CRD `spec.names.kind` by
   lowercasing it and checking it as a DNS-1035 label, which excludes `/`.
   See:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiextensions-apiserver/pkg/apis/apiextensions/validation/validation.go#L762-L763 *)
Axiom valid_kind_slash_free: ∀ kind, valid_kind kind → slash_free kind.

(* Kubernetes selects the name validator from the resource's REST strategy.
   This is a closed-world definition for the four resource kinds represented
   by KObjectV: StatefulSet uses a DNS-1123 label; Pod, ReplicaSet, and PVC use
   a DNS-1123 subdomain. An unknown kind has no valid names in this model.
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L47-L54
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L749-L757
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/core/validation/validation.go#L256-L259
   https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/core/validation/validation.go#L1860-L1863 *)
Definition valid_name (kind name : go_string) : Prop :=
  (kind = "StatefulSet"%go ∧ valid_dns1123_label name) ∨
  ((kind = "Pod"%go ∨
    kind = "ReplicaSet"%go ∨
    kind = "PersistentVolumeClaim"%go) ∧
   valid_dns1123_subdomain name).

(* After resource-specific validation, the API server applies common metadata
   validation with ValidatePathSegmentName for every resource kind:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/create.go#L126-L130
   ValidatePathSegmentName rejects names containing `/`:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/path/name.go#L24-L45 *)
Lemma dns1123_lower_alphanumeric_not_slash b:
  dns1123_lower_alphanumeric b → b ≠ byte_slash.
Proof.
  unfold dns1123_lower_alphanumeric, byte_slash.
  intros [Hdigit | Hlower] ->; word.
Qed.

Lemma dns1123_label_byte_not_slash b:
  dns1123_label_byte b → b ≠ byte_slash.
Proof.
  intros [Halphanumeric | ->].
  - by apply dns1123_lower_alphanumeric_not_slash.
  - unfold byte_dash, byte_slash. word.
Qed.

Lemma dns1123_subdomain_byte_not_slash b:
  dns1123_subdomain_byte b → b ≠ byte_slash.
Proof.
  intros [Hlabel | ->].
  - by apply dns1123_label_byte_not_slash.
  - unfold byte_dot, byte_slash. word.
Qed.

Lemma dns1123_label_tail_slash_free previous suffix:
  dns1123_label_tail previous suffix → slash_free suffix.
Proof.
  unfold slash_free.
  revert previous.
  induction suffix as [|b suffix IH]; intros previous Htail; simpl in *.
  - constructor.
  - destruct Htail as [Hb Htail].
    constructor.
    + by apply dns1123_label_byte_not_slash.
    + by apply (IH b).
Qed.

Lemma dns1123_subdomain_tail_slash_free previous suffix:
  dns1123_subdomain_tail previous suffix → slash_free suffix.
Proof.
  unfold slash_free.
  revert previous.
  induction suffix as [|b suffix IH]; intros previous Htail; simpl in *.
  - constructor.
  - destruct Htail as (Hb & _ & _ & Htail).
    constructor.
    + by apply dns1123_subdomain_byte_not_slash.
    + by apply (IH b).
Qed.

Lemma valid_dns1123_label_slash_free s:
  valid_dns1123_label s → slash_free s.
Proof.
  intros [Hsyntax _].
  destruct s as [|first suffix]; simpl in Hsyntax; [contradiction|].
  destruct Hsyntax as [Hfirst Htail].
  unfold slash_free. constructor.
  - by apply dns1123_lower_alphanumeric_not_slash.
  - exact (dns1123_label_tail_slash_free first suffix Htail).
Qed.

Lemma valid_dns1123_subdomain_slash_free s:
  valid_dns1123_subdomain s → slash_free s.
Proof.
  intros [Hsyntax _].
  destruct s as [|first suffix]; simpl in Hsyntax; [contradiction|].
  destruct Hsyntax as [Hfirst Htail].
  unfold slash_free. constructor.
  - by apply dns1123_lower_alphanumeric_not_slash.
  - exact (dns1123_subdomain_tail_slash_free first suffix Htail).
Qed.

Lemma valid_name_slash_free {kind} name:
  valid_name kind name → slash_free name.
Proof.
  intros [[_ Hlabel] | [_ Hsubdomain]].
  - by apply valid_dns1123_label_slash_free.
  - by apply valid_dns1123_subdomain_slash_free.
Qed.

(* With [prefix = true], Kubernetes' label and subdomain name validators call
   [maskTrailingDash]. If the name has at least two bytes and ends in ["-"],
   that function validates [name[:len(name)-2] + "a"]; otherwise it validates
   the name unchanged:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/generic.go#L36-L49
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/generic.go#L70-L79
   We reported [name[:len(name)-2]] to the Kubernetes community as a likely
   bug:
   https://github.com/kubernetes/kubernetes/issues/137491
   The community acknowledged that the rationale is unclear, but does not plan
   to change the behavior. *)
Definition valid_generate_name kind generate_name : Prop :=
  (∃ prefix char,
    generate_name = prefix ++ [char] ++ "-"%go ∧
    valid_name kind (prefix ++ [byte_a])) ∨
  (¬ ∃ prefix char,
    generate_name = prefix ++ [char] ++ "-"%go) ∧
  valid_name kind generate_name.

(* We often use this lemma to prove that a generate name is valid. *)
Lemma valid_generate_name_of_valid_prefix kind generate_name:
  (∃ prefix,
    generate_name = prefix ++ "-"%go ∧
    prefix ≠ ""%go ∧
    valid_name kind prefix) →
  valid_generate_name kind generate_name.
Proof.
  assert (Ha : dns1123_lower_alphanumeric byte_a).
  { unfold dns1123_lower_alphanumeric, byte_a. right. word. }
  assert (Hlabel_tail : ∀ previous prefix last,
      dns1123_label_tail previous (prefix ++ [last]) →
      dns1123_label_tail previous (prefix ++ [byte_a])).
  { intros previous prefix last. revert previous.
    induction prefix as [|b prefix IH]; intros previous Htail; simpl in *.
    - split.
      + left. exact Ha.
      + exact Ha.
    - destruct Htail as [Hb Htail].
      split; first exact Hb.
      by apply IH. }
  assert (Hsubdomain_tail : ∀ previous prefix last,
      dns1123_subdomain_tail previous (prefix ++ [last]) →
      dns1123_subdomain_tail previous (prefix ++ [byte_a])).
  { intros previous prefix last. revert previous.
    induction prefix as [|b prefix IH]; intros previous Htail; simpl in *.
    - split_and!.
      + left. left. exact Ha.
      + intros _. exact Ha.
      + intros Heq. unfold byte_a, byte_dot in Heq. word.
      + exact Ha.
    - destruct Htail as (Hb & Hprevious & Hb_dot & Htail).
      split_and!; try done.
      by apply IH. }
  assert (Hlabel : ∀ prefix last,
      valid_dns1123_label (prefix ++ [last]) →
      valid_dns1123_label (prefix ++ [byte_a])).
  { intros prefix last [Hsyntax Hlength].
    split.
    - destruct prefix as [|first suffix].
      + simpl. split; exact Ha.
      + simpl in Hsyntax |-.
        destruct Hsyntax as [Hfirst Htail].
        split; first exact Hfirst.
        exact (Hlabel_tail first suffix last Htail).
    - rewrite !app_length /= in Hlength.
      rewrite app_length /=. exact Hlength. }
  assert (Hsubdomain : ∀ prefix last,
      valid_dns1123_subdomain (prefix ++ [last]) →
      valid_dns1123_subdomain (prefix ++ [byte_a])).
  { intros prefix last [Hsyntax Hlength].
    split.
    - destruct prefix as [|first suffix].
      + simpl. split; exact Ha.
      + simpl in Hsyntax |-.
        destruct Hsyntax as [Hfirst Htail].
        split; first exact Hfirst.
        exact (Hsubdomain_tail first suffix last Htail).
    - rewrite !app_length /= in Hlength.
      rewrite app_length /=. exact Hlength. }
  assert (Hvalid_name : ∀ kind prefix last,
      valid_name kind (prefix ++ [last]) →
      valid_name kind (prefix ++ [byte_a])).
  { intros k prefix last [[Hkind Hvalid] | [Hkind Hvalid]].
    - left. split; first exact Hkind. exact (Hlabel prefix last Hvalid).
    - right. split; first exact Hkind. exact (Hsubdomain prefix last Hvalid). }
  assert (Hsnoc : ∀ s : go_string,
      s ≠ ""%go → ∃ prefix last, s = prefix ++ [last]).
  { intros s. induction s as [|b s IH]; intros Hnonempty.
    - contradiction.
    - destruct s as [|b' s].
      + exists [], b. done.
      + destruct (IH ltac:(done)) as (prefix & last & ->).
        exists (b :: prefix), last. done. }
  intros (prefix & -> & Hprefix_nonempty & Hprefix_valid).
  destruct (Hsnoc prefix Hprefix_nonempty) as (prefix' & last & ->).
  left. exists prefix', last. split.
  - by rewrite app_assoc.
  - exact (Hvalid_name kind prefix' last Hprefix_valid).
Qed.

Lemma valid_generate_name_nonempty kind generate_name:
  valid_generate_name kind generate_name →
  generate_name ≠ ""%go.
Proof.
  intros [(prefix & char & -> & _) | [_ Hvalid]].
  - intros Hempty.
    apply app_eq_nil in Hempty as [_ Hdash]. done.
  - intros ->.
    destruct Hvalid as [[_ [Hsyntax _]] | [_ [Hsyntax _]]]; done.
Qed.

(* Kubernetes validates a nonempty namespace with ValidateNamespaceName, which
   is NameIsDNSLabel:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L173-L180
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/generic.go#L60-L63 *)
Definition valid_namespace (ns : go_string) : Prop :=
  valid_dns1123_label ns.

(* Object metadata validation applies ValidateNamespaceName to namespaced
   resources:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L173-L180
   ValidateNamespaceName is NameIsDNSLabel, whose DNS-1123 label regexp
   permits only lowercase alphanumerics and `-`, and therefore excludes `/`:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/generic.go#L44-L63
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/util/validation/validation.go#L176-L202 *)
Lemma valid_namespace_slash_free ns:
  valid_namespace ns → slash_free ns.
Proof.
  unfold valid_namespace.
  apply valid_dns1123_label_slash_free.
Qed.

Axiom valid_uid: go_string → Prop.

(* The generic registry initializes metadata on create with
   FillObjectMetaSystemFields, which assigns uuid.NewUUID():
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L477-L488
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/meta.go#L38-L42
   Kubernetes' NewUUID uses google/uuid's canonical 36-byte string encoding,
   so a system-assigned UID is nonempty:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/util/uuid/uuid.go#L25-L26
   https://github.com/google/uuid/blob/v1.6.0/uuid.go#L244-L268 *)
Axiom valid_uid_non_empty: ∀ uid, valid_uid uid → uid ≠ ""%go.

(* The same canonical UUID encoder emits only hexadecimal digits and `-`, so
   a system-assigned UID cannot contain `/`:
   https://github.com/google/uuid/blob/v1.6.0/uuid.go#L244-L268 *)
Axiom valid_uid_slash_free: ∀ uid, valid_uid uid → slash_free uid.

(* This predicate describes a resource version assigned to a persisted object,
   rather than the empty resource version accepted in some request paths. *)
Axiom valid_resource_version: go_string → Prop.

(* etcd's MVCC revision counter starts at 1 and advances on writes:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/vendor/go.etcd.io/etcd/server/v3/storage/mvcc/kvstore.go#L96-L104
   https://github.com/kubernetes/kubernetes/blob/release-1.34/vendor/go.etcd.io/etcd/server/v3/storage/mvcc/kvstore_txn.go#L182-L188
   Kubernetes passes that positive revision to APIObjectVersioner when decoding
   a stored object, and APIObjectVersioner formats every nonzero revision as a
   base-10 string, so the assigned resource version is nonempty:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/storage/etcd3/decoder.go#L59-L74
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/storage/api_object_versioner.go#L32-L43 *)
Axiom valid_resource_version_non_empty: ∀ rv, valid_resource_version rv → rv ≠ ""%go.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/generic.go#L82 *)
Definition valid_generation (generation: w64) : Prop :=
  (0 <= sint.Z generation)%Z.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/validation/validation.go#L113 *)
Axiom valid_labels: option (gmap go_string go_string) → Prop.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L44 *)
Axiom valid_annotations: option (gmap go_string go_string) → Prop.

(* TODO: this definition is incomplete but for now we only care about kind *)
Definition valid_typemeta kind tm : Prop :=
  kind = tm.(v1.TypeMeta.Kind') ∧ valid_kind kind.

(* The API version expected for each concrete kind represented by [KObjectV]. *)
Definition valid_api_version kind api_version : Prop :=
  ((kind = "Pod"%go ∨ kind = "PersistentVolumeClaim"%go) ∧
    api_version = "v1"%go) ∨
  ((kind = "ReplicaSet"%go ∨ kind = "StatefulSet"%go) ∧
    api_version = "apps/v1"%go).

(* TypeMeta on a create request may omit [kind] and/or [apiVersion]: the JSON
   decoder fills each missing GVK field from the REST endpoint's default GVK.
   An explicitly incompatible kind does not match that typed object and fails
   during decoding/conversion, while an incompatible group/version is rejected
   by the create handler before resource validation:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/runtime/serializer/json/json.go#L115-L127
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/runtime/serializer/json/json.go#L164-L205
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/endpoints/handlers/create.go#L116-L147

   [valid_typemeta] remains the stronger invariant for an object returned by
   Kubernetes. *)
Definition valid_create_typemeta kind tm : Prop :=
  (tm.(v1.TypeMeta.Kind') = ""%go ∨ kind = tm.(v1.TypeMeta.Kind')) ∧
  (tm.(v1.TypeMeta.APIVersion') = ""%go ∨
    valid_api_version kind tm.(v1.TypeMeta.APIVersion')).

Lemma zero_typemeta_valid_create kind :
  valid_create_typemeta kind (zero_val v1.TypeMeta.t).
Proof. split; left; done. Qed.
