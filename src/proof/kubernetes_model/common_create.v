From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common.
From New.proof.k8s_io.apiserver.pkg.registry Require Export rest.

(** Important modeling assumption: we currently ignore fields that are not
    represented by the Kubernetes view types. In particular, we assume that
    validation of those Go fields always succeeds. We will gradually add those
    fields to the view types and verify their validation. Proofs using the
    specification of [applyValidationAndDefaulting] do not need to own or
    reason about the unmodeled fields.

    TODO: [KObjectV.deepown_l] must existentially own all reachable Go fields,
    including unmodeled fields, so helper calls cannot mutate memory outside
    their separation-logic footprint. *)

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__generateNewUIDAndUpdate l used_uid_l (used_uid : gmap types.UID.t unit) :
  {{{ is_pkg_init apimodel ∗
      l.[(apimodel.State.t), "usedUID"] ↦ used_uid_l ∗
      used_uid_l ↦$ used_uid
  }}}
    l @! (go.PointerType apimodel.State) @! "generateNewUIDAndUpdate" #()
  {{{ uid, RET #uid;
      ⌜ used_uid !! uid = None ⌝ ∗
      ⌜ valid_uid uid ⌝ ∗
      l.[(apimodel.State.t), "usedUID"] ↦ used_uid_l ∗
      used_uid_l ↦$ <[uid:=()]> used_uid
  }}}.
Proof.
Admitted.

Lemma wp_State__generateNewName l m_ptr kind namespace generate_name (phys_state : gmap KKey.t interface.t):
  {{{ is_pkg_init apimodel ∗
      ⌜ valid_generate_name kind generate_name ⌝ ∗
      ⌜ length generate_name ≤ 58 ⌝ ∗
      l.[(apimodel.State.t), "m"] ↦ m_ptr ∗
      m_ptr ↦$ phys_state
  }}}
    l @! (go.PointerType apimodel.State) @! "generateNewName" #kind #namespace #generate_name
  {{{ (new_name: go_string), RET #new_name;
      ⌜ new_name ≠ ""%go ⌝ ∗
      ⌜ valid_name kind new_name ⌝ ∗
      ⌜ phys_state !! {| KKey.Kind' := kind; KKey.Namespace' := namespace; KKey.Name' := new_name;|} = None ⌝ ∗
      ⌜ ∀ kind namespace,
          ¬ reserved_key_pred {| KKey.Kind' := kind;
                             KKey.Namespace' := namespace;
                             KKey.Name' := new_name |} ⌝ ∗
      l.[(apimodel.State.t), "m"] ↦ m_ptr ∗
      m_ptr ↦$ phys_state
  }}}.
Proof.
Admitted.

(** [create_prepared_for_helper] describes the private object copy passed to
    [applyValidationAndDefaulting]. [State.create] is below request decoding, so
    it preserves TypeMeta. It wipes system metadata, fills the request
    namespace, generates a creation timestamp and UID, and generates a name
    when the request omits one. *)
Definition create_prepared_for_helper
    (namespace name : go_string) (input helper_input : KObjectV.t) : Prop :=
  let input_meta := KObjectV.objectmeta input in
  let helper_meta := KObjectV.objectmeta helper_input in
  name = helper_meta.(ObjectMetaV.Name') ∧
  name ≠ ""%go ∧
  valid_name (KObjectV.kind input) name ∧
  valid_uid helper_meta.(ObjectMetaV.UID') ∧
  (if decide (input_meta.(ObjectMetaV.Name') = ""%go)
   then input_meta.(ObjectMetaV.GenerateName') ≠ ""%go
   else name = input_meta.(ObjectMetaV.Name')) ∧
  helper_input =
    KObjectV.update_objectmeta input
      (input_meta <| ObjectMetaV.Name' := name |>
                  <| ObjectMetaV.Namespace' := namespace |>
                  <| ObjectMetaV.SelfLink' := ""%go |>
                  <| ObjectMetaV.UID' := helper_meta.(ObjectMetaV.UID') |>
                  <| ObjectMetaV.CreationTimestamp' := helper_meta.(ObjectMetaV.CreationTimestamp') |>
                  <| ObjectMetaV.DeletionTimestamp' := None |>
                  <| ObjectMetaV.DeletionGracePeriodSeconds' := None |>).

(** [create_stored_from_helper_result] describes the mutation after the helper
    succeeds. Generic metadata validation is read-only. Storage then assigns a
    fresh resource version, stores the object, and returns a deep copy. *)
Definition create_stored_from_helper_result
    (helper_result stored : KObjectV.t) : Prop :=
  KObjectV.same_kind helper_result stored ∧
  KObjectV.typemeta helper_result = KObjectV.typemeta stored ∧
  ObjectMetaV.equiv_except_resource_version
    (KObjectV.objectmeta helper_result) (KObjectV.objectmeta stored) ∧
  KObjectV.spec helper_result = KObjectV.spec stored ∧
  KObjectV.status helper_result = KObjectV.status stored ∧
  valid_resource_version (KObjectV.objectmeta stored).(ObjectMetaV.ResourceVersion').

Definition valid_without_resource_version (obj : KObjectV.t) : Prop :=
  valid_typemeta (KObjectV.kind obj) (KObjectV.typemeta obj) ∧
  ObjectMetaV.valid (KObjectV.kind obj) (KObjectV.objectmeta obj) ∧
  ObjectSpecV.valid (KObjectV.spec obj) ∧
  ObjectStatusV.valid (KObjectV.status obj).

(** This is the single trusted semantic contract for a successful helper
    call. *)
Definition create_helper_result
    (namespace : go_string) (input helper_input helper_result : KObjectV.t) : Prop :=
  KObjectV.created namespace input helper_result ∧
  valid_without_resource_version helper_result ∧
  (KObjectV.objectmeta helper_result).(ObjectMetaV.Name') =
    (KObjectV.objectmeta helper_input).(ObjectMetaV.Name') ∧
  (KObjectV.objectmeta helper_result).(ObjectMetaV.UID') =
    (KObjectV.objectmeta helper_input).(ObjectMetaV.UID').

Lemma create_stored_from_helper_result_created namespace input helper_result stored :
  KObjectV.created namespace input helper_result →
  create_stored_from_helper_result helper_result stored →
  KObjectV.created namespace input stored.
Proof.
  intros Hcreated Hstored.
  destruct input; destruct helper_result; simpl in Hcreated; try contradiction.
  all: destruct stored; simpl in Hstored |- *; try contradiction.
  all: destruct Hcreated as (Htypemeta & Hmeta & Hgeneration & Hspec & Hstatus).
  all: destruct Hstored as (Hsame & Htypemeta_eq & Hmeta_eq & Hspec_eq & Hstatus_eq & _);
    try contradiction.
  all: cbn [KObjectV.typemeta] in Htypemeta_eq.
  all: cbn [KObjectV.objectmeta] in Hmeta_eq.
  all: cbn [KObjectV.spec] in Hspec_eq.
  all: cbn [KObjectV.status] in Hstatus_eq.
  all: refine (conj _ (conj _ (conj _ (conj _ _))));
    [ rewrite -Htypemeta_eq; exact Htypemeta
    | match goal with
      | Hcreated : ObjectMetaV.created _ _ ?helper_meta,
        Hequiv : ObjectMetaV.equiv_except_resource_version ?helper_meta ?stored_meta
          |- ObjectMetaV.created _ _ ?stored_meta =>
          rewrite /ObjectMetaV.equiv_except_resource_version
            /ObjectMetaV.without_resource_version in Hequiv;
          destruct helper_meta, stored_meta; simpl in *;
          inversion Hequiv; subst; exact Hcreated
      end
    | pose proof Hmeta_eq as Hmeta_fields;
      rewrite /ObjectMetaV.equiv_except_resource_version
        /ObjectMetaV.without_resource_version in Hmeta_fields;
      pose proof (f_equal ObjectMetaV.Generation' Hmeta_fields) as Hgeneration_eq;
      simpl in Hgeneration_eq; rewrite -Hgeneration_eq; exact Hgeneration
    | injection Hspec_eq as Hspec_field_eq;
      rewrite -Hspec_field_eq; exact Hspec
    | first
        [ exact Hstatus
        | injection Hstatus_eq as Hstatus_field_eq;
          rewrite -Hstatus_field_eq; exact Hstatus
        | match goal with
          | H : ReplicaSetStatusV.created ?input ?helper_result
              |- ReplicaSetStatusV.created ?input ?stored =>
              destruct helper_result; destruct stored; exact H
          end ] ].
Qed.

Lemma create_stored_from_helper_result_valid helper_result stored :
  valid_without_resource_version helper_result →
  create_stored_from_helper_result helper_result stored →
  KObjectV.valid stored.
Proof.
  intros Hvalid Hstored.
  destruct Hvalid as (Htypemeta & Hmeta & Hspec & Hstatus).
  destruct Hstored as (Hkind & Htypemeta_eq & Hmeta_eq & Hspec_eq & Hstatus_eq & Hrv).
  assert (KObjectV.kind helper_result = KObjectV.kind stored) as Hkind_eq.
  { destruct helper_result, stored; simpl in Hkind |- *; try contradiction; done. }
  rewrite /KObjectV.valid.
  split_and!.
  - rewrite -Hkind_eq -Htypemeta_eq. exact Htypemeta.
  - exact Hrv.
  - rewrite -Hkind_eq.
    pose proof Hmeta_eq as Hmeta_fields.
    rewrite /ObjectMetaV.equiv_except_resource_version
      /ObjectMetaV.without_resource_version in Hmeta_fields.
    pose proof (f_equal ObjectMetaV.GenerateName' Hmeta_fields) as Hgenerate_name.
    pose proof (f_equal ObjectMetaV.Name' Hmeta_fields) as Hname.
    pose proof (f_equal ObjectMetaV.Namespace' Hmeta_fields) as Hnamespace.
    pose proof (f_equal ObjectMetaV.UID' Hmeta_fields) as Huid.
    pose proof (f_equal ObjectMetaV.Labels' Hmeta_fields) as Hlabels.
    pose proof (f_equal ObjectMetaV.Annotations' Hmeta_fields) as Hannotations.
    pose proof (f_equal ObjectMetaV.OwnerReferences' Hmeta_fields) as Howners.
    pose proof (f_equal ObjectMetaV.Finalizers' Hmeta_fields) as Hfinalizers.
    pose proof (f_equal ObjectMetaV.ManagedFields' Hmeta_fields) as Hmanaged_fields.
    pose proof (f_equal ObjectMetaV.SelfLink' Hmeta_fields) as Hself_link.
    simpl in Hgenerate_name, Hname, Hnamespace, Huid, Hlabels, Hannotations,
      Howners, Hfinalizers, Hmanaged_fields, Hself_link.
    unfold ObjectMetaV.valid in Hmeta |- *.
    rewrite -Hgenerate_name -Hname -Hnamespace -Huid -Hlabels -Hannotations
      -Howners -Hfinalizers -Hmanaged_fields -Hself_link. exact Hmeta.
  - rewrite -Hspec_eq. exact Hspec.
  - rewrite -Hstatus_eq. exact Hstatus.
Qed.

(** Strong contract for a create satisfying the modeled sufficient validity
    condition. [input] is the submitted create object and [helper_input] is the
    prepared private copy passed to the helper. Under the modeling assumption
    above, validation of unmodeled fields adds no precondition. *)
Lemma wp_applyValidationAndDefaulting_ok
    i l helper_input (request_kind namespace name : go_string) input :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface i l helper_input ⌝ ∗
      ⌜ KObjectV.valid_create request_kind namespace input ⌝ ∗
      ⌜ create_prepared_for_helper namespace name input helper_input ⌝ ∗
      KObjectV.deepown_l l helper_input 1
  }}}
    @! apimodel.applyValidationAndDefaulting #(interface.ok i) #name
  {{{ helper_result, RET #interface.nil;
      KObjectV.deepown_l l helper_result 1 ∗
      ⌜ KObjectV.valid_interface i l helper_result ⌝ ∗
      ⌜ create_helper_result namespace input helper_input helper_result ⌝
  }}}.
Proof. Admitted.

End proof.
