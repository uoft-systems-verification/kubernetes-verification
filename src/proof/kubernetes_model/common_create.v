From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common admitted.
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
          end
        | match goal with
          | H : DeploymentStatusV.created ?input ?helper_result
              |- DeploymentStatusV.created ?input ?stored =>
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

End proof.
