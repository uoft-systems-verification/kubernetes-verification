From New.proof Require Import prelude empty_ffi wp_keep.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Import v1.
From New.object_specs Require Export prelude.
From New.proof.kubernetes_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Local Set Default Proof Using "All".

Definition storage_object_normalize (obj : KObjectV.t) : KObjectV.t :=
  KObjectV.update_objectmeta obj
    ((KObjectV.objectmeta obj)
       <| ObjectMetaV.ResourceVersion' := ""%go |>
       <| ObjectMetaV.SelfLink' := ""%go |>).

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

Definition valid_without_resource_version (obj : KObjectV.t) : Prop :=
  ObjectMetaV.valid (KObjectV.kind obj) (KObjectV.objectmeta obj) ∧
  ∀ rv, valid_resource_version rv →
    KObjectV.valid (KObjectV.update_objectmeta obj
      (KObjectV.objectmeta obj <| ObjectMetaV.ResourceVersion' := rv |>)).

(** [update_objects_equiv_except_resource_version] relates two views of the
    same object when only the server-managed resource version may differ.
    Storage establishes this relation between the helper result and the stored
    object. *)
Definition update_objects_equiv_except_resource_version (obj1 obj2 : KObjectV.t) : Prop :=
  KObjectV.same_kind obj1 obj2 ∧
  KObjectV.typemeta obj1 = KObjectV.typemeta obj2 ∧
  ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta obj1) (KObjectV.objectmeta obj2) ∧
  KObjectV.spec obj1 = KObjectV.spec obj2 ∧
  KObjectV.status obj1 = KObjectV.status obj2.

(** [update_prepared_for_helper] describes the object that the update caller
    passes to an update or status-update validation/defaulting helper. [input]
    is the object submitted to the request. The caller fills an empty namespace
    with [namespace]. It fills an omitted resource version from [old], while a
    nonempty submitted resource version must already equal the old one. Schema
    defaulting and the remaining normalization happen inside the helper, not in
    this preparation relation. *)
Definition update_prepared_for_helper
    (namespace : go_string) (old input helper_input : KObjectV.t) : Prop :=
  ((KObjectV.objectmeta input).(ObjectMetaV.Namespace') = ""%go ∨
   (KObjectV.objectmeta input).(ObjectMetaV.Namespace') = namespace) ∧
  ((KObjectV.objectmeta input).(ObjectMetaV.ResourceVersion') = ""%go ∨
   (KObjectV.objectmeta input).(ObjectMetaV.ResourceVersion') =
     (KObjectV.objectmeta old).(ObjectMetaV.ResourceVersion')) ∧
  KObjectV.key old = KObjectV.key helper_input ∧
  helper_input =
    KObjectV.update_objectmeta input
      ((KObjectV.objectmeta input) <| ObjectMetaV.Namespace' := namespace |>
                                   <| ObjectMetaV.ResourceVersion' :=
                                        (KObjectV.objectmeta old).(ObjectMetaV.ResourceVersion') |>).

(** This is the single trusted semantic contract for a successful ordinary
    update-helper call. [old] and [helper_input] are the objects passed to the
    helper, and [helper_result] is the mutated input object after it returns.

    The first two conjuncts expose facts needed by callers that separately own
    status or rely on an unchanged spec. The remaining conjuncts connect the
    helper result to the public end-to-end update relation and invariants. *)
Definition applyValidationAndDefaultingOnUpdate_updated
    (namespace : go_string) (old helper_input helper_result : KObjectV.t) : Prop :=
  KObjectV.status helper_result = KObjectV.status old ∧
  (KObjectV.spec helper_input = KObjectV.spec old →
    KObjectV.spec helper_result = KObjectV.spec old) ∧
  (∀ input stored,
    update_prepared_for_helper namespace old input helper_input →
    update_objects_equiv_except_resource_version helper_result stored →
    KObjectV.updated (KObjectV.spec old) input stored) ∧
  (KObjectV.valid old →
    valid_typemeta (KObjectV.kind helper_input) (KObjectV.typemeta helper_input) →
    KObjectV.valid helper_result) ∧
  (KObjectV.extra_valid old → KObjectV.extra_valid helper_result).

(** This is the single trusted semantic contract for a successful status-update
    helper call. [old] and [helper_input] are the objects passed to the helper,
    and [helper_result] is the mutated input object after it returns. *)
Definition applyValidationAndDefaultingOnStatusUpdate_updated
    (namespace : go_string) (old helper_input helper_result : KObjectV.t) : Prop :=
  (∀ request_kind input stored,
    KObjectV.valid old →
    KObjectV.valid_status_update request_kind namespace
      (KObjectV.objectmeta old) (KObjectV.status old) input →
    update_prepared_for_helper namespace old input helper_input →
    update_objects_equiv_except_resource_version helper_result stored →
    KObjectV.status_updated input stored ∧
    KObjectV.spec stored = KObjectV.spec old) ∧
  (KObjectV.valid old →
    valid_typemeta (KObjectV.kind helper_input) (KObjectV.typemeta helper_input) →
    KObjectV.valid helper_result).

Definition delete_tx_preconditions_with_rv (options : DeleteOptionsV.t) (rv : go_string) :
    PreconditionsV.t :=
  match options.(DeleteOptionsV.Preconditions') with
  | None => {|
      PreconditionsV.UID' := None;
      PreconditionsV.ResourceVersion' := Some rv;
    |}
  | Some preconditions =>
      preconditions <| PreconditionsV.ResourceVersion' := Some rv |>
  end.

Definition delete_tx_options_with_rv (options : DeleteOptionsV.t) (rv : go_string) :
    DeleteOptionsV.t :=
  options <| DeleteOptionsV.Preconditions' :=
    Some (delete_tx_preconditions_with_rv options rv) |>.

#[global] Instance KKey_into_val_inj : go.IntoValInj KKey.t.
Proof.
  constructor. intros k1 k2 Heq.
  assert (k1.(KKey.Kind') = k2.(KKey.Kind')) as Hkind.
  {
    pose proof (go.tagged_steps under
      (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Kind"%go) (#k1)
      (#k1.(KKey.Kind')) _) as Hstep1.
    pose proof (go.tagged_steps under
      (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Kind"%go) (#k2)
      (#k2.(KKey.Kind')) _) as Hstep2.
    assert (is_go_step_pure (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Kind"%go)
      (#k1) (#k1.(KKey.Kind'))) as Hpure.
    { rewrite (go.is_go_step_pure_det (IsGoStepPureDet:=Hstep1)). done. }
    rewrite Heq in Hpure.
    rewrite (go.is_go_step_pure_det (IsGoStepPureDet:=Hstep2)) in Hpure.
    symmetry in Hpure.
    injection Hpure as Hpure.
    destruct go.into_val_inj_string as [Hinj].
    specialize (Hinj k1.(KKey.Kind') k2.(KKey.Kind')).
    exact (Hinj Hpure).
  }
  assert (k1.(KKey.Name') = k2.(KKey.Name')) as Hname.
  {
    pose proof (go.tagged_steps under
      (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Name"%go) (#k1)
      (#k1.(KKey.Name')) _) as Hstep1.
    pose proof (go.tagged_steps under
      (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Name"%go) (#k2)
      (#k2.(KKey.Name')) _) as Hstep2.
    assert (is_go_step_pure (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Name"%go)
      (#k1) (#k1.(KKey.Name'))) as Hpure.
    { rewrite (go.is_go_step_pure_det (IsGoStepPureDet:=Hstep1)). done. }
    rewrite Heq in Hpure.
    rewrite (go.is_go_step_pure_det (IsGoStepPureDet:=Hstep2)) in Hpure.
    symmetry in Hpure.
    injection Hpure as Hpure.
    destruct go.into_val_inj_string as [Hinj].
    specialize (Hinj k1.(KKey.Name') k2.(KKey.Name')).
    exact (Hinj Hpure).
  }
  assert (k1.(KKey.Namespace') = k2.(KKey.Namespace')) as Hnamespace.
  {
    pose proof (go.tagged_steps under
      (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Namespace"%go) (#k1)
      (#k1.(KKey.Namespace')) _) as Hstep1.
    pose proof (go.tagged_steps under
      (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Namespace"%go) (#k2)
      (#k2.(KKey.Namespace')) _) as Hstep2.
    assert (is_go_step_pure (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Namespace"%go)
      (#k1) (#k1.(KKey.Namespace'))) as Hpure.
    { rewrite (go.is_go_step_pure_det (IsGoStepPureDet:=Hstep1)). done. }
    rewrite Heq in Hpure.
    rewrite (go.is_go_step_pure_det (IsGoStepPureDet:=Hstep2)) in Hpure.
    symmetry in Hpure.
    injection Hpure as Hpure.
    destruct go.into_val_inj_string as [Hinj].
    specialize (Hinj k1.(KKey.Namespace') k2.(KKey.Namespace')).
    exact (Hinj Hpure).
  }
  destruct k1, k2; simpl in *; congruence.
Qed.

#[global] Instance KKey_safe_map_key key :
  SafeMapKey (K:=KKey.t) apimodel.KKey key.
Proof.
  constructor. iIntros (stk E Ψ) "HΨ". wp_auto_keep.
  replace (bool_decide (apimodel.KKey.Kind' key = apimodel.KKey.Kind' key)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto_keep.
  replace (bool_decide (apimodel.KKey.Name' key = apimodel.KKey.Name' key)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto_keep. done.
Qed.

Lemma objectmeta_update_objectmeta obj m :
  KObjectV.objectmeta (KObjectV.update_objectmeta obj m) = m.
Proof. destruct obj; done. Qed.

Lemma storage_object_normalize_update_objectmeta_deletionTimestamp obj m :
  storage_object_normalize (KObjectV.update_objectmeta obj m) =
  storage_object_normalize obj →
  m.(ObjectMetaV.DeletionTimestamp') =
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp').
Proof.
  destruct obj as [p|rs|pvc|sts|d].
  - destruct p as [pt pm ps pst]. destruct pm. destruct m. simpl.
    intros H. inversion H. done.
  - destruct rs as [rt rm rspec rstatus]. destruct rm. destruct m. simpl.
    intros H. inversion H. done.
  - destruct pvc as [pvct pvcm pvcs pvcst]. destruct pvcm. destruct m. simpl.
    intros H. inversion H. done.
  - destruct sts as [stst stsm stss stsst]. destruct stsm. destruct m. simpl.
    intros H. inversion H. done.
  - destruct d as [dt dm ds dst]. destruct dm. destruct m. simpl.
    intros H. inversion H. done.
Qed.

Lemma objectmeta_updated_of_valid_simple_update_without_rv_selflink_eq m_old m_input m_updated :
  ObjectMetaV.valid_simple_update m_old m_input →
  ObjectMetaV.updated m_input m_updated →
  (m_updated <| ObjectMetaV.ResourceVersion' := ""%go |> <| ObjectMetaV.SelfLink' := ""%go |>) =
  (m_old <| ObjectMetaV.ResourceVersion' := ""%go |> <| ObjectMetaV.SelfLink' := ""%go |>) →
  ObjectMetaV.updated m_input m_old.
Proof.
  rewrite /ObjectMetaV.valid_simple_update /ObjectMetaV.updated.
  destruct m_old, m_input, m_updated; simpl.
  intros Hvalid Hupdated Hnormalized. inversion Hnormalized; subst.
  simpl in *. intuition congruence.
Qed.

Lemma storage_object_normalize_objectmeta_updated obj_old obj_input obj_updated :
  storage_object_normalize obj_updated = storage_object_normalize obj_old →
  ObjectMetaV.valid_simple_update
    (KObjectV.objectmeta obj_old)
    (KObjectV.objectmeta obj_input) →
  ObjectMetaV.updated
    (KObjectV.objectmeta obj_input)
    (KObjectV.objectmeta obj_updated) →
  ObjectMetaV.updated
    (KObjectV.objectmeta obj_input)
    (KObjectV.objectmeta obj_old).
Proof.
  intros Hstorage Hvalid Hupdated.
  eapply objectmeta_updated_of_valid_simple_update_without_rv_selflink_eq; [done|done|].
  assert (KObjectV.objectmeta (storage_object_normalize obj_updated) =
          KObjectV.objectmeta (storage_object_normalize obj_old)) as Hnormalized.
  { rewrite Hstorage. done. }
  rewrite /storage_object_normalize !objectmeta_update_objectmeta in Hnormalized.
  exact Hnormalized.
Qed.

Lemma storage_object_normalize_spec_eq obj1 obj2 :
  storage_object_normalize obj1 = storage_object_normalize obj2 →
  KObjectV.spec obj1 = KObjectV.spec obj2.
Proof.
  intros Hstorage.
  assert (KObjectV.spec (storage_object_normalize obj1) =
          KObjectV.spec (storage_object_normalize obj2)) as Hspec_eq.
  { rewrite Hstorage. done. }
  rewrite /storage_object_normalize !KObjectV.spec_update_objectmeta in Hspec_eq.
  exact Hspec_eq.
Qed.
End proof.
