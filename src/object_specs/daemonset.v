From New.proof Require Import prelude empty_ffi.
From New.generatedviews Require Export daemonset.
From New.proof.string Require Import decimal.
From New.object_specs Require Export labelselector pod.
From New.object_specs Require Import top_level.
From New.proof Require Import struct.

Local Transparent ObjectMetaView.ObjectMetaV.deepown ObjectMetaV.deepown.
Local Transparent DaemonSetView.DaemonSetSpecV.deepown DaemonSetView.DaemonSetStatusV.deepown.

Module DaemonSetSpecV.
Include DaemonSetView.DaemonSetSpecV.

(* MinReadySeconds must be nonnegative. *)
Definition min_ready_seconds_valid (spec : t) : Prop :=
  0 ≤ sint.Z spec.(MinReadySeconds').

(* RevisionHistoryLimit may be omitted; a provided value must be nonnegative. *)
Definition revision_history_limit_valid (spec : t) : Prop :=
  match spec.(RevisionHistoryLimit') with
  | None => True
  | Some n => 0 ≤ sint.Z n
  end.

(* No value -- add 10, value provided -- preserve*)
Definition revision_history_limit_defaulted
    (input stored : t) : Prop :=
  stored.(RevisionHistoryLimit') =
    Some (match input.(RevisionHistoryLimit') with
          | None => W32 10
          | Some n => n
          end).

(* No type provided -- default RollingUpdate, preserve provided type *)
Definition default_update_strategy_type
    (strategy_type : go_string) : go_string :=
  if decide (strategy_type = ""%go)
  then "RollingUpdate"%go
  else strategy_type.

(* Relate the input and resulting strategy-type fields. *)
Definition update_strategy_type_defaulted
    (input stored : t) : Prop :=
  stored.(UpdateStrategy').(DaemonSetView.DaemonSetUpdateStrategyV.Type') =
    default_update_strategy_type
      input.(UpdateStrategy').(DaemonSetView.DaemonSetUpdateStrategyV.Type').

(* Pure value corresponding to intstr.FromInt32(n). *)
Definition int_or_string_from_int32
    (n : w32) : PodView.IntOrStringV.t :=
  {|
    intstr.IntOrString.Type' := W64 0;
    intstr.IntOrString.IntVal' := n;
    intstr.IntOrString.StrVal' := ""%go;
  |}.

(* No MaxUnavailable -- default 1, preserve the provided value *)
Definition default_max_unavailable
    (input : option PodView.IntOrStringV.t)
    : option PodView.IntOrStringV.t :=
  match input with
  | None => Some (int_or_string_from_int32 (W32 1))
  | Some value => Some value
  end.

(* No MaxSurge -- default 0, preserve the provided value *)
Definition default_max_surge
    (input : option PodView.IntOrStringV.t)
    : option PodView.IntOrStringV.t :=
  match input with
  | None => Some (int_or_string_from_int32 (W32 0))
  | Some value => Some value
  end.

(* Fill omitted rolling-update parameters. *)
Definition default_rolling_update
    (input : option DaemonSetView.RollingUpdateDaemonSetV.t)
    : DaemonSetView.RollingUpdateDaemonSetV.t :=
  let rolling :=
    match input with
    | None => DaemonSetView.RollingUpdateDaemonSetV.zero
    | Some value => value
    end in
    {|
        DaemonSetView.RollingUpdateDaemonSetV.MaxUnavailable' :=
          default_max_unavailable
            rolling.(DaemonSetView.RollingUpdateDaemonSetV.MaxUnavailable');
        DaemonSetView.RollingUpdateDaemonSetV.MaxSurge' :=
          default_max_surge
            rolling.(DaemonSetView.RollingUpdateDaemonSetV.MaxSurge');
    |}.

(* Round-trip through the internal apps type. A missing RollingUpdate stays
   missing, but its parameters are non-pointer IntOrString values internally:
   nil becomes integer zero, and conversion back allocates a pointer.
   See pkg/apis/apps/v1/zz_generated.conversion.go and
   staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/conversion.go. *)
Definition converted_rolling_update
    (input : option DaemonSetView.RollingUpdateDaemonSetV.t)
    : option DaemonSetView.RollingUpdateDaemonSetV.t :=
  match input with
  | None => None
  | Some rolling => Some {|
      DaemonSetView.RollingUpdateDaemonSetV.MaxUnavailable' :=
        Some (default (int_or_string_from_int32 (W32 0))
          rolling.(DaemonSetView.RollingUpdateDaemonSetV.MaxUnavailable'));
      DaemonSetView.RollingUpdateDaemonSetV.MaxSurge' :=
        Some (default (int_or_string_from_int32 (W32 0))
          rolling.(DaemonSetView.RollingUpdateDaemonSetV.MaxSurge'));
    |}
  end.

(* Relate RollingUpdate fields after defaulting and version conversion.
   RollingUpdate defaults already make both parameter pointers non-nil;
   other strategies still undergo conversion if the structure is present. *)
Definition rolling_update_normalized
    (input stored : t) : Prop :=
  let input_strategy := input.(UpdateStrategy') in
  let strategy_type :=
    default_update_strategy_type
      input_strategy.(DaemonSetView.DaemonSetUpdateStrategyV.Type') in
  stored.(UpdateStrategy').(DaemonSetView.DaemonSetUpdateStrategyV.RollingUpdate') =
    if decide (strategy_type = "RollingUpdate"%go)
    then Some (default_rolling_update
      input_strategy.(DaemonSetView.DaemonSetUpdateStrategyV.RollingUpdate'))
    else converted_rolling_update input_strategy.(DaemonSetView.DaemonSetUpdateStrategyV.RollingUpdate').

(* Defaulting and conversion relation for the complete update strategy. *)
Definition update_strategy_normalized
    (input stored : t) : Prop :=
  update_strategy_type_defaulted input stored ∧
  rolling_update_normalized input stored.

(* The integer branch of ValidatePositiveIntOrPercent. *)
Definition int_or_string_integer_valid
    (value : PodView.IntOrStringV.t) : Prop :=
  value.(intstr.IntOrString.Type') = W64 0 ∧
  0 ≤ sint.Z value.(intstr.IntOrString.IntVal').

(* Parse a nonempty decimal digit sequence followed by '%'. *)
Definition parse_percent_string (s : go_string) : option nat :=
  match reverse s with
  | [] => None
  | last_byte :: reversed_digits =>
      if decide (last_byte = W8 37)
      then parse_decimal_string (reverse reversed_digits)
      else None
  end.

(* String branch of ValidatePositiveIntOrPercent: syntax only. *)
Definition int_or_string_percent_valid
    (value : PodView.IntOrStringV.t) : Prop :=
  value.(intstr.IntOrString.Type') = W64 1 ∧
  ∃ n, parse_percent_string value.(intstr.IntOrString.StrVal') = Some n.

Definition positive_int_percent_valid
    (value : PodView.IntOrStringV.t) : Prop :=
    int_or_string_integer_valid value ∨
    int_or_string_percent_valid value.

(* Validate one parameter, including the percentage bound, n% <= 100%. *)
Definition daemonset_int_or_percent_valid
    (value : PodView.IntOrStringV.t) : Prop :=
  positive_int_percent_valid value ∧
  (if decide (value.(intstr.IntOrString.Type') = W64 1)
    then match parse_percent_string value.(intstr.IntOrString.StrVal') with
        | Some n => (n ≤ 100)%nat
        | None => False
        end
    else True).

(* Test for zero; validity is checked separately. *)
Definition int_or_percent_is_zero
    (value : PodView.IntOrStringV.t) : Prop :=
  if decide (value.(intstr.IntOrString.Type') = W64 0)
  then value.(intstr.IntOrString.IntVal') = W32 0
  else if decide (value.(intstr.IntOrString.Type') = W64 1)
       then parse_percent_string value.(intstr.IntOrString.StrVal') = Some (0%nat)
       else False.

(* Validate RollingUpdate parameters after defaulting. *)
(* both are valid, only one can be zero*)
Definition rolling_update_valid
    (rolling : DaemonSetView.RollingUpdateDaemonSetV.t) : Prop :=
  match rolling.(DaemonSetView.RollingUpdateDaemonSetV.MaxUnavailable'),
        rolling.(DaemonSetView.RollingUpdateDaemonSetV.MaxSurge') with
  | Some unavailable, Some surge =>
      daemonset_int_or_percent_valid unavailable ∧
      daemonset_int_or_percent_valid surge ∧
      ((int_or_percent_is_zero unavailable ∧ ¬ int_or_percent_is_zero surge) ∨
       (¬ int_or_percent_is_zero unavailable ∧ int_or_percent_is_zero surge))
  | _, _ => False
  end.

(* Validate the update strategy after defaulting. *)
Definition update_strategy_valid
    (strategy : DaemonSetView.DaemonSetUpdateStrategyV.t) : Prop :=
  let strategy_type := strategy.(DaemonSetView.DaemonSetUpdateStrategyV.Type') in
  if decide (strategy_type = "OnDelete"%go)
  then True
  else if decide (strategy_type = "RollingUpdate"%go)
       then match strategy.(DaemonSetView.DaemonSetUpdateStrategyV.RollingUpdate') with
            | Some rolling => rolling_update_valid rolling
            | None => False
            end
       else False.

(* Creation path for the five fields of the external apps/v1 DaemonSetSpec.
   Pod-template defaults, conversion, feature-field preparation and validation
   reuse the existing PodTemplateSpecV / PodAPI contracts. Those imported
   routines remain a trusted boundary in the fixed model configuration.
   Internal Spec.TemplateGeneration is carried through an outer metadata
   annotation, so it belongs to the later whole-object specification. *)

Definition selector_valid (spec : t) : Prop :=
  match spec.(Selector') with
  | None => False
  | Some selector =>
      LabelSelectorV.valid selector ∧
      ¬ LabelSelectorV.empty selector ∧
      LabelSelectorV.matches selector spec.(Template').(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')
  end.

(* The shared template predicate includes RestartPolicy = Always and
   ActiveDeadlineSeconds = None after preparation, as required by DaemonSet. *)
Definition template_valid (spec : t) : Prop :=
  PodTemplateSpecV.valid spec.(Template').

(* Compute the same two-field result described by update_strategy_normalized. *)
Definition normalized_update_strategy
    (strategy : DaemonSetView.DaemonSetUpdateStrategyV.t)
    : DaemonSetView.DaemonSetUpdateStrategyV.t :=
  let strategy_type := default_update_strategy_type strategy.(DaemonSetView.DaemonSetUpdateStrategyV.Type') in
  {|
    DaemonSetView.DaemonSetUpdateStrategyV.Type' := strategy_type;
    DaemonSetView.DaemonSetUpdateStrategyV.RollingUpdate' :=
      if decide (strategy_type = "RollingUpdate"%go)
      then Some (default_rolling_update strategy.(DaemonSetView.DaemonSetUpdateStrategyV.RollingUpdate'))
      else converted_rolling_update strategy.(DaemonSetView.DaemonSetUpdateStrategyV.RollingUpdate');
  |}.

(* A concrete candidate result for creation: preserve Selector and
   MinReadySeconds, prepare Template, default/convert UpdateStrategy, and
   default RevisionHistoryLimit. *)
Definition normalized (spec : t) : t :=
  spec <| Template' := PodTemplateSpecV.normalized spec.(Template') |>
    <| UpdateStrategy' := normalized_update_strategy spec.(UpdateStrategy') |>
    <| RevisionHistoryLimit' := Some (default (W32 10) spec.(RevisionHistoryLimit')) |>.

(* Conditions on a submitted spec. Defaults may still be omitted here.
   This is the Spec component of creation, not a complete API admission check:
   root metadata, conversion errors and other admission checks are separate. *)
Definition valid_create (spec : t) : Prop :=
  selector_valid spec ∧
  template_valid spec ∧
  update_strategy_valid (normalized_update_strategy spec.(UpdateStrategy')) ∧
  min_ready_seconds_valid spec ∧
  revision_history_limit_valid spec.

(* Creation-path storage invariant in the fixed model configuration.
   Compatibility with legacy objects and old-template-dependent updates must
   be addressed separately when implementing the update path. *)
Definition valid (spec : t) : Prop :=
  valid_create spec ∧ normalized spec = spec.

(* Relate all five input/result fields. This relation describes processing;
   it does not by itself assert that the input passes admission validation. *)
Definition created (input stored : t) : Prop :=
  stored.(Selector') = input.(Selector') ∧
  stored.(Template') = PodTemplateSpecV.normalized input.(Template') ∧
  update_strategy_normalized input stored ∧
  stored.(MinReadySeconds') = input.(MinReadySeconds') ∧
  revision_history_limit_defaulted input stored.

Definition selector_for_comparison
    (selector : LabelSelectorV.t) : LabelSelectorV.t :=
  selector
    <| LabelSelectorV.MatchLabels' :=
      Some (default ∅ selector.(LabelSelectorV.MatchLabels')) |>
    <| LabelSelectorV.MatchExpressions' := Some
      ((λ requirement, requirement
        <| LabelSelectorRequirementV.Values' :=
          Some (LabelSelectorRequirementV.values_list requirement) |>)
        <$> LabelSelectorV.match_expressions_list selector) |>.

Definition selector_unchanged (old input : t) : Prop :=
  (selector_for_comparison <$> input.(Selector')) =
  (selector_for_comparison <$> old.(Selector')).

Module UpdateAPI.

Parameter prepare_template :
  PodTemplateSpecV.t → PodTemplateSpecV.t → PodTemplateSpecV.t.

Parameter validate_selector_template : t → t → bool.

End UpdateAPI.

Definition normalized_update (old input : t) : t :=
  input
    <| Template' :=
      UpdateAPI.prepare_template old.(Template') input.(Template') |>
    <| UpdateStrategy' :=
      normalized_update_strategy input.(UpdateStrategy') |>
    <| RevisionHistoryLimit' :=
      Some (default (W32 10) input.(RevisionHistoryLimit')) |>.

Definition valid_update (old input : t) : Prop :=
  let prepared := normalized_update old input in
  selector_unchanged old prepared ∧
  UpdateAPI.validate_selector_template old prepared = true ∧
  update_strategy_valid prepared.(UpdateStrategy') ∧
  min_ready_seconds_valid prepared ∧
  revision_history_limit_valid prepared.

Definition updated (old input stored : t) : Prop :=
  stored = normalized_update old input.

(* for any update_strategy, whether it satisfies update_strategy_valid*)
Global Instance update_strategy_valid_dec strategy :
  Decision (update_strategy_valid strategy).
Proof.
  unfold update_strategy_valid.
  repeat case_decide; try apply _.
  destruct strategy.(DaemonSetView.DaemonSetUpdateStrategyV.RollingUpdate')
    as [[unavailable surge]|]; last apply _.
  unfold rolling_update_valid; simpl.
  destruct unavailable as [unavailable|], surge as [surge|]; try apply _.
  unfold daemonset_int_or_percent_valid, positive_int_percent_valid,
    int_or_string_integer_valid, int_or_string_percent_valid, int_or_percent_is_zero.
  repeat case_decide;
    destruct (parse_percent_string unavailable.(intstr.IntOrString.StrVal'));
    destruct (parse_percent_string surge.(intstr.IntOrString.StrVal'));
    apply _.
Defined.

Global Instance valid_update_dec old input :
  Decision (valid_update old input).
Proof.
  unfold valid_update.
  set (prepared := normalized_update old input).
  unfold selector_unchanged, min_ready_seconds_valid, revision_history_limit_valid.
  destruct prepared.(RevisionHistoryLimit'); apply _.
Defined.

(* for idempotent lemmas below, used to proof once default is value added,
   next time default won't change them *)
Lemma default_update_strategy_type_idempotent strategy_type :
  default_update_strategy_type (default_update_strategy_type strategy_type) =
    default_update_strategy_type strategy_type.
Proof.
  unfold default_update_strategy_type.
  repeat case_decide; simplify_eq; done.
Qed.

Lemma default_rolling_update_idempotent rolling :
  default_rolling_update (Some (default_rolling_update rolling)) = default_rolling_update rolling.
Proof.
  destruct rolling as [[unavailable surge]|]; [destruct unavailable, surge|]; done.
Qed.

Lemma converted_rolling_update_idempotent rolling :
  converted_rolling_update (converted_rolling_update rolling) = converted_rolling_update rolling.
Proof.
  destruct rolling as [[unavailable surge]|]; [destruct unavailable, surge|]; done.
Qed.

Lemma normalized_update_strategy_idempotent strategy :
  normalized_update_strategy (normalized_update_strategy strategy) = normalized_update_strategy strategy.
Proof.
  unfold normalized_update_strategy; simpl.
  rewrite default_update_strategy_type_idempotent.
  case_decide; simpl.
  - rewrite default_rolling_update_idempotent. reflexivity.
  - rewrite converted_rolling_update_idempotent. reflexivity.
Qed.

Lemma normalized_idempotent spec : normalized (normalized spec) = normalized spec.
Proof.
  unfold normalized; simpl.
  rewrite PodTemplateSpecV.normalized_idempotent normalized_update_strategy_idempotent.
  destruct spec.(RevisionHistoryLimit'); done.
Qed.

(* nomalization operations won't impact fields' validation*)
Lemma selector_valid_normalized spec : selector_valid (normalized spec) ↔ selector_valid spec.
Proof. done. Qed.

Lemma valid_create_normalized spec : valid_create spec → valid_create (normalized spec).
Proof.
  intros (Hselector & Htemplate & Hstrategy & Hmin & Hhistory).
  unfold valid_create. split_and!.
  - apply selector_valid_normalized. exact Hselector.
  - unfold template_valid in *. simpl. apply PodTemplateSpecV.normalized_valid. exact Htemplate.
  - simpl. rewrite normalized_update_strategy_idempotent. exact Hstrategy.
  - exact Hmin.
  - unfold revision_history_limit_valid in *. simpl.
    destruct spec.(RevisionHistoryLimit') as [n|]; simpl in *; [exact Hhistory|word].
Qed.

Lemma created_normalized input : created input (normalized input).
Proof.
  unfold created, update_strategy_normalized, update_strategy_type_defaulted,
    rolling_update_normalized, revision_history_limit_defaulted, normalized, normalized_update_strategy.
  simpl. repeat split; reflexivity.
Qed.

Lemma created_eq_normalized input stored : created input stored → stored = normalized input.
Proof.
  destruct input as [selector template [strategy_type rolling] min_ready history].
  destruct stored as [selector' template' [strategy_type' rolling'] min_ready' history'].
  unfold created, update_strategy_normalized, update_strategy_type_defaulted,
    rolling_update_normalized, revision_history_limit_defaulted; simpl.
  intros (Hselector & Htemplate & [Htype Hrolling] & Hmin & Hhistory).
  subst. reflexivity.
Qed.

(* This consistency theorem depends on the existing trusted template
   normalization contracts; it is not a proof of the Kubernetes Go routines. *)
Lemma created_valid input stored :
  valid_create input → created input stored → valid stored.
Proof.
  intros Hvalid Hcreated. apply created_eq_normalized in Hcreated. subst stored.
  split; [apply valid_create_normalized; exact Hvalid|apply normalized_idempotent].
Qed.

End DaemonSetSpecV.


Module DaemonSetStatusV.
Include DaemonSetView.DaemonSetStatusV.

(* Creation resets the submitted status to its zero value. *)
Definition created (_input stored : t) : Prop :=
  stored = zero.

(* Some fields must be nonegative *)
Definition valid_request_nonegative (status : t) : Prop :=
  0 ≤ sint.Z status.(CurrentNumberScheduled') ∧
  0 ≤ sint.Z status.(NumberMisscheduled') ∧
  0 ≤ sint.Z status.(DesiredNumberScheduled') ∧
  0 ≤ sint.Z status.(NumberReady') ∧
  0 ≤ sint.Z status.(ObservedGeneration') ∧
  0 ≤ sint.Z status.(UpdatedNumberScheduled') ∧
  0 ≤ sint.Z status.(NumberAvailable') ∧
  0 ≤ sint.Z status.(NumberUnavailable') ∧
  (match status.(CollisionCount') with
   | None => True
   | Some count => (0 ≤ sint.Z count)
   end).

(* Stored statuses satisfy the numeric validation rules. *)
Definition valid (status : t) : Prop :=
  valid_request_nonegative status.

Global Instance valid_dec status : Decision (valid status).
Proof.
  unfold valid, valid_request_nonegative.
  destruct status.(CollisionCount'); apply _.
Defined.

(* CollisionCount cannot decrease*)
Definition collision_count_not_decreased (old input : t) : Prop :=
  match old.(CollisionCount'), input.(CollisionCount') with
  | None, _ => True
  | Some _, None => False
  | Some old_count, Some new_count =>
      sint.Z old_count ≤ sint.Z new_count
  end.

Global Instance collision_count_not_decreased_dec old input :
  Decision (collision_count_not_decreased old input).
Proof.
  unfold collision_count_not_decreased.
  destruct old.(CollisionCount'), input.(CollisionCount'); apply _.
Defined.

(* Only the Status part of ValidateDaemonSetStatusUpdate.
   ObjectMeta validation belongs to the whole-object specification. *)
Definition valid_update (old input : t) : Prop :=
  valid input ∧
  collision_count_not_decreased old input.

Global Instance valid_update_dec old input :
  Decision (valid_update old input).
Proof.
  unfold valid_update.
  apply _.
Defined.

(* The status-update strategy preserves all submitted Status fields. *)
Definition updated (input stored : t) : Prop :=
  stored = input.

Lemma valid_zero : valid zero.
Proof.
  rewrite /valid /valid_request_nonegative /zero /=.
  split_and!; word.
Qed.

Lemma created_valid input stored :
  created input stored → valid stored.
Proof.
  unfold created.
  intros ->.
  exact valid_zero.
Qed.

Lemma updated_valid old input stored :
  valid_update old input → updated input stored → valid stored.
Proof.
  intros [Hvalid _] Hupdated.
  unfold updated in Hupdated.
  subst stored.
  exact Hvalid.
Qed.

End DaemonSetStatusV.


Module DaemonSetV.
Include DaemonSetView.DaemonSetV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Definition kind : go_string :=
  "DaemonSet"%go.

Definition meta_key (meta : ObjectMetaV.t) : KKey.t :=
  {|
    KKey.Kind' := kind;
    KKey.Namespace' := meta.(ObjectMetaV.Namespace');
    KKey.Name' := meta.(ObjectMetaV.Name');
  |}.

Definition key (v: t) : KKey.t :=
  meta_key v.(ObjectMeta').

Definition valid (sts: t) : Prop :=
  valid_typemeta kind sts.(TypeMeta') ∧
  valid_resource_version sts.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  ObjectMetaV.valid kind sts.(ObjectMeta') ∧
  DaemonSetSpecV.valid sts.(Spec') ∧
  DaemonSetStatusV.valid sts.(Status').

Definition extra_valid (_sts : t) : Prop := True.

(* Parse a signed decimal integer within the int64 range. *)
Definition parse_decimal_int64 (s : go_string) : option Z :=
  let parsed :=
    match s with
    | [] => None
    | b :: rest =>
        if decide (b = W8 45) then
          (* ASCII '-' *)
          match parse_decimal_string rest with
          | Some n => Some (- Z.of_nat n)
          | None => None
          end
        else if decide (b = W8 43) then
          (* ASCII '+' *)
          match parse_decimal_string rest with
          | Some n => Some (Z.of_nat n)
          | None => None
          end
        else
          match parse_decimal_string s with
          | Some n => Some (Z.of_nat n)
          | None => None
          end
    end in
  match parsed with
  | None => None
  | Some z =>
      if decide ((- (2 ^ 63) ≤ z < 2 ^ 63)%Z)
      then Some z
      else None
  end.

(* A missing annotation is allowed; a present value must parse successfully. *)
Definition template_generation_annotation_valid
    (meta : ObjectMetaV.t) : Prop :=
  let annotations := default ∅ meta.(ObjectMetaV.Annotations') in
  match annotations !! "deprecated.daemonset.template.generation"%go with
  | None => True
  | Some value => is_Some (parse_decimal_int64 value)
  end.

Definition valid_create request_kind ns (input : t) : Prop :=
  request_kind = kind ∧
  ns ≠ ""%go ∧
  valid_namespace ns ∧
  valid_create_typemeta kind input.(TypeMeta') ∧
  template_generation_annotation_valid input.(ObjectMeta') ∧
  ObjectMetaV.valid_create kind ns input.(ObjectMeta') ∧
  DaemonSetSpecV.valid_create input.(Spec').

(* Assemble the ordinary-update precondition using the current model interfaces.
   This is not a complete characterization of Kubernetes update acceptance. *)

(* first check request and input object *)
Definition valid_update_input
    (request_kind namespace : go_string) (input : t) : Prop :=
  request_kind = kind ∧
  namespace ≠ ""%go ∧
  valid_namespace namespace ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  template_generation_annotation_valid input.(ObjectMeta').

(* check the request and input, changes between input and old metadata, and old spec*)
Definition valid_update
    (request_kind namespace : go_string)
    (old_meta : ObjectMetaV.t)
    (old_spec : DaemonSetSpecV.t)
    (input : t) : Prop :=
  valid_update_input request_kind namespace input ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  DaemonSetSpecV.valid_update old_spec input.(Spec').

Definition valid_status_update
    (request_kind namespace : go_string)
    (old_meta : ObjectMetaV.t)
    (old_status : DaemonSetStatusV.t)
    (input : t) : Prop :=
  request_kind = kind ∧
  namespace ≠ ""%go ∧
  valid_namespace namespace ∧
  namespace = input.(ObjectMeta').(ObjectMetaV.Namespace') ∧
  input.(ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ∧
  input.(ObjectMeta').(ObjectMetaV.UID') ≠ ""%go ∧
  valid_resource_version input.(ObjectMeta').(ObjectMetaV.ResourceVersion') ∧
  valid_typemeta kind input.(TypeMeta') ∧
  template_generation_annotation_valid input.(ObjectMeta') ∧
  ObjectMetaV.valid_update old_meta input.(ObjectMeta') ∧
  DaemonSetStatusV.valid_update old_status input.(Status').

(* read and parse special annotations, successfully parse will return a new-constructed metadata*)
Definition prepare_create_metadata
    (meta : ObjectMetaV.t) : option ObjectMetaV.t :=
  let annotations := default ∅ meta.(ObjectMetaV.Annotations') in
  let parsed :=
    match annotations !! "deprecated.daemonset.template.generation"%go with
    | None => Some 0%Z
    | Some value => parse_decimal_int64 value
    end in
  match parsed with
  | None => None
  | Some n =>
      let template_generation := Z.max 1 n in
      let value := decimal_string (Z.to_nat template_generation) in
      Some (meta <| ObjectMetaV.Annotations' :=
        Some (<["deprecated.daemonset.template.generation"%go := value]> annotations) |>)
  end.

(* Preparation changes only annotations; API-model clients also need the
   unchanged identity and owner-reference fields. *)
Lemma prepare_create_metadata_eq input prepared :
  prepare_create_metadata input = Some prepared →
  prepared = input <| ObjectMetaV.Annotations' := prepared.(ObjectMetaV.Annotations') |>.
Proof.
  unfold prepare_create_metadata.
  destruct (match (default ∅ input.(ObjectMetaV.Annotations')) !!
      "deprecated.daemonset.template.generation"%go with
    | None => Some 0%Z
    | Some value => parse_decimal_int64 value
    end) as [n|]; last discriminate.
  intros Heq. inversion Heq; subst. done.
Qed.

Definition created (namespace : go_string) (input stored : t) : Prop :=
  match prepare_create_metadata input.(ObjectMeta') with
  | None => False
  | Some expected_meta =>
      valid_typemeta kind stored.(TypeMeta') ∧
      ObjectMetaV.created namespace expected_meta stored.(ObjectMeta') ∧
      stored.(ObjectMeta').(ObjectMetaV.Generation') = W64 1 ∧
      DaemonSetSpecV.created input.(Spec') stored.(Spec') ∧
      DaemonSetStatusV.created input.(Status') stored.(Status')
  end.

Lemma created_metadata namespace input stored :
  created namespace input stored →
  stored.(ObjectMeta').(ObjectMetaV.Namespace') = namespace ∧
  stored.(ObjectMeta').(ObjectMetaV.OwnerReferences') = input.(ObjectMeta').(ObjectMetaV.OwnerReferences') ∧
  stored.(ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None.
Proof.
  unfold created.
  destruct (prepare_create_metadata input.(ObjectMeta')) as [prepared|] eqn:Hprepare;
    last contradiction.
  intros (_ & Hmeta & _).
  apply prepare_create_metadata_eq in Hprepare.
  rewrite Hprepare /ObjectMetaV.created /= in Hmeta. tauto.
Qed.

(* Canonical signed decimal spelling, as used by strconv.FormatInt(n, 10). *)
Definition signed_decimal_string (n : Z) : go_string :=
  if decide ((n < 0) %Z)
  then W8 45 :: decimal_string (Z.to_nat ( - n))
  else decimal_string (Z.to_nat n).

(* Abstraction for the current interface, which provides no old metadata.
   The special annotation becomes a canonical int64 value.
   Its relationship to the old value is not specified here.
   Generation and ResourceVersion retain ObjectMetaV.updated's abstraction. *)
Definition metadata_updated (input stored : ObjectMetaV.t) : Prop :=
  ∃ template_generation : Z,
    (- (2 ^ 63) ≤ template_generation < 2 ^ 63)%Z ∧
    ObjectMetaV.updated
      (input <| ObjectMetaV.Annotations' :=
        Some (<["deprecated.daemonset.template.generation"%go :=
          signed_decimal_string template_generation]>
          (default ∅ input.(ObjectMetaV.Annotations'))) |>)
      stored.

(* Expose the ordinary metadata guarantees without claiming that the special
   annotation is unchanged. Generation and ResourceVersion remain abstract. *)
Lemma metadata_updated_preserves_fields input stored :
  metadata_updated input stored →
  ObjectMetaV.updated
    (input <| ObjectMetaV.Annotations' := stored.(ObjectMetaV.Annotations') |>) stored.
Proof.
  intros (generation & Hrange & Hupdated).
  rewrite /ObjectMetaV.updated /= in Hupdated |- *. tauto.
Qed.

Definition status_updated (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  metadata_updated input.(ObjectMeta') stored.(ObjectMeta') ∧
  DaemonSetStatusV.updated input.(Status') stored.(Status').

Definition updated
    (old_spec : DaemonSetSpecV.t)
    (input stored : t) : Prop :=
  stored.(TypeMeta') = input.(TypeMeta') ∧
  metadata_updated input.(ObjectMeta') stored.(ObjectMeta') ∧
  DaemonSetSpecV.updated old_spec input.(Spec') stored.(Spec').

#[global]
Instance top_level_instance : top_level Σ t :=
  Build_top_level Σ t ObjectMetaV.t DaemonSetSpecV.t DaemonSetStatusV.t
    valid
    extra_valid
    valid_create
    valid_update
    valid_status_update
    created
    updated
    status_updated
    deepown_l.

Definition valid_without_meta (ds : t) : Prop :=
  DaemonSetSpecV.valid ds.(Spec') ∧
  DaemonSetStatusV.valid ds.(Status').

Definition typemeta_ptr l: loc :=
  struct_field_ref v1.DaemonSet.t "TypeMeta" l.

Definition objectmeta_ptr l: loc :=
  struct_field_ref v1.DaemonSet.t "ObjectMeta" l.

Definition spec_ptr l: loc :=
  struct_field_ref v1.DaemonSet.t "Spec" l.

Definition status_ptr l: loc :=
  struct_field_ref v1.DaemonSet.t "Status" l.

Definition update_objectmeta (v: t) (m: ObjectMetaV.t) : t :=
  v <| ObjectMeta' := m |>.

Definition deepown_without_meta (c: v1.DaemonSet.t) (v: t) dq: iProp Σ :=
  "Hdeepown_spec" ∷ DaemonSetSpecV.deepown c.(v1.DaemonSet.Spec') v.(Spec') dq ∗
  "Hdeepown_status" ∷ DaemonSetStatusV.deepown c.(v1.DaemonSet.Status') v.(Status') dq.

Definition deepown_l_without_meta l v (dq: dfrac): iProp Σ :=
  ∃ c,
    spec_ptr l ↦{dq} c.(v1.DaemonSet.Spec') ∗
    status_ptr l ↦{dq} c.(v1.DaemonSet.Status') ∗
    deepown_without_meta c v dq.

End def.
(* the same as deepown proofs in StatefulSetV *)
Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.

Lemma deepown_l_split l v dq:
  deepown_l l v dq ⊢
    ⌜ l ≠ null ⌝ ∗
    (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
    ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
    DaemonSetSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
    DaemonSetStatusV.deepown_l (status_ptr l) v.(Status') dq.
Proof.
  unfold deepown_l, deepown.
  iIntros "H".
  iDestruct "H" as (c) "[Hl Hdeepown]".
  iDestruct "Hdeepown" as "(%Htypemeta & Hobjectmeta & Hspec & Hstatus)".
  iDestruct (struct_fields_split (V:=v1.DaemonSet.t) with "Hl")
    as "[Hfields %Hnot_null]".
  iNamedPrefix "Hfields" "H".
  iSplitR; first done.
  rewrite -Htypemeta.
  iFrame "HTypeMeta".
  iSplitL "HObjectMeta Hobjectmeta".
  { unfold ObjectMetaV.deepown_l, objectmeta_ptr. iFrame. }
  iSplitL "HSpec Hspec".
  { unfold DaemonSetSpecV.deepown_l, spec_ptr. iFrame. }
  unfold DaemonSetStatusV.deepown_l, status_ptr. iFrame.
Qed.

Lemma deepown_l_merge l v vm dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) vm dq ∗
  DaemonSetSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  DaemonSetStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
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
  iAssert (typed_pointsto_def l (v1.DaemonSet.mk v_typemeta cm cspec cstatus) dq)
    with "[HTypeMeta HObjectMeta HSpec HStatus]" as "Hfields".
  { simpl. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.DaemonSet.t)
    l (v1.DaemonSet.mk v_typemeta cm cspec cstatus) dq Hnot_null
    with "Hfields") as "Hl".
  iExists (v1.DaemonSet.mk v_typemeta cm cspec cstatus).
  iSplitL "Hl"; first iExact "Hl".
  iSplitR "Hobjectmeta Hspec Hstatus"; first done.
  simpl. iFrame.
Qed.

Lemma deepown_l_restore l v dq:
  l ≠ null →
  (typemeta_ptr l) ↦{dq} v.(TypeMeta') ∗
  ObjectMetaV.deepown_l (objectmeta_ptr l) v.(ObjectMeta') dq ∗
  DaemonSetSpecV.deepown_l (spec_ptr l) v.(Spec') dq ∗
  DaemonSetStatusV.deepown_l (status_ptr l) v.(Status') dq ⊢
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
End DaemonSetV.