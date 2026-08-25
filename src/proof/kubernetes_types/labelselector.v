From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export common.

Module LabelSelectorRequirementV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.

Record t := mk {
  Key' : go_string;
  Operator' : v1.LabelSelectorOperator.t;
  Values' : option (list go_string);
}.

Global Instance eq_dec : EqDecision t.
Proof. solve_decision. Defined.

Definition valid_operator (operator : v1.LabelSelectorOperator.t) : Prop :=
  operator = "In"%go ∨ operator = "NotIn"%go ∨
  operator = "Exists"%go ∨ operator = "DoesNotExist"%go.

(* Kubernetes validation and selector matching use only [len(Values)], so nil
   and non-nil empty slices have the same semantic value. *)
Definition values_list (requirement : t) : list go_string :=
  match requirement.(Values') with
  | Some values => values
  | None => []
  end.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/validation/validation.go#L76-L103 *)
Definition valid (requirement : t) : Prop :=
  valid_operator requirement.(Operator') ∧
  ((requirement.(Operator') = "In"%go ∨
      requirement.(Operator') = "NotIn"%go) →
    values_list requirement ≠ []) ∧
  ((requirement.(Operator') = "Exists"%go ∨
      requirement.(Operator') = "DoesNotExist"%go) →
    values_list requirement = []) ∧
  valid_label_name requirement.(Key') ∧
  Forall valid_label_value (values_list requirement).

Definition deepown (c : v1.LabelSelectorRequirement.t) (v : t) dq : iProp Σ :=
  "%Hdeepown_key" ∷ ⌜c.(v1.LabelSelectorRequirement.Key') = v.(Key')⌝ ∗
  "%Hdeepown_operator" ∷
    ⌜c.(v1.LabelSelectorRequirement.Operator') = v.(Operator')⌝ ∗
  "%Hdeepown_values_none" ∷
    ⌜c.(v1.LabelSelectorRequirement.Values') = slice.nil ↔
      v.(Values') = None⌝ ∗
  "Hdeepown_values_some" ∷
    (match v.(Values') with
    | Some values =>
        c.(v1.LabelSelectorRequirement.Values') ↦*{dq} values
    | None => True%I
    end).

End def.
End LabelSelectorRequirementV.

Module LabelSelectorV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.

Record t := mk {
  MatchLabels' : option (gmap go_string go_string);
  MatchExpressions' : option (list LabelSelectorRequirementV.t);
}.

Global Instance eq_dec : EqDecision t.
Proof. solve_decision. Defined.

(* As with requirement values, Kubernetes treats nil and non-nil empty
   MatchExpressions slices identically for validation and matching. *)
Definition match_expressions_list
    (selector : t) : list LabelSelectorRequirementV.t :=
  match selector.(MatchExpressions') with
  | Some match_expressions => match_expressions
  | None => []
  end.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/validation/validation.go#L62-L74 *)
Definition valid (selector : t) : Prop :=
  valid_labels selector.(MatchLabels') ∧
  Forall LabelSelectorRequirementV.valid
    (match_expressions_list selector).

Definition extra_valid (selector : t) : Prop :=
  Z.of_nat
    (size (default ∅ selector.(MatchLabels')) +
      length (match_expressions_list selector)) ≤ 2 ^ 63 - 1.

Definition empty (selector : t) : Prop :=
  (selector.(MatchLabels') = None ∨ selector.(MatchLabels') = Some ∅) ∧
  match_expressions_list selector = [].

Definition match_labels
    (required labels : option (gmap go_string go_string)) : Prop :=
  match required with
  | None => True
  | Some required_labels =>
      match labels with
      | None => required_labels = ∅
      | Some labels =>
          ∀ key value, required_labels !! key = Some value →
            labels !! key = Some value
      end
  end.

Definition selected_label
    (labels : option (gmap go_string go_string)) (key : go_string) :
    option go_string :=
  match labels with
  | Some labels => labels !! key
  | None => None
  end.

Definition requirement_matches
    (labels : option (gmap go_string go_string))
    (requirement : LabelSelectorRequirementV.t) : Prop :=
  (requirement.(LabelSelectorRequirementV.Operator') = "In"%go ∧
    match selected_label labels requirement.(LabelSelectorRequirementV.Key') with
    | Some label_value =>
        label_value ∈ LabelSelectorRequirementV.values_list requirement
    | None => False
    end) ∨
  (requirement.(LabelSelectorRequirementV.Operator') = "NotIn"%go ∧
    match selected_label labels requirement.(LabelSelectorRequirementV.Key') with
    | Some label_value =>
        label_value ∉ LabelSelectorRequirementV.values_list requirement
    | None => True
    end) ∨
  (requirement.(LabelSelectorRequirementV.Operator') =
      "Exists"%go ∧
      is_Some
        (selected_label labels requirement.(LabelSelectorRequirementV.Key'))) ∨
  (requirement.(LabelSelectorRequirementV.Operator') =
      "DoesNotExist"%go ∧
      selected_label labels requirement.(LabelSelectorRequirementV.Key') = None).

Global Instance requirement_matches_dec labels requirement :
  Decision (requirement_matches labels requirement).
Proof.
  unfold requirement_matches, selected_label.
  destruct labels as [label_map|].
  - destruct (label_map !! requirement.(LabelSelectorRequirementV.Key'));
      simpl; apply _.
  - apply _.
Defined.

Definition matches
    (selector : t) (labels : option (gmap go_string go_string)) : Prop :=
  match_labels selector.(MatchLabels') labels ∧
  Forall (requirement_matches labels) (match_expressions_list selector).

Global Instance match_labels_dec required labels :
  Decision (match_labels required labels).
Proof.
  unfold match_labels.
  destruct required as [required|]; last (left; done).
  destruct labels as [labels|].
  - destruct (decide (required ⊆ labels)) as [Hsubset|Hnot_subset].
    + left. rewrite map_subseteq_spec in Hsubset. exact Hsubset.
    + right. intros Hmatches. apply Hnot_subset.
      rewrite map_subseteq_spec. exact Hmatches.
  - apply _.
Defined.

Global Instance matches_dec selector labels : Decision (matches selector labels).
Proof. unfold matches. apply _. Defined.

Definition deepown (c : v1.LabelSelector.t) (v : t) dq : iProp Σ :=
  "%Hdeepown_matchlabels_none" ∷
    ⌜c.(v1.LabelSelector.MatchLabels') = null ↔ v.(MatchLabels') = None⌝ ∗
  "Hdeepown_matchlabels_some" ∷
    (match v.(MatchLabels') with
    | Some match_labels =>
        ∃ match_labels_c,
          c.(v1.LabelSelector.MatchLabels') ↦${dq} match_labels_c ∗
          ⌜match_labels_c = match_labels⌝
    | None => True%I
    end) ∗
  "%Hdeepown_matchexpressions_none" ∷
    ⌜c.(v1.LabelSelector.MatchExpressions') = slice.nil ↔
      v.(MatchExpressions') = None⌝ ∗
  "Hdeepown_matchexpressions_some" ∷
    (match v.(MatchExpressions') with
    | Some match_expressions =>
        ∃ match_expressions_c,
          deepown_list c.(v1.LabelSelector.MatchExpressions')
            match_expressions_c match_expressions
            (λ requirement pure_requirement,
              LabelSelectorRequirementV.deepown
                requirement pure_requirement dq)
    | None => True%I
    end).

Definition deepown_l l v dq : iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

End def.
End LabelSelectorV.
