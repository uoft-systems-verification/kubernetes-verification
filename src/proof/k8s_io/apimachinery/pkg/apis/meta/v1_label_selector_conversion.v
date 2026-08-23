From New.proof Require Import prelude empty_ffi.
From New.proof.k8s_io.apimachinery.pkg Require Export labels_add.
From New.proof.kubernetes_types Require Import labelselector.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {labels_sem : labels.Assumptions}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Local Set Default Proof Using "All".

Definition map_label_requirement (key value : go_string) :
    LabelRequirementV.t :=
  LabelRequirementV.mk key "="%go [value].

Definition expression_converts
    (api : LabelSelectorRequirementV.t)
    (requirement : LabelRequirementV.t) : Prop :=
  requirement.(LabelRequirementV.Key') =
      api.(LabelSelectorRequirementV.Key') ∧
  requirement.(LabelRequirementV.Values') =
      LabelSelectorRequirementV.values_list api ∧
  ((api.(LabelSelectorRequirementV.Operator') = "In"%go ∧
      requirement.(LabelRequirementV.Operator') = "in"%go) ∨
    (api.(LabelSelectorRequirementV.Operator') = "NotIn"%go ∧
      requirement.(LabelRequirementV.Operator') = "notin"%go) ∨
    (api.(LabelSelectorRequirementV.Operator') = "Exists"%go ∧
      requirement.(LabelRequirementV.Operator') = "exists"%go) ∨
    (api.(LabelSelectorRequirementV.Operator') = "DoesNotExist"%go ∧
      requirement.(LabelRequirementV.Operator') = "!"%go)).

Lemma expression_converts_supported api requirement :
  expression_converts api requirement →
  LabelRequirementV.supported requirement.
Proof.
  intros (_ & _ & Hop).
  destruct Hop as [[_ Hrequirement]|[[_ Hrequirement]|
      [[_ Hrequirement]|[_ Hrequirement]]]];
    rewrite /LabelRequirementV.supported Hrequirement /=; tauto.
Qed.

Lemma valid_expression_conversion api :
  LabelSelectorRequirementV.valid api →
  ∃ requirement,
    expression_converts api requirement ∧
    valid_requirement_inputs
      requirement.(LabelRequirementV.Key')
      requirement.(LabelRequirementV.Operator')
      requirement.(LabelRequirementV.Values').
Proof.
  intros (Hop & Hin & Hexists & Hkey & Hvalues).
  destruct Hop as [Hop|[Hop|[Hop|Hop]]].
  - exists (LabelRequirementV.mk api.(LabelSelectorRequirementV.Key')
      "in"%go (LabelSelectorRequirementV.values_list api)).
    split; [rewrite /expression_converts /=; tauto|].
    rewrite /valid_requirement_inputs /=. split_and!; try done.
    left. split; [left; done|]. apply Hin. tauto.
  - exists (LabelRequirementV.mk api.(LabelSelectorRequirementV.Key')
      "notin"%go (LabelSelectorRequirementV.values_list api)).
    split; [rewrite /expression_converts /=; tauto|].
    rewrite /valid_requirement_inputs /=. split_and!; try done.
    left. split; [right; done|]. apply Hin. tauto.
  - exists (LabelRequirementV.mk api.(LabelSelectorRequirementV.Key')
      "exists"%go (LabelSelectorRequirementV.values_list api)).
    split; [rewrite /expression_converts /=; tauto|].
    rewrite /valid_requirement_inputs /=. split_and!; try done.
    right. right. split; [left; done|]. apply Hexists. tauto.
  - exists (LabelRequirementV.mk api.(LabelSelectorRequirementV.Key')
      "!"%go (LabelSelectorRequirementV.values_list api)).
    split; [rewrite /expression_converts /=; tauto|].
    rewrite /valid_requirement_inputs /=. split_and!; try done.
    right. right. split; [right; done|]. apply Hexists. tauto.
Qed.

Lemma expression_converts_valid_inputs api requirement :
  LabelSelectorRequirementV.valid api →
  expression_converts api requirement →
  valid_requirement_inputs
    requirement.(LabelRequirementV.Key')
    requirement.(LabelRequirementV.Operator')
    requirement.(LabelRequirementV.Values').
Proof.
  intros (Hop_valid & Hin & Hexists & Hkey_valid & Hvalues_valid)
    (Hkey & Hvalues & Hop).
  rewrite /valid_requirement_inputs Hkey Hvalues.
  split_and!; try done.
  destruct Hop as [[Hapi Hop]|[[Hapi Hop]|[[Hapi Hop]|[Hapi Hop]]]].
  - rewrite Hop. left. split; [left; done|]. apply Hin. tauto.
  - rewrite Hop. left. split; [right; done|]. apply Hin. tauto.
  - rewrite Hop. right. right. split; [left; done|].
    apply Hexists. tauto.
  - rewrite Hop. right. right. split; [right; done|].
    apply Hexists. tauto.
Qed.

Lemma expression_converts_matches api requirement labels_set :
  expression_converts api requirement →
  LabelRequirementV.matches requirement labels_set ↔
    LabelSelectorV.requirement_matches labels_set api.
Proof.
  intros (Hkey & Hvalues & Hop).
  destruct Hop as [[Hapi Hop]|[[Hapi Hop]|[[Hapi Hop]|[Hapi Hop]]]].
  all: rewrite /LabelRequirementV.matches
      /LabelSelectorV.requirement_matches
      /LabelRequirementV.selected_label /LabelSelectorV.selected_label
      Hkey Hvalues Hapi Hop /=.
  all: destruct labels_set as [label_map|]; simpl.
  all: try destruct (label_map !! api.(LabelSelectorRequirementV.Key'));
    simpl.
  Timeout 10 all: set_solver.
Qed.

Lemma map_label_requirement_matches key value labels_set :
  LabelRequirementV.matches (map_label_requirement key value) labels_set ↔
  LabelSelectorV.selected_label labels_set key = Some value.
Proof.
  rewrite /map_label_requirement /LabelRequirementV.matches
    /LabelRequirementV.selected_label /LabelSelectorV.selected_label /=.
  destruct labels_set as [labels_set|]; simpl.
  all: try destruct (labels_set !! key); simpl.
  Timeout 10 all: set_solver.
Qed.

Lemma selector_matches_snoc requirements requirement labels_set :
  selector_matches (requirements ++ [requirement]) labels_set ↔
  selector_matches requirements labels_set ∧
    LabelRequirementV.matches requirement labels_set.
Proof. rewrite /selector_matches Forall_app Forall_singleton. done. Qed.

Fixpoint map_requirements (keys : list go_string)
    (labels_map : gmap go_string go_string) : list LabelRequirementV.t :=
  match keys with
  | [] => []
  | key :: keys =>
      match labels_map !! key with
      | Some value =>
          map_label_requirement key value :: map_requirements keys labels_map
      | None => map_requirements keys labels_map
      end
  end.

Lemma elem_of_map_requirements requirement keys labels_map :
  requirement ∈ map_requirements keys labels_map ↔
  ∃ key value, key ∈ keys ∧ labels_map !! key = Some value ∧
    requirement = map_label_requirement key value.
Proof.
  induction keys as [|key keys IH]; simpl.
  { Timeout 10 set_solver. }
  destruct (labels_map !! key) as [value|] eqn:Hlookup; simpl.
  - rewrite elem_of_cons IH. Timeout 10 set_solver.
  - rewrite IH. Timeout 10 set_solver.
Qed.

Lemma map_requirements_snoc keys labels_map key value :
  labels_map !! key = Some value →
  map_requirements (keys ++ [key]) labels_map =
    map_requirements keys labels_map ++ [map_label_requirement key value].
Proof.
  intros Hlookup. induction keys as [|head keys IH]; simpl.
  - rewrite Hlookup. done.
  - destruct (labels_map !! head); simpl; rewrite IH; done.
Qed.

Lemma map_requirements_length keys labels_map :
  (∀ key, In key keys → ∃ value, labels_map !! key = Some value) →
  length (map_requirements keys labels_map) = length keys.
Proof.
  intros Hlookup. induction keys as [|key keys IH]; simpl; first done.
  destruct (Hlookup key (or_introl eq_refl)) as [value Hvalue].
  rewrite Hvalue /=. f_equal. apply IH.
  intros key' Hkey'. apply Hlookup. right. exact Hkey'.
Qed.

Lemma map_requirements_supported keys labels_map :
  Forall LabelRequirementV.supported (map_requirements keys labels_map).
Proof.
  induction keys as [|key keys IH]; simpl; first constructor.
  destruct (labels_map !! key) as [value|]; last exact IH.
  constructor; last exact IH.
  rewrite /map_label_requirement /LabelRequirementV.supported /=. tauto.
Qed.

Lemma expression_conversions_supported apis requirements :
  Forall2 expression_converts apis requirements →
  Forall LabelRequirementV.supported requirements.
Proof.
  intros Hconverts. induction Hconverts as
    [|api requirement apis requirements Hconvert _ IH].
  - constructor.
  - constructor.
    + eapply expression_converts_supported. exact Hconvert.
    + exact IH.
Qed.

Lemma Forall2_nil_left {A B} (R : A → B → Prop) ys :
  Forall2 R [] ys → ys = [].
Proof. intros Hrelated. inversion Hrelated. done. Qed.

Lemma fmap_eq_nil {A B} (f : A → B) xs :
  f <$> xs = [] → xs = [].
Proof. destruct xs; simpl; [done|discriminate]. Qed.

Lemma map_requirements_match keys labels_map labels_set :
  list_to_set keys = dom labels_map →
  selector_matches (map_requirements keys labels_map) labels_set ↔
    LabelSelectorV.match_labels (Some labels_map) labels_set.
Proof.
  intros Hdom. rewrite /selector_matches.
  destruct labels_set as [labels_set|].
  - rewrite /LabelSelectorV.match_labels Forall_forall.
    split; intros Hmatch.
    + intros key value Hlookup.
      apply (proj1 (map_label_requirement_matches key value (Some labels_set))).
      apply Hmatch. rewrite <-list_elem_of_In.
      apply (proj2 (elem_of_map_requirements _ _ _)).
      exists key, value. repeat split; try done.
      rewrite <-(elem_of_list_to_set (C:=gset go_string)).
      rewrite Hdom elem_of_dom. eauto.
    + intros requirement Hin.
      rewrite <-list_elem_of_In in Hin.
      apply (proj1 (elem_of_map_requirements _ _ _)) in Hin as
        (key & value & _ & Hlookup & ->).
      apply (proj2 (map_label_requirement_matches key value (Some labels_set))).
      apply Hmatch. exact Hlookup.
  - rewrite /LabelSelectorV.match_labels Forall_forall.
    split; intros Hmatch.
    + apply map_eq. intros key.
      rewrite lookup_empty.
      destruct (labels_map !! key) as [value|] eqn:Hlookup; last done.
      exfalso.
      specialize (Hmatch (map_label_requirement key value)).
      rewrite map_label_requirement_matches in Hmatch.
      assert (In (map_label_requirement key value)
        (map_requirements keys labels_map)) as Hin.
      { rewrite <-list_elem_of_In.
        apply (proj2 (elem_of_map_requirements _ _ _)).
        exists key, value. repeat split; try done.
        rewrite <-(elem_of_list_to_set (C:=gset go_string)).
        rewrite Hdom elem_of_dom. eauto. }
      specialize (Hmatch Hin).
      rewrite /LabelSelectorV.selected_label in Hmatch. discriminate.
    + subst labels_map.
      assert (keys = []) as ->.
      { destruct keys as [|key keys]; first done.
        exfalso. assert (key ∈
          list_to_set (C:=gset go_string) (key :: keys)) as Hkey.
        { Timeout 10 set_solver. }
        rewrite Hdom dom_empty elem_of_empty in Hkey. done. }
      intros requirement Hfalse. inversion Hfalse.
Qed.

Lemma expression_conversions_match apis requirements labels_set :
  Forall2 expression_converts apis requirements →
  selector_matches requirements labels_set ↔
    Forall (LabelSelectorV.requirement_matches labels_set) apis.
Proof.
  intros Hrelated. rewrite /selector_matches.
  induction Hrelated as [|api requirement apis requirements Hconvert _ IH];
    simpl; first done.
  split; intros Hall.
  - inversion Hall as [|? ? Hhead Htail]. constructor.
    + apply (proj1 (expression_converts_matches _ _ _ Hconvert)). exact Hhead.
    + apply (proj1 IH). exact Htail.
  - inversion Hall as [|? ? Hhead Htail]. constructor.
    + apply (proj2 (expression_converts_matches _ _ _ Hconvert)). exact Hhead.
    + apply (proj2 IH). exact Htail.
Qed.

End proof.
