From New.proof Require Import prelude empty_ffi.
From New.proof.map Require Import len for_range.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export
  v1 v1_label_selector_conversion.
From New.proof.kubernetes_types Require Import labelselector.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : v1.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

Lemma label_selector_matches_empty selector :
  LabelSelectorV.empty selector →
  ∀ labels_set,
    LabelSelectorV.matches selector labels_set ↔ everything_matches labels_set.
Proof.
  intros ([Hlabels_none|Hlabels_empty] & Hexpressions) labels_set.
  - rewrite /LabelSelectorV.matches /LabelSelectorV.match_labels
      Hlabels_none Hexpressions /everything_matches /=. done.
  - rewrite /LabelSelectorV.matches /LabelSelectorV.match_labels
      Hlabels_empty Hexpressions /everything_matches /=.
    destruct labels_set as [labels_set|]; simpl.
    + done.
    + split; [done|]. intros _. split; [done|constructor].
Qed.

Lemma wp_LabelSelectorAsSelector selector_l selector dq :
  {{{ "#Hinit" ∷ is_pkg_init v1 ∗
      "%Hvalid" ∷ ⌜ LabelSelectorV.valid selector ⌝ ∗
      "%Hextra_valid" ∷ ⌜ LabelSelectorV.extra_valid selector ⌝ ∗
      "Hselector" ∷ LabelSelectorV.deepown_l selector_l selector dq
  }}}
    @! v1.LabelSelectorAsSelector #selector_l
  {{{ converted, RET (#converted, #interface.nil);
      LabelSelectorV.deepown_l selector_l selector dq ∗
      is_selector converted (LabelSelectorV.matches selector)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct Hvalid as (Hlabels_valid & Hexpressions_valid).
  rename Hextra_valid into Hsize.
  iAssert (is_pkg_init labels) as "#Hlabels_init".
  { iPkgInit. }
  iDestruct "Hselector" as (selector_c) "[Hselector_l Hselector]".
  iDestruct (struct_fields_split (V:=v1.LabelSelector.t)
    with "Hselector_l") as "[Hselector_fields %Hselector_nonnull]".
  iNamedPrefix "Hselector_fields" "Hselector_field_".
  iNamedPrefix "Hselector" "Hselector_".
  wp_auto.
  rewrite -> bool_decide_false by exact Hselector_nonnull.
  wp_pures.
  destruct selector.(LabelSelectorV.MatchLabels') as [labels_map|]
    eqn:Hlabels_opt.
  all: lazymatch goal with
  | labels_map : gmap go_string go_string |- _ =>
      iDestruct "Hselector_Hdeepown_matchlabels_some" as
        (labels_map_c) "[Hlabels_map %Hlabels_map_c]";
      subst labels_map_c
  | _ =>
      assert (v1.LabelSelector.MatchLabels' selector_c = map.nil)
        as Hlabels_map_nil;
      [apply (proj2 Hselector_Hdeepown_matchlabels_none); done|]
  end.
  all: destruct selector.(LabelSelectorV.MatchExpressions') as [expressions|]
    eqn:Hexpressions_opt.
  all: lazymatch goal with
  | expressions : list LabelSelectorRequirementV.t |- _ =>
      iDestruct "Hselector_Hdeepown_matchexpressions_some" as
        (expressions_c) "Hexpressions";
      iEval (rewrite /deepown_list) in "Hexpressions";
      iDestruct "Hexpressions" as "[Hexpressions_sl Hexpressions]"
  | _ =>
      assert (v1.LabelSelector.MatchExpressions' selector_c = slice.nil)
        as Hexpressions_nil;
      [apply (proj2 Hselector_Hdeepown_matchexpressions_none); done|];
      pose (expressions := ([] : list LabelSelectorRequirementV.t));
      pose (expressions_c := ([] : list v1.LabelSelectorRequirement.t));
      iAssert (v1.LabelSelector.MatchExpressions' selector_c ↦*
        expressions_c)%I as "Hexpressions_sl";
      [rewrite Hexpressions_nil /expressions_c; iApply own_slice_nil|];
      iAssert (([∗ list] expression_c;expression ∈
        expressions_c;expressions,
        LabelSelectorRequirementV.deepown expression_c expression dq))%I
        as "Hexpressions";
      [rewrite /expressions_c /expressions big_sepL2_nil; done|]
  end.
  all: unfold LabelSelectorV.extra_valid in Hsize.
  all: rewrite Hlabels_opt /LabelSelectorV.match_expressions_list
    Hexpressions_opt /= in Hsize.
  all: try (rewrite Hlabels_opt /= in Hlabels_valid).
  all: try (rewrite /LabelSelectorV.match_expressions_list
    Hexpressions_opt /= in Hexpressions_valid).
  all: iDestruct (own_slice_len with "Hexpressions_sl") as
    %[Hexpressions_len Hexpressions_nonnegative].
  all: iDestruct (big_sepL2_length with "Hexpressions") as
    %Hexpressions_models_len.
  all: assert (sint.nat
      (slice.len (v1.LabelSelector.MatchExpressions' selector_c)) =
      length expressions) as Hexpressions_word_len by lia.
  all: wp_auto.
  all: lazymatch goal with
  | Hlabels_map_nil : _ = map.nil |- _ =>
      rewrite Hlabels_map_nil;
      wp_apply (wp_map_len_nil_resolved (K:=go_string) (V:=go_string)
        go.string go.string)
  | _ =>
      wp_apply (wp_map_len_resolved (K:=go_string) (V:=go_string)
        go.string go.string with "Hlabels_map");
      iIntros "Hlabels_map"
  end.
  all: try done.
  all: try (
    wp_bind (![go.PointerType apis_meta_v1.LabelSelector] (#ps_ptr))%E;
    wp_load;
    wp_pure;
    wp_bind (![go.SliceType apis_meta_v1.LabelSelectorRequirement]
      (StructFieldRef apis_meta_v1.LabelSelector "MatchExpressions"
        (#selector_l)))%E;
    wp_pure;
    wp_load;
    wp_auto;
    wp_if_destruct).
  all: lazymatch goal with
  | Hzero : word.add _ _ = W64 0 |- _ =>
      assert (size (default ∅ selector.(LabelSelectorV.MatchLabels')) +
        length expressions = 0)%nat as Hempty_sum by
        (rewrite Hlabels_opt /=; word);
      assert (length expressions = 0%nat) as Hexpressions_empty by lia;
      apply nil_length_inv in Hexpressions_empty;
      subst expressions
  | _ => idtac
  end.
  all: try lazymatch goal with
  | Hzero : word.add _ _ = W64 0,
      labels_map : gmap go_string go_string |- _ =>
      assert (size labels_map = 0%nat) as Hlabels_empty by
        (rewrite Hlabels_opt /= in Hempty_sum; lia);
      apply map_size_empty_inv in Hlabels_empty;
      subst labels_map
  | _ => idtac
  end.
  1: wp_bind (@! labels.Everything #())%E.
  1: wp_apply (wp_Everything with "[$]").
  1: iIntros (converted) "#Hconverted".
  1: wp_auto.
  1: iApply "HΦ".
  1: iSplitR "Hconverted".
  1: iCombineNamed "Hselector_field_*" as "Hselector_fields".
  1: iAssert (typed_pointsto_def selector_l selector_c dq)
    with "[Hselector_fields]" as "Hselector_l".
  1: { iNamed "Hselector_fields". simpl. rewrite /named.
       iFrame. }
  1: iDestruct (struct_fields_combine (V:=v1.LabelSelector.t)
    selector_l selector_c dq Hselector_nonnull with "Hselector_l") as
    "Hselector_l".
  1: iExists selector_c.
  1: iFrame "Hselector_l".
  1: rewrite /LabelSelectorV.deepown /named Hlabels_opt
    Hexpressions_opt /=.
  1: iFrame.
  1: iFrame "%".
  1: done.
  1: assert (∀ labels_set, everything_matches labels_set ↔
      LabelSelectorV.matches selector labels_set) as Hmatches.
  1: { intros labels_set. symmetry. apply label_selector_matches_empty.
       rewrite /LabelSelectorV.empty /LabelSelectorV.match_expressions_list
         Hlabels_opt Hexpressions_opt /=.
       split; [auto|done]. }
  1: iPoseProof (is_selector_ext converted everything_matches
    (LabelSelectorV.matches selector) Hmatches with "Hconverted") as
    "Hconverted'".
  1: (iExactEq "Hconverted'"; done).
  1: wp_apply (wp_map_len_resolved (K:=go_string) (V:=go_string)
    go.string go.string with "Hlabels_map").
  1: iIntros "Hlabels_map".
  1: wp_auto.
  1: wp_apply (wp_slice_make3 (V:=labels.Requirement.t)
    (t:=labels.Requirement)); first word.
  1: iIntros (requirements_sl) "(Hrequirements & Hrequirements_cap & %)".
  1: wp_auto.
  1: set P := (λ (keys : list go_string) (i : Z),
    ∃ (last_value last_key : go_string) (current_sl : slice.t)
      (entries : list (labels.Requirement.t * LabelRequirementV.t)),
      "Hv" ∷ v_ptr ↦ last_value ∗
      "Hk" ∷ k_ptr ↦ last_key ∗
      "Hrequirements_ptr" ∷ requirements_ptr ↦ current_sl ∗
      "Hrequirements" ∷ current_sl ↦* (fst <$> entries) ∗
      "Hrequirements_cap" ∷
        own_slice_cap labels.Requirement.t current_sl (DfracOwn 1) ∗
      "Hentries" ∷ ([∗ list] entry ∈ entries,
        label_requirement_rep entry.1 entry.2) ∗
      "%Hentries_pure" ∷ ⌜ snd <$> entries =
        map_requirements (take (Z.to_nat i) keys) labels_map ⌝)%I.
  1: wp_apply (wp_map_for_range_return_func
    (key_type:=go.string) P with "Hlabels_map"); first done.
  1: iIntros (keys) "%Hkeys".
  1: destruct Hkeys as (Hkeys_dom & Hkeys_len & Hkeys_nodup).
  1: iSplitL "v k requirements Hrequirements Hrequirements_cap".
  1: { iExists ""%go, ""%go, requirements_sl, [].
       rewrite /P fmap_nil take_0 /=.
       iFrame. done. }
  1: iSplitL "".
  1: { iModIntro. iIntros (i key value) "%Hiter Hloop".
       destruct Hiter as (Hi_bounds & Hkey_lookup & Hvalue_lookup).
       iDestruct "Hloop" as
         (last_value last_key current_sl entries)
         "(Hv & Hk & Hrequirements_ptr & Hrequirements &
          Hrequirements_cap & #Hentries & %Hentries_pure)".
       simpl subst'.
       wp_auto.
       wp_apply wp_slice_literal. iSplitR; first done.
       iIntros (value_sl) "[Hvalue_sl _]". wp_auto.
       assert (valid_label_name key ∧ valid_label_value value)
         as [Hkey_valid Hvalue_valid].
       { apply Hlabels_valid. exact Hvalue_lookup. }
       wp_apply (wp_NewRequirement with
         "[$Hlabels_init $Hvalue_sl]").
       { rewrite /valid_requirement_inputs /=.
         split_and!; try done.
         - constructor; [done|constructor].
         - right. left. done. }
       iIntros (requirement_l requirement_c)
         "(Hrequirement_l & #Hrequirement)".
       wp_auto.
       wp_apply wp_slice_literal. iSplitR; first done.
       iIntros (one_sl) "[Hone_sl _]". wp_auto.
       wp_apply (wp_slice_append with
         "[$Hrequirements $Hrequirements_cap $Hone_sl]").
       iIntros (current_sl')
         "(Hrequirements & Hrequirements_cap & Hone_sl)".
       wp_auto.
       iEval (simpl) in "Hrequirements".
       iEval (simpl) in "Hrequirement".
       iRight. iSplit; first done.
       iExists value, key, current_sl',
         (entries ++ [(requirement_c, map_label_requirement key value)]).
       iFrame.
       iSplit.
       { assert (<[sint.nat (W64 0):=requirement_c]>
             [(zero_val labels.Requirement.t)] = [requirement_c]) as Hone.
         { simpl. done. }
         iEval (rewrite Hone) in "Hrequirements".
         iExactEq "Hrequirements".
         rewrite /named. f_equal. rewrite fmap_app /=. done. }
       iSplit.
       { rewrite big_sepL_snoc /=.
         iFrame "#". }
       iPureIntro.
       rewrite fmap_app /= Hentries_pure.
       replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
       rewrite (take_S_r _ _ _ Hkey_lookup).
       symmetry. apply map_requirements_snoc. exact Hvalue_lookup. }
  1: iIntros "Hlabels_map Hloop".
  1: iDestruct "Hloop" as
    (last_value last_key map_requirements_sl map_entries)
    "(Hv & Hk & Hrequirements_ptr & Hrequirements &
     Hrequirements_cap & #Hmap_entries & %Hmap_entries_pure)".
  1: assert (snd <$> map_entries = map_requirements keys labels_map)
    as Hmap_entries_pure_all.
  1: { rewrite Hmap_entries_pure.
       replace (Z.to_nat (Z.of_nat (size labels_map))) with
         (length keys) by lia.
       assert (take (length keys) keys = keys) as Htake.
       { apply take_ge. lia. }
       rewrite Htake. done. }
  1: wp_auto.
  1: set I := (∃ (loop_i : w64)
      (current_expression_c : v1.LabelSelectorRequirement.t)
      (current_sl : slice.t)
      (expression_entries :
        list (labels.Requirement.t * LabelRequirementV.t)),
      i_ptr ↦ loop_i ∗
      expr_ptr ↦ current_expression_c ∗
      requirements_ptr ↦ current_sl ∗
      current_sl ↦* (fst <$> (map_entries ++ expression_entries)) ∗
      own_slice_cap labels.Requirement.t current_sl (DfracOwn 1) ∗
      ([∗ list] entry ∈ expression_entries,
        label_requirement_rep entry.1 entry.2) ∗
      v1.LabelSelector.MatchExpressions' selector_c ↦* expressions_c ∗
      ([∗ list] c;expression ∈ expressions_c;expressions,
        LabelSelectorRequirementV.deepown c expression dq) ∗
      ⌜ Forall2 expression_converts
          (take (sint.nat loop_i) expressions)
          (snd <$> expression_entries) ⌝ ∗
      ⌜ 0 ≤ sint.Z loop_i ≤ length expressions ⌝)%I.
  1: iAssert I with
    "[i expr Hrequirements_ptr Hrequirements Hrequirements_cap
      Hexpressions_sl Hexpressions]" as "Hloop".
  1: { iExists (W64 0), (zero_val v1.LabelSelectorRequirement.t),
         map_requirements_sl, [].
       rewrite fmap_app /= app_nil_r take_0.
       iFrame.
       iPureIntro. split; [constructor|word]. }
  1: wp_for "Hloop".
  1: iDestruct "Hloop" as
    "(Hi & Hexpr_ptr & Hrequirements_ptr & Hrequirements &
     Hrequirements_cap & #Hexpression_entries & Hexpressions_sl &
     Hexpressions & %Hexpression_entries_pure & %Hloop_bounds)".
  1: wp_auto.
  1: wp_if_destruct.
  1: destruct Hloop_bounds as [Hloop_nonnegative Hloop_upper].
  1: assert (0 ≤ sint.Z loop_i < length expressions) as Hloop_lt by word.
  1: list_elem expressions_c (sint.Z loop_i) as expression_c.
  1: list_elem expressions (sint.Z loop_i) as expression.
  1: assert (0 ≤ sint.Z loop_i <
      sint.Z (slice.len (v1.LabelSelector.MatchExpressions' selector_c)))
    as Hslice_bounds by word.
  1: wp_pures.
  1: rewrite decide_True; try exact Hslice_bounds.
  1: wp_apply (wp_load_slice_index with "[$Hexpressions_sl]");
    [word|iPureIntro; exact Hexpression_c_lookup|].
  1: iIntros "Hexpressions_sl".
  1: wp_auto.
  1: iDestruct (big_sepL2_lookup_acc with "Hexpressions") as
    "[Hexpression Hrestore_expressions]";
    [exact Hexpression_c_lookup|exact Hexpression_lookup|].
  1: iNamedPrefix "Hexpression" "Hexpression_".
  1: assert (LabelSelectorRequirementV.valid expression)
    as Hexpression_valid.
  1: { rewrite Forall_forall in Hexpressions_valid.
       apply Hexpressions_valid.
       rewrite <-list_elem_of_In.
       eapply list_elem_of_lookup_2. exact Hexpression_lookup. }
  1: pose proof Hexpression_valid as Hvalid_expression.
  1: destruct Hexpression_valid as
    (Hoperator & Hin_values & Hexists_values & Hkey_valid & Hvalues_valid).
  1: destruct Hoperator as
    [Hoperator|[Hoperator|[Hoperator|Hoperator]]].
  all: try (rewrite Hexpression_Hdeepown_operator Hoperator; wp_auto).
  all: try lazymatch goal with
  | Hoperator : LabelSelectorRequirementV.Operator' ?expression = _ |- _ =>
      destruct expression.(LabelSelectorRequirementV.Values') as [values|]
        eqn:Hvalues_opt
  end.
  all: try lazymatch goal with
  | Hvalues_opt : LabelSelectorRequirementV.Values' ?expression = Some ?values
      |- _ =>
      iRename "Hexpression_Hdeepown_values_some" into "Hsource_values";
      rewrite /LabelSelectorRequirementV.values_list Hvalues_opt /=
        in Hvalues_valid Hin_values Hexists_values
  | Hvalues_opt : LabelSelectorRequirementV.Values' ?expression = None
      |- _ =>
      rewrite /LabelSelectorRequirementV.values_list Hvalues_opt /=
        in Hvalues_valid Hin_values Hexists_values
  end.
  1: iPoseProof (own_slice_nil (V:=go_string) (DfracOwn 1))
    as "Hcopied_values".
  1: iPoseProof (own_slice_cap_nil (V:=go_string))
    as "Hcopied_values_cap".
  1: wp_apply (wp_slice_append (V:=go_string) (t:=go.string)
    (st:=go.SliceType go.string)
    slice.nil [] (v1.LabelSelectorRequirement.Values' expression_c)
    values dq with
    "[$Hcopied_values $Hcopied_values_cap $Hsource_values]").
  1: iIntros (copied_values_sl)
    "(Hcopied_values_out & Hcopied_values_cap_out & Hsource_values_out)".
  1: iEval (simpl) in "Hcopied_values_out".
  1: wp_auto.
  1: rewrite Hexpression_Hdeepown_key.
  1: wp_apply (wp_NewRequirement with
    "[$Hlabels_init $Hcopied_values_out]").
  1: { rewrite /valid_requirement_inputs /=.
       split_and!; try done.
       left. split; [left; done|].
       apply Hin_values. left. exact Hoperator. }
  1: iIntros (requirement_l requirement_c')
    "(Hrequirement_l & #Hrequirement)".
  1: wp_auto.
  1: wp_apply wp_slice_literal.
  1: iSplitR; first done.
  1: iIntros (one_requirement_l) "[Hone_requirement _]".
  1: wp_auto.
  1: wp_apply (wp_slice_append with
    "[$Hrequirements $Hrequirements_cap $Hone_requirement]").
  1: iIntros (current_sl')
    "(Hrequirements_out & Hrequirements_cap_out & Hone_requirement_out)".
  1: wp_auto.
  1: set (new_requirement := LabelRequirementV.mk
    expression.(LabelSelectorRequirementV.Key') "in"%go values).
  1: assert (expression_converts expression new_requirement)
    as Hexpression_converts.
  1: { rewrite /expression_converts /new_requirement /= Hoperator
         /LabelSelectorRequirementV.values_list Hvalues_opt /=.
       tauto. }
  1: iAssert (LabelSelectorRequirementV.deepown expression_c expression dq)
    with "[Hsource_values_out]" as "Hexpression".
  1: { rewrite /LabelSelectorRequirementV.deepown /named Hvalues_opt /=.
       iFrame. iPureIntro. split_and!; done. }
  1: iSpecialize ("Hrestore_expressions" with "Hexpression").
  1: assert (<[sint.nat (W64 0):=requirement_c']>
      [(zero_val labels.Requirement.t)] = [requirement_c'])
    as Hone_requirement.
  1: { simpl. done. }
  1: iEval (rewrite Hone_requirement) in "Hrequirements_out".
  1: iApply wp_for_post_do.
  1: wp_auto.
  1: iFrame "HΦ Hselector_field_MatchLabels
    Hselector_field_MatchExpressions Hlabels_map Hv Hk".
  1: iExists (word.add loop_i (W64 1)), expression_c, current_sl',
    (expression_entries ++ [(requirement_c', new_requirement)]).
  1: iFrame "Hi Hexpr_ptr Hrequirements_ptr Hrequirements_cap_out
    Hexpressions_sl Hrestore_expressions".
  1: iSplitL "Hrequirements_out".
  1: { iExactEq "Hrequirements_out".
       f_equal. rewrite !fmap_app /=. symmetry. apply app_assoc. }
  1: iSplit.
  1: { rewrite big_sepL_snoc /=. iFrame "#". }
  1: iSplit; first iFrame.
  1: iPureIntro.
  1: replace (sint.nat (word.add loop_i (W64 1))) with
    (S (sint.nat loop_i)) by word.
  1: rewrite (take_S_r _ _ _ Hexpression_lookup) fmap_app /=.
  1: apply Forall2_app; [exact Hexpression_entries_pure|].
  1: constructor; [exact Hexpression_converts|constructor].
  1: word.
  1: (exfalso; apply (Hin_values (or_introl Hoperator))).
  1: done.

  Ltac finish_expression mapped_operator values source_sl frac valid_expression :=
    let copied_values_sl := fresh "copied_values_sl" in
    let requirement_l := fresh "requirement_l" in
    let requirement_c := fresh "requirement_c" in
    let one_requirement_l := fresh "one_requirement_l" in
    let current_sl_next := fresh "current_sl" in
    let values_nil := fresh "Hvalues_nil" in
    lazymatch goal with
    | Hvalues_opt : LabelSelectorRequirementV.Values' ?expression = _,
      Hexpression_Hdeepown_values_none :
        v1.LabelSelectorRequirement.Values' ?expression_c = slice.nil ↔ _,
      Hexpression_Hdeepown_key :
        v1.LabelSelectorRequirement.Key' ?expression_c = _,
      Hoperator : LabelSelectorRequirementV.Operator' ?expression = _,
      Hin_values : _, Hexists_values : _, Hkey_valid : _,
      Hvalues_valid : _,
      Hexpression_entries_pure :
        Forall2 expression_converts (take (sint.nat ?loop_i) ?expressions)
          (snd <$> ?expression_entries),
      Hexpression_lookup : ?expressions !! sint.nat ?loop_i = Some ?expression
      |- _ =>
    lazymatch type of Hvalues_opt with
    | LabelSelectorRequirementV.Values' expression = None =>
        assert (v1.LabelSelectorRequirement.Values' expression_c = slice.nil)
          as values_nil;
        [apply (proj2 Hexpression_Hdeepown_values_none); done|];
        rewrite values_nil;
        iAssert (slice.nil ↦*{frac} ([] : list go_string))%I
          as "Hsource_values";
        [iApply own_slice_nil|]
    | _ => idtac
    end;
    set (new_requirement := LabelRequirementV.mk
      expression.(LabelSelectorRequirementV.Key') mapped_operator values);
    assert (expression_converts expression new_requirement)
      as Hexpression_converts;
    [rewrite /expression_converts /new_requirement /= Hoperator
       /LabelSelectorRequirementV.values_list Hvalues_opt /=;
     split; [done|]; split; [done|];
     first [left; split; done
       | right; left; split; done
       | right; right; left; split; done
       | right; right; right; split; done]|];
    pose proof (expression_converts_valid_inputs _ _ valid_expression
      Hexpression_converts) as Hvalid_inputs;
    iPoseProof (own_slice_nil (V:=go_string) (DfracOwn 1))
      as "Hcopied_values";
    iPoseProof (own_slice_cap_nil (V:=go_string))
      as "Hcopied_values_cap";
    iAssert (slice.nil ↦* ([] : list go_string) ∗
      own_slice_cap go_string slice.nil (DfracOwn 1) ∗
      source_sl ↦*{frac} values)%I
      with "[Hcopied_values Hcopied_values_cap Hsource_values]"
      as "Happend_values";
    [iSplitL "Hcopied_values"; [iExact "Hcopied_values"|];
     iSplitL "Hcopied_values_cap"; [iExact "Hcopied_values_cap"|];
     lazymatch type of Hvalues_opt with
     | LabelSelectorRequirementV.Values' expression = None =>
         iExact "Hsource_values"
     | _ => iExact "Hsource_values"
     end|];
    wp_apply (wp_slice_append (V:=go_string) (t:=go.string)
      (st:=go.SliceType go.string)
      slice.nil [] source_sl
      values frac with "Happend_values");
    iIntros (copied_values_sl)
      "(Hcopied_values_out & Hcopied_values_cap_out & Hsource_values_out)";
    iEval (simpl) in "Hcopied_values_out";
    wp_auto;
    rewrite Hexpression_Hdeepown_key;
    wp_apply (wp_NewRequirement with
      "[$Hlabels_init $Hcopied_values_out]");
    [exact Hvalid_inputs|];
    iIntros (requirement_l requirement_c)
      "(Hrequirement_l & #Hrequirement)";
    wp_auto;
    wp_apply wp_slice_literal;
    iSplitR; [done|];
    iIntros (one_requirement_l) "[Hone_requirement _]";
    wp_auto;
    wp_apply (wp_slice_append with
      "[$Hrequirements $Hrequirements_cap $Hone_requirement]");
    iIntros (current_sl_next)
      "(Hrequirements_out & Hrequirements_cap_out & Hone_requirement_out)";
    wp_auto;
    iAssert (LabelSelectorRequirementV.deepown expression_c expression frac)
      with "[Hsource_values_out]" as "Hexpression";
    [rewrite /LabelSelectorRequirementV.deepown /named Hvalues_opt /=;
     iFrame; iPureIntro; split_and!; done|];
    iSpecialize ("Hrestore_expressions" with "Hexpression");
    assert (<[sint.nat (W64 0):=requirement_c]>
        [(zero_val labels.Requirement.t)] = [requirement_c])
      as Hone_requirement;
    [simpl; done|];
    iEval (rewrite Hone_requirement) in "Hrequirements_out";
    iApply wp_for_post_do;
    wp_auto;
    iFrame "HΦ Hselector_field_MatchLabels
      Hselector_field_MatchExpressions";
    try iFrame "Hv";
    try iFrame "Hk";
    try iFrame "Hlabels_map";
    iExists (word.add loop_i (W64 1)), expression_c, current_sl_next,
      (expression_entries ++ [(requirement_c, new_requirement)]);
    iFrame "Hi Hexpr_ptr Hrequirements_ptr Hrequirements_cap_out
      Hexpressions_sl Hrestore_expressions";
    iSplitL "Hrequirements_out";
    [iExactEq "Hrequirements_out";
     f_equal; rewrite !fmap_app /=;
     first [done | (symmetry; apply app_assoc)]|];
    iSplit;
    [rewrite big_sepL_snoc /=; iFrame "#"|];
    iSplit; [iFrame|];
    iPureIntro;
    [replace (sint.nat (word.add loop_i (W64 1))) with
       (S (sint.nat loop_i)) by word;
     rewrite (take_S_r _ _ _ Hexpression_lookup) fmap_app /=;
     apply Forall2_app;
     [exact Hexpression_entries_pure|];
     constructor;
     [exact Hexpression_converts|constructor]
    |word]
    end.

  1: finish_expression "notin"%go values
    (v1.LabelSelectorRequirement.Values' expression_c) dq Hvalid_expression.
  1: (exfalso; apply (Hin_values (or_intror Hoperator))).
  1: done.
  1: finish_expression "exists"%go values
    (v1.LabelSelectorRequirement.Values' expression_c) dq Hvalid_expression.
  1: finish_expression "exists"%go ([] : list go_string) slice.nil dq
    Hvalid_expression.
  1: finish_expression "!"%go values
    (v1.LabelSelectorRequirement.Values' expression_c) dq Hvalid_expression.
  1: finish_expression "!"%go ([] : list go_string) slice.nil dq
    Hvalid_expression.

  1: assert (sint.nat loop_i = length expressions) as Hloop_done by word.
  1: assert (take (sint.nat loop_i) expressions = expressions) as Htake_all.
  1: { apply take_ge. lia. }
  1: rewrite Htake_all in Hexpression_entries_pure.
  1: assert (length (map_requirements keys labels_map) = length keys)
    as Hmap_requirements_len.
  1: { apply map_requirements_length. intros key Hkey.
       assert (key ∈ dom labels_map) as Hkey_dom.
       { rewrite <- list_elem_of_In in Hkey.
         rewrite <- Hkeys_dom. rewrite elem_of_list_to_set. exact Hkey. }
       rewrite elem_of_dom in Hkey_dom. exact Hkey_dom. }
  1: pose proof (f_equal (@length LabelRequirementV.t)
    Hmap_entries_pure_all) as Hmap_entries_len.
  1: rewrite !length_fmap Hmap_requirements_len Hkeys_len
    in Hmap_entries_len.
  1: pose proof (Forall2_length Hexpression_entries_pure)
    as Hexpression_entries_len.
  1: rewrite length_fmap in Hexpression_entries_len.
  1: assert (Forall LabelRequirementV.supported
      (snd <$> (map_entries ++ expression_entries))) as Hsupported.
  1: { rewrite fmap_app. apply Forall_app. split.
       - rewrite Hmap_entries_pure_all. apply map_requirements_supported.
       - eapply expression_conversions_supported.
         exact Hexpression_entries_pure. }
  1: assert (Z.of_nat (length (map_entries ++ expression_entries)) ≤
      2 ^ 63 - 1) as Hentries_size.
  1: { rewrite length_app Hmap_entries_len.
       rewrite <- Hexpression_entries_len. lia. }
  1: iAssert (by_key_contents current_sl
      (map_entries ++ expression_entries))
    with "[Hrequirements Hmap_entries Hexpression_entries]"
    as "Hrequirements_contents".
  1: { rewrite /by_key_contents big_sepL_app.
       iFrame "Hrequirements". iFrame "#". }
  1: wp_apply wp_NewSelector.
  1: iIntros (empty_selector) "[%Hempty_selector #Hempty_selector_rep]".
  1: rewrite Hempty_selector.
  1: wp_auto.
  1: wp_apply (wp_empty_internalSelector__Add current_sl
    (map_entries ++ expression_entries)
    with "[$Hlabels_init $Hrequirements_contents]"); first exact Hentries_size.
  1: exact Hsupported.
  1: iIntros (converted) "#Hconverted".
  1: wp_auto.
  1: iApply "HΦ".
  1: iSplitR "Hconverted".
  1: iCombineNamed "Hselector_field_*" as "Hselector_fields".
  1: iAssert (typed_pointsto_def selector_l selector_c dq)
    with "[Hselector_fields]" as "Hselector_l".
  1: { iNamed "Hselector_fields". simpl. rewrite /named.
       iFrame; try done. }
  1: iDestruct (struct_fields_combine (V:=v1.LabelSelector.t)
    selector_l selector_c dq Hselector_nonnull with "Hselector_l") as
    "Hselector_l".
  1: iExists selector_c.
  1: iFrame "Hselector_l".
  1: rewrite /LabelSelectorV.deepown /named Hlabels_opt
    Hexpressions_opt /=.
  1: iFrame.
  1: iFrame "%".
  1: done.
  1: assert (∀ labels_set,
      selector_matches (snd <$> (map_entries ++ expression_entries))
        labels_set ↔ LabelSelectorV.matches selector labels_set)
    as Hmatches.
  1: { intros labels_set.
       rewrite fmap_app Hmap_entries_pure_all /selector_matches Forall_app.
       change ((selector_matches (map_requirements keys labels_map)
           labels_set ∧
         selector_matches (snd <$> expression_entries) labels_set) ↔
         LabelSelectorV.matches selector labels_set).
       rewrite (map_requirements_match keys labels_map labels_set Hkeys_dom).
       rewrite (expression_conversions_match expressions
         (snd <$> expression_entries) labels_set
         Hexpression_entries_pure).
       rewrite /LabelSelectorV.matches
         /LabelSelectorV.match_expressions_list Hlabels_opt
         Hexpressions_opt /=. done. }
  1: iPoseProof (is_selector_ext converted
    (selector_matches (snd <$> (map_entries ++ expression_entries)))
    (LabelSelectorV.matches selector) Hmatches with "Hconverted") as
    "Hconverted'".
  1: iExact "Hconverted'".

  1: wp_bind (@! labels.Everything #())%E.
  1: wp_apply (wp_Everything with "[$]").
  1: iIntros (converted) "#Hconverted".
  1: wp_auto.
  1: iApply "HΦ".
  1: iSplitR "Hconverted".
  1: iCombineNamed "Hselector_field_*" as "Hselector_fields".
  1: iAssert (typed_pointsto_def selector_l selector_c dq)
    with "[Hselector_fields]" as "Hselector_l".
  1: { iNamed "Hselector_fields". simpl. rewrite /named.
       iFrame; try done. }
  1: iDestruct (struct_fields_combine (V:=v1.LabelSelector.t)
    selector_l selector_c dq Hselector_nonnull with "Hselector_l") as
    "Hselector_l".
  1: iExists selector_c.
  1: iFrame "Hselector_l".
  1: rewrite /LabelSelectorV.deepown /named Hlabels_opt
    Hexpressions_opt /=.
  1: iFrame.
  1: iFrame "%".
  1: done.
  1: assert (∀ labels_set, everything_matches labels_set ↔
      LabelSelectorV.matches selector labels_set) as Hmatches.
  1: { intros labels_set. symmetry. apply label_selector_matches_empty.
       rewrite /LabelSelectorV.empty /LabelSelectorV.match_expressions_list
         Hlabels_opt Hexpressions_opt /=. split; [auto|done]. }
  1: iPoseProof (is_selector_ext converted everything_matches
    (LabelSelectorV.matches selector) Hmatches with "Hconverted") as
    "Hconverted'".
  1: iExact "Hconverted'".

  1: wp_apply (wp_map_len_resolved (K:=go_string) (V:=go_string)
    go.string go.string with "Hlabels_map").
  1: iIntros "Hlabels_map".
  1: wp_auto.
  1: unfold expressions in Hexpressions_word_len.
  1: simpl in Hexpressions_word_len.
  1: wp_apply (wp_slice_make3 (V:=labels.Requirement.t)
    (t:=labels.Requirement)); first word.
  1: iIntros (requirements_sl) "(Hrequirements & Hrequirements_cap & %)".
  1: wp_auto.
  1: set P := (λ (keys : list go_string) (i : Z),
    ∃ (last_value last_key : go_string) (current_sl : slice.t)
      (entries : list (labels.Requirement.t * LabelRequirementV.t)),
      "Hv" ∷ v_ptr ↦ last_value ∗
      "Hk" ∷ k_ptr ↦ last_key ∗
      "Hrequirements_ptr" ∷ requirements_ptr ↦ current_sl ∗
      "Hrequirements" ∷ current_sl ↦* (fst <$> entries) ∗
      "Hrequirements_cap" ∷
        own_slice_cap labels.Requirement.t current_sl (DfracOwn 1) ∗
      "Hentries" ∷ ([∗ list] entry ∈ entries,
        label_requirement_rep entry.1 entry.2) ∗
      "%Hentries_pure" ∷ ⌜ snd <$> entries =
        map_requirements (take (Z.to_nat i) keys) labels_map ⌝)%I.
  1: wp_apply (wp_map_for_range_return_func
    (key_type:=go.string) P with "Hlabels_map"); first done.
  1: iIntros (keys) "%Hkeys".
  1: destruct Hkeys as (Hkeys_dom & Hkeys_len & Hkeys_nodup).
  1: iSplitL "v k requirements Hrequirements Hrequirements_cap".
  1: { iExists ""%go, ""%go, requirements_sl, [].
       rewrite /P fmap_nil take_0 /=. iFrame. done. }
  1: iSplitL "".
  1: { iModIntro. iIntros (i key value) "%Hiter Hloop".
       destruct Hiter as (Hi_bounds & Hkey_lookup & Hvalue_lookup).
       iDestruct "Hloop" as
         (last_value last_key current_sl entries)
         "(Hv & Hk & Hrequirements_ptr & Hrequirements &
          Hrequirements_cap & #Hentries & %Hentries_pure)".
       simpl subst'. wp_auto.
       wp_apply wp_slice_literal. iSplitR; first done.
       iIntros (value_sl) "[Hvalue_sl _]". wp_auto.
       assert (valid_label_name key ∧ valid_label_value value)
         as [Hkey_valid Hvalue_valid].
       { apply Hlabels_valid. exact Hvalue_lookup. }
       wp_apply (wp_NewRequirement with
         "[$Hlabels_init $Hvalue_sl]").
       { rewrite /valid_requirement_inputs /=.
         split_and!; try done.
         - constructor; [done|constructor].
         - right. left. done. }
       iIntros (requirement_l requirement_c)
         "(Hrequirement_l & #Hrequirement)".
       wp_auto.
       wp_apply wp_slice_literal. iSplitR; first done.
       iIntros (one_sl) "[Hone_sl _]". wp_auto.
       wp_apply (wp_slice_append with
         "[$Hrequirements $Hrequirements_cap $Hone_sl]").
       iIntros (current_sl')
         "(Hrequirements & Hrequirements_cap & Hone_sl)".
       wp_auto.
       iEval (simpl) in "Hrequirements".
       iEval (simpl) in "Hrequirement".
       iRight. iSplit; first done.
       iExists value, key, current_sl',
         (entries ++ [(requirement_c, map_label_requirement key value)]).
       iFrame.
       iSplit.
       { assert (<[sint.nat (W64 0):=requirement_c]>
             [(zero_val labels.Requirement.t)] = [requirement_c]) as Hone.
         { simpl. done. }
         iEval (rewrite Hone) in "Hrequirements".
         iExactEq "Hrequirements".
         rewrite /named. f_equal. rewrite fmap_app /=. done. }
       iSplit.
       { rewrite big_sepL_snoc /=. iFrame "#". }
       iPureIntro.
       rewrite fmap_app /= Hentries_pure.
       replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
       rewrite (take_S_r _ _ _ Hkey_lookup).
       symmetry. apply map_requirements_snoc. exact Hvalue_lookup. }
  1: iIntros "Hlabels_map Hloop".
  1: iDestruct "Hloop" as
    (last_value last_key map_requirements_sl map_entries)
    "(Hv & Hk & Hrequirements_ptr & Hrequirements &
     Hrequirements_cap & #Hmap_entries & %Hmap_entries_pure)".
  1: assert (snd <$> map_entries = map_requirements keys labels_map)
    as Hmap_entries_pure_all.
  1: { rewrite Hmap_entries_pure.
       replace (Z.to_nat (Z.of_nat (size labels_map))) with
         (length keys) by lia.
       assert (take (length keys) keys = keys) as Htake.
       { apply take_ge. lia. }
       rewrite Htake. done. }
  1: wp_auto.
  1: set I := (∃ (loop_i : w64)
      (current_expression_c : v1.LabelSelectorRequirement.t)
      (current_sl : slice.t)
      (expression_entries :
        list (labels.Requirement.t * LabelRequirementV.t)),
      i_ptr ↦ loop_i ∗
      expr_ptr ↦ current_expression_c ∗
      requirements_ptr ↦ current_sl ∗
      current_sl ↦* (fst <$> (map_entries ++ expression_entries)) ∗
      own_slice_cap labels.Requirement.t current_sl (DfracOwn 1) ∗
      ([∗ list] entry ∈ expression_entries,
        label_requirement_rep entry.1 entry.2) ∗
      v1.LabelSelector.MatchExpressions' selector_c ↦* expressions_c ∗
      ([∗ list] c;expression ∈ expressions_c;expressions,
        LabelSelectorRequirementV.deepown c expression dq) ∗
      ⌜ Forall2 expression_converts
          (take (sint.nat loop_i) expressions)
          (snd <$> expression_entries) ⌝ ∗
      ⌜ 0 ≤ sint.Z loop_i ≤ length expressions ⌝)%I.
  1: iAssert I with
    "[i expr Hrequirements_ptr Hrequirements Hrequirements_cap
      Hexpressions_sl Hexpressions]" as "Hloop".
  1: { iExists (W64 0), (zero_val v1.LabelSelectorRequirement.t),
         map_requirements_sl, [].
       rewrite fmap_app /= app_nil_r take_0.
       unfold expressions, expressions_c. simpl.
       iFrame "i expr Hrequirements_ptr Hrequirements Hrequirements_cap
         Hexpressions_sl".
       all: done. }
  1: try iClear "Hexpressions_sl Hexpressions".
  1: wp_for "Hloop".
  1: iDestruct "Hloop" as
    "(Hi & Hexpr_ptr & Hrequirements_ptr & Hrequirements &
     Hrequirements_cap & #Hexpression_entries & Hexpressions_sl &
     Hexpressions & %Hexpression_entries_pure & %Hloop_bounds)".
  1: wp_auto.
  1: wp_if_destruct.
  1: exfalso; word.
  1: unfold expressions in Hexpression_entries_pure.
  1: rewrite take_nil in Hexpression_entries_pure.
  1: assert (expression_entries = []) as ->.
  1: { apply (fmap_eq_nil snd).
       eapply Forall2_nil_left. exact Hexpression_entries_pure. }
  1: assert (snd <$> map_entries = map_requirements keys labels_map)
    as Hmap_entries_all by exact Hmap_entries_pure_all.
  1: assert (length (map_requirements keys labels_map) = length keys)
    as Hmap_requirements_len.
  1: { apply map_requirements_length. intros key Hkey.
       rewrite <- list_elem_of_In in Hkey.
       assert (key ∈ dom labels_map) as Hkey_dom.
       { rewrite <- Hkeys_dom. rewrite elem_of_list_to_set. exact Hkey. }
       rewrite elem_of_dom in Hkey_dom. exact Hkey_dom. }
  1: pose proof (f_equal (@length LabelRequirementV.t)
    Hmap_entries_all) as Hmap_entries_len.
  1: rewrite !length_fmap Hmap_requirements_len Hkeys_len
    in Hmap_entries_len.
  1: assert (Forall LabelRequirementV.supported (snd <$> map_entries))
    as Hsupported by
      (rewrite Hmap_entries_all; apply map_requirements_supported).
  1: assert (Z.of_nat (length map_entries) ≤ 2 ^ 63 - 1)
    as Hentries_size by (rewrite Hmap_entries_len; lia).
  1: iEval (rewrite app_nil_r) in "Hrequirements".
  1: iAssert (by_key_contents current_sl map_entries)
    with "[Hrequirements Hmap_entries]" as "Hrequirements_contents".
  1: { rewrite /by_key_contents. iFrame "Hrequirements". iFrame "#". }
  1: wp_apply wp_NewSelector.
  1: iIntros (empty_selector) "[%Hempty_selector #Hempty_selector_rep]".
  1: rewrite Hempty_selector.
  1: wp_auto.
  1: wp_apply (wp_empty_internalSelector__Add current_sl map_entries
    with "[$Hlabels_init $Hrequirements_contents]"); first exact Hentries_size.
  1: exact Hsupported.
  1: iIntros (converted) "#Hconverted".
  1: wp_auto.
  1: iApply "HΦ".
  1: iSplitR "Hconverted".
  1: iCombineNamed "Hselector_field_*" as "Hselector_fields".
  1: iAssert (typed_pointsto_def selector_l selector_c dq)
    with "[Hselector_fields]" as "Hselector_l".
  1: { iNamed "Hselector_fields". simpl. rewrite /named.
       iFrame; try done. }
  1: iDestruct (struct_fields_combine (V:=v1.LabelSelector.t)
    selector_l selector_c dq Hselector_nonnull with "Hselector_l") as
    "Hselector_l".
  1: iExists selector_c.
  1: iFrame "Hselector_l".
  1: rewrite /LabelSelectorV.deepown /named Hlabels_opt
    Hexpressions_opt /=.
  1: iFrame.
  1: iFrame "%".
  1: done.
  1: assert (∀ labels_set, selector_matches (snd <$> map_entries) labels_set ↔
      LabelSelectorV.matches selector labels_set) as Hmatches.
  1: { intros labels_set. rewrite Hmap_entries_all.
       rewrite (map_requirements_match keys labels_map labels_set Hkeys_dom).
       rewrite /LabelSelectorV.matches
         /LabelSelectorV.match_expressions_list Hlabels_opt
         Hexpressions_opt /=.
       split.
       - intros Hmatch. split; [exact Hmatch|constructor].
       - intros [Hmatch _]. exact Hmatch. }
  1: iPoseProof (is_selector_ext converted
    (selector_matches (snd <$> map_entries))
    (LabelSelectorV.matches selector) Hmatches with "Hconverted") as
    "Hconverted'".
  1: iExact "Hconverted'".
  all: wp_if_destruct.

  1: assert (length expressions = 0%nat) as Hexpressions_empty by word.
  1: apply nil_length_inv in Hexpressions_empty.
  1: subst expressions.
  1: wp_bind (@! labels.Everything #())%E.
  1: wp_apply (wp_Everything with "[$]").
  1: iIntros (converted) "#Hconverted".
  1: wp_auto.
  1: iApply "HΦ".
  1: iSplitR "Hconverted".
  1: iCombineNamed "Hselector_field_*" as "Hselector_fields".
  1: iAssert (typed_pointsto_def selector_l selector_c dq)
    with "[Hselector_fields]" as "Hselector_l".
  1: { iNamed "Hselector_fields". simpl.
       rewrite /named Hlabels_map_nil. iFrame. }
  1: iDestruct (struct_fields_combine (V:=v1.LabelSelector.t)
    selector_l selector_c dq Hselector_nonnull with "Hselector_l") as
    "Hselector_l".
  1: iExists selector_c.
  1: iFrame "Hselector_l".
  1: rewrite /LabelSelectorV.deepown /named Hlabels_opt
    Hexpressions_opt /=.
  1: iFrame.
  1: iFrame "%".
  1: assert (∀ labels_set, everything_matches labels_set ↔
      LabelSelectorV.matches selector labels_set) as Hmatches.
  1: { intros labels_set. symmetry. apply label_selector_matches_empty.
       rewrite /LabelSelectorV.empty /LabelSelectorV.match_expressions_list
         Hlabels_opt Hexpressions_opt /=. split; [auto|done]. }
  1: iPoseProof (is_selector_ext converted everything_matches
    (LabelSelectorV.matches selector) Hmatches with "Hconverted") as
    "Hconverted'".
  1: iExact "Hconverted'".

  3: unfold expressions in Hexpressions_word_len.
  3: simpl in Hexpressions_word_len.
  3: exfalso; word.

  2: wp_bind (@! labels.Everything #())%E.
  2: wp_apply (wp_Everything with "[$]").
  2: iIntros (converted) "#Hconverted".
  2: wp_auto.
  2: iApply "HΦ".
  2: iSplitR "Hconverted".
  2: iCombineNamed "Hselector_field_*" as "Hselector_fields".
  2: iAssert (typed_pointsto_def selector_l selector_c dq)
    with "[Hselector_fields]" as "Hselector_l".
  2: { iNamed "Hselector_fields". simpl.
       rewrite /named Hlabels_map_nil. iFrame. }
  2: iDestruct (struct_fields_combine (V:=v1.LabelSelector.t)
    selector_l selector_c dq Hselector_nonnull with "Hselector_l") as
    "Hselector_l".
  2: iExists selector_c.
  2: iFrame "Hselector_l".
  2: rewrite /LabelSelectorV.deepown /named Hlabels_opt
    Hexpressions_opt /=.
  2: iFrame.
  2: iFrame "%".
  2: assert (∀ labels_set, everything_matches labels_set ↔
      LabelSelectorV.matches selector labels_set) as Hmatches.
  2: { intros labels_set. symmetry. apply label_selector_matches_empty.
       rewrite /LabelSelectorV.empty /LabelSelectorV.match_expressions_list
         Hlabels_opt Hexpressions_opt /=. split; [auto|done]. }
  2: iPoseProof (is_selector_ext converted everything_matches
    (LabelSelectorV.matches selector) Hmatches with "Hconverted") as
    "Hconverted'".
  2: iExact "Hconverted'".

  1: wp_apply (wp_map_len_nil_resolved (K:=go_string) (V:=go_string)
    go.string go.string).
  1: wp_pures.
  1: wp_apply (wp_slice_make3 (V:=labels.Requirement.t)
    (t:=labels.Requirement)); first word.
  1: iIntros (requirements_sl) "(Hrequirements & Hrequirements_cap & %)".
  1: wp_auto.
  1: wp_apply (wp_map_for_range_nil go.string go.string).
  1: wp_pures.
  1: set I := (∃ (loop_i : w64)
      (current_expression_c : v1.LabelSelectorRequirement.t)
      (current_sl : slice.t)
      (expression_entries :
        list (labels.Requirement.t * LabelRequirementV.t)),
      i_ptr ↦ loop_i ∗
      expr_ptr ↦ current_expression_c ∗
      requirements_ptr ↦ current_sl ∗
      current_sl ↦* (fst <$> expression_entries) ∗
      own_slice_cap labels.Requirement.t current_sl (DfracOwn 1) ∗
      ([∗ list] entry ∈ expression_entries,
        label_requirement_rep entry.1 entry.2) ∗
      v1.LabelSelector.MatchExpressions' selector_c ↦* expressions_c ∗
      ([∗ list] c;expression ∈ expressions_c;expressions,
        LabelSelectorRequirementV.deepown c expression dq) ∗
      ⌜ Forall2 expression_converts
          (take (sint.nat loop_i) expressions)
          (snd <$> expression_entries) ⌝ ∗
      ⌜ 0 ≤ sint.Z loop_i ≤ length expressions ⌝)%I.
  1: iAssert I with
    "[i expr requirements Hrequirements Hrequirements_cap
      Hexpressions_sl Hexpressions]" as "Hloop".
  1: { iExists (W64 0), (zero_val v1.LabelSelectorRequirement.t),
         requirements_sl, [].
       rewrite take_0 /=.
       iFrame. iPureIntro. split; [constructor|word]. }
  1: wp_for "Hloop".
  1: iDestruct "Hloop" as
    "(Hi & Hexpr_ptr & Hrequirements_ptr & Hrequirements &
     Hrequirements_cap & #Hexpression_entries & Hexpressions_sl &
     Hexpressions & %Hexpression_entries_pure & %Hloop_bounds)".
  1: wp_auto.
  1: wp_if_destruct.
  1: destruct Hloop_bounds as [Hloop_nonnegative Hloop_upper].
  1: assert (0 ≤ sint.Z loop_i < length expressions) as Hloop_lt by word.
  1: list_elem expressions_c (sint.Z loop_i) as expression_c.
  1: list_elem expressions (sint.Z loop_i) as expression.
  1: assert (0 ≤ sint.Z loop_i <
      sint.Z (slice.len (v1.LabelSelector.MatchExpressions' selector_c)))
    as Hslice_bounds by word.
  1: wp_pures.
  1: rewrite decide_True; try exact Hslice_bounds.
  1: wp_apply (wp_load_slice_index with "[$Hexpressions_sl]");
    [word|iPureIntro; exact Hexpression_c_lookup|].
  1: iIntros "Hexpressions_sl".
  1: wp_auto.
  1: iDestruct (big_sepL2_lookup_acc with "Hexpressions") as
    "[Hexpression Hrestore_expressions]";
    [exact Hexpression_c_lookup|exact Hexpression_lookup|].
  1: iNamedPrefix "Hexpression" "Hexpression_".
  1: assert (LabelSelectorRequirementV.valid expression)
    as Hexpression_valid.
  1: { rewrite Forall_forall in Hexpressions_valid.
       apply Hexpressions_valid.
       rewrite <-list_elem_of_In.
       eapply list_elem_of_lookup_2. exact Hexpression_lookup. }
  1: pose proof Hexpression_valid as Hvalid_expression.
  1: destruct Hexpression_valid as
    (Hoperator & Hin_values & Hexists_values & Hkey_valid & Hvalues_valid).
  1: destruct Hoperator as
    [Hoperator|[Hoperator|[Hoperator|Hoperator]]].
  all: try (rewrite Hexpression_Hdeepown_operator Hoperator; wp_auto).
  all: try lazymatch goal with
  | Hoperator : LabelSelectorRequirementV.Operator' ?expression = _ |- _ =>
      destruct expression.(LabelSelectorRequirementV.Values') as [values|]
        eqn:Hvalues_opt
  end.
  all: try lazymatch goal with
  | Hvalues_opt : LabelSelectorRequirementV.Values' ?expression = Some ?values
      |- _ =>
      iRename "Hexpression_Hdeepown_values_some" into "Hsource_values";
      rewrite /LabelSelectorRequirementV.values_list Hvalues_opt /=
        in Hvalues_valid Hin_values Hexists_values
  | Hvalues_opt : LabelSelectorRequirementV.Values' ?expression = None
      |- _ =>
      rewrite /LabelSelectorRequirementV.values_list Hvalues_opt /=
        in Hvalues_valid Hin_values Hexists_values
  end.
  1: finish_expression "in"%go values
    (v1.LabelSelectorRequirement.Values' expression_c) dq Hvalid_expression.
  1: (exfalso; apply (Hin_values (or_introl Hoperator))).
  1: done.
  1: finish_expression "notin"%go values
    (v1.LabelSelectorRequirement.Values' expression_c) dq Hvalid_expression.
  1: (exfalso; apply (Hin_values (or_intror Hoperator))).
  1: done.
  1: finish_expression "exists"%go values
    (v1.LabelSelectorRequirement.Values' expression_c) dq Hvalid_expression.
  1: finish_expression "exists"%go ([] : list go_string) slice.nil dq
    Hvalid_expression.
  1: finish_expression "!"%go values
    (v1.LabelSelectorRequirement.Values' expression_c) dq Hvalid_expression.
  1: finish_expression "!"%go ([] : list go_string) slice.nil dq
    Hvalid_expression.

  1: assert (sint.nat loop_i = length expressions) as Hloop_done by word.
  1: assert (take (sint.nat loop_i) expressions = expressions) as Htake_all.
  1: { apply take_ge. lia. }
  1: rewrite Htake_all in Hexpression_entries_pure.
  1: pose proof (Forall2_length Hexpression_entries_pure)
    as Hexpression_entries_len.
  1: rewrite length_fmap in Hexpression_entries_len.
  1: assert (Forall LabelRequirementV.supported
      (snd <$> expression_entries)) as Hsupported.
  1: { eapply expression_conversions_supported.
       exact Hexpression_entries_pure. }
  1: assert (Z.of_nat (length expression_entries) ≤ 2 ^ 63 - 1)
    as Hentries_size.
  1: { rewrite <- Hexpression_entries_len. simpl in Hsize. lia. }
  1: iAssert (by_key_contents current_sl expression_entries)
    with "[Hrequirements Hexpression_entries]"
    as "Hrequirements_contents".
  1: { rewrite /by_key_contents.
       iFrame "Hrequirements". iFrame "#". }
  1: wp_apply wp_NewSelector.
  1: iIntros (empty_selector) "[%Hempty_selector #Hempty_selector_rep]".
  1: rewrite Hempty_selector.
  1: wp_auto.
  1: wp_apply (wp_empty_internalSelector__Add current_sl expression_entries
    with "[$Hlabels_init $Hrequirements_contents]"); first exact Hentries_size.
  1: exact Hsupported.
  1: iIntros (converted) "#Hconverted".
  1: wp_auto.
  1: iApply "HΦ".
  1: iSplitR "Hconverted".
  1: iCombineNamed "Hselector_field_*" as "Hselector_fields".
  1: iAssert (typed_pointsto_def selector_l selector_c dq)
    with "[Hselector_fields]" as "Hselector_l".
  1: { iNamed "Hselector_fields". simpl.
       rewrite /named Hlabels_map_nil. iFrame. }
  1: iDestruct (struct_fields_combine (V:=v1.LabelSelector.t)
    selector_l selector_c dq Hselector_nonnull with "Hselector_l") as
    "Hselector_l".
  1: iExists selector_c.
  1: iFrame "Hselector_l".
  1: rewrite /LabelSelectorV.deepown /named Hlabels_opt
    Hexpressions_opt /=.
  1: iFrame.
  1: iFrame "%".
  1: assert (∀ labels_set,
      selector_matches (snd <$> expression_entries) labels_set ↔
      LabelSelectorV.matches selector labels_set) as Hmatches.
  1: { intros labels_set.
       rewrite (expression_conversions_match expressions
         (snd <$> expression_entries) labels_set
         Hexpression_entries_pure).
       rewrite /LabelSelectorV.matches
         /LabelSelectorV.match_expressions_list Hlabels_opt
         Hexpressions_opt /=.
       split.
       - intros Hmatch. split; [done|exact Hmatch].
       - intros [_ Hmatch]. exact Hmatch. }
  1: iPoseProof (is_selector_ext converted
    (selector_matches (snd <$> expression_entries))
    (LabelSelectorV.matches selector) Hmatches with "Hconverted") as
    "Hconverted'".
  1: iExact "Hconverted'".
Qed.

End proof.
