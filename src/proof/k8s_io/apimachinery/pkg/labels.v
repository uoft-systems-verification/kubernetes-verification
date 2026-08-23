From New.proof Require Import prelude empty_ffi.
From New.proof.k8s_io.apimachinery.pkg Require Export labels_init.

Module LabelRequirementV.

Record t := mk {
  Key' : go_string;
  Operator' : selection.Operator.t;
  Values' : list go_string;
}.

Global Instance eq_dec : EqDecision t.
Proof. solve_decision. Defined.

Definition selected_label
    (ls : option (gmap go_string go_string)) (key : go_string) :
    option go_string :=
  match ls with
  | Some labels => labels !! key
  | None => None
  end.

Definition matches
    (r : t) (ls : option (gmap go_string go_string)) : Prop :=
  ((r.(Operator') = "in"%go ∨ r.(Operator') = "="%go ∨
      r.(Operator') = "=="%go) ∧
    match selected_label ls r.(Key') with
    | Some value => value ∈ r.(Values')
    | None => False
    end) ∨
  ((r.(Operator') = "notin"%go ∨ r.(Operator') = "!="%go) ∧
    match selected_label ls r.(Key') with
    | Some value => value ∉ r.(Values')
    | None => True
    end) ∨
  (r.(Operator') = "exists"%go ∧ is_Some (selected_label ls r.(Key'))) ∨
  (r.(Operator') = "!"%go ∧ selected_label ls r.(Key') = None).

Definition supported (r : t) : Prop :=
  r.(Operator') = "in"%go ∨ r.(Operator') = "="%go ∨
  r.(Operator') = "=="%go ∨ r.(Operator') = "notin"%go ∨
  r.(Operator') = "!="%go ∨ r.(Operator') = "exists"%go ∨
  r.(Operator') = "!"%go.

Global Instance matches_dec r ls : Decision (matches r ls).
Proof. unfold matches. destruct (selected_label ls r.(Key')); apply _. Defined.

End LabelRequirementV.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : labels.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

Definition labels_set_rep (l : map.t)
    (ls : option (gmap go_string go_string)) (dq : dfrac) : iProp Σ :=
  ⌜ l = null ↔ ls = None ⌝ ∗
  match ls with
  | Some m => l ↦${dq} m
  | None => True
  end.

Global Instance labels_set_rep_persistent l ls :
  Persistent (labels_set_rep l ls DfracDiscarded).
Proof. rewrite /labels_set_rep. apply _. Qed.

Definition label_requirement_rep (c : labels.Requirement.t)
    (r : LabelRequirementV.t) : iProp Σ :=
  ⌜ c.(labels.Requirement.key') = r.(LabelRequirementV.Key') ⌝ ∗
  ⌜ c.(labels.Requirement.operator') = r.(LabelRequirementV.Operator') ⌝ ∗
  c.(labels.Requirement.strValues') ↦*□ r.(LabelRequirementV.Values').

Global Instance label_requirement_rep_persistent c r :
  Persistent (label_requirement_rep c r).
Proof. rewrite /label_requirement_rep. apply _. Qed.

Definition selector_matches
    (requirements : list LabelRequirementV.t)
    (ls : option (gmap go_string go_string)) : Prop :=
  Forall (λ requirement, LabelRequirementV.matches requirement ls) requirements.

Global Instance selector_matches_dec requirements ls :
  Decision (selector_matches requirements ls).
Proof. unfold selector_matches. apply _. Defined.

Definition everything_matches (_ : option (gmap go_string go_string)) : Prop := True.
Definition nothing_matches (_ : option (gmap go_string go_string)) : Prop := False.

Global Instance everything_matches_dec ls : Decision (everything_matches ls).
Proof. unfold everything_matches. apply _. Defined.

Global Instance nothing_matches_dec ls : Decision (nothing_matches ls).
Proof. unfold nothing_matches. apply _. Defined.

Definition is_selector (selector : labels.Selector.t)
    (P : option (gmap go_string go_string) → Prop) : iProp Σ :=
  (∃ sl cs requirements,
    ⌜ selector = interface.ok (interface.mk labels.internalSelector #sl) ⌝ ∗
    sl ↦*□ cs ∗
    ([∗ list] c;r ∈ cs;requirements, label_requirement_rep c r) ∗
    ⌜ Forall LabelRequirementV.supported requirements ⌝ ∗
    ⌜ ∀ ls, P ls ↔ selector_matches requirements ls ⌝) ∨
  (⌜ selector = interface.ok (interface.mk labels.nothingSelector #(labels.nothingSelector.mk)) ⌝ ∗
    ⌜ ∀ ls, ¬ P ls ⌝).

Global Instance is_selector_persistent selector P :
  Persistent (is_selector selector P).
Proof. rewrite /is_selector. apply _. Qed.

Lemma wp_Set__Has l ls dq key :
  {{{ labels_set_rep l ls dq }}}
    l @! labels.Set' @! "Has" #key
  {{{ b, RET #b;
      labels_set_rep l ls dq ∗
      ⌜ b = bool_decide (is_Some (LabelRequirementV.selected_label ls key)) ⌝
  }}}.
Proof.
  wp_start as "H".
  rewrite /labels_set_rep.
  iDestruct "H" as "[%Hl Hmap]".
  wp_auto.
  destruct ls as [m|].
  - wp_apply (wp_map_lookup2 with "Hmap") as "Hmap".
    iApply "HΦ". iSplit.
    { iSplit.
      - iPureIntro. exact Hl.
      - iExact "Hmap". }
    iPureIntro. destruct (m !! key) as [value|] eqn:Hlookup;
      rewrite /LabelRequirementV.selected_label Hlookup; simpl; done.
  - assert (l = null) as -> by (apply Hl; done). wp_auto.
    iApply "HΦ". iSplit; [iSplit; done|done].
Qed.

Lemma wp_Set__Lookup l ls dq key :
  {{{ labels_set_rep l ls dq }}}
    l @! labels.Set' @! "Lookup" #key
  {{{ value b, RET (#value, #b);
      labels_set_rep l ls dq ∗
      ⌜ (b = true ∧ LabelRequirementV.selected_label ls key = Some value) ∨
        (b = false ∧ LabelRequirementV.selected_label ls key = None) ⌝
  }}}.
Proof.
  wp_start as "H".
  rewrite /labels_set_rep.
  iDestruct "H" as "[%Hl Hmap]".
  wp_auto.
  destruct ls as [m|].
  - wp_apply (wp_map_lookup2 with "Hmap") as "Hmap".
    iApply "HΦ". iSplit.
    { iSplit.
      - iPureIntro. exact Hl.
      - iExact "Hmap". }
    iPureIntro. destruct (m !! key) as [value|] eqn:Hlookup;
      rewrite /LabelRequirementV.selected_label Hlookup; simpl; eauto.
  - assert (l = null) as -> by (apply Hl; done). wp_auto.
    iApply "HΦ". iSplit; [iSplit; done|eauto].
Qed.

Lemma wp_Requirement__hasValue r_l c r dq value :
  {{{ r_l ↦{dq} c ∗ label_requirement_rep c r }}}
    r_l @! (go.PointerType labels.Requirement) @! "hasValue" #value
  {{{ b, RET #b;
      r_l ↦{dq} c ∗
      label_requirement_rep c r ∗
      ⌜ b = bool_decide (value ∈ r.(LabelRequirementV.Values')) ⌝
  }}}.
Proof.
  wp_start as "H". iDestruct "H" as "[Hr #Hrep]".
  rewrite /label_requirement_rep.
  iDestruct "Hrep" as "(%Hkey & %Hop & #Hvalues)".
  rewrite exception_do_unseal /exception_do_def.
  wp_auto.
  iDestruct (own_slice_len with "Hvalues") as %[Hlen Hlen_nonneg].
  wp_alloc loop_i_ptr as "Hloop_i". wp_auto.
  set I := (∃ (loop_i source_i : w64),
    "Hloop_i" ∷ loop_i_ptr ↦ loop_i ∗
    "Hi" ∷ i_ptr ↦ source_i ∗
    "Hr" ∷ r_l ↦{dq} c ∗
    "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z loop_i ≤ length r.(LabelRequirementV.Values') ⌝ ∗
    "%Hnot_found" ∷ ⌜ value ∉ take (sint.nat loop_i) r.(LabelRequirementV.Values') ⌝)%I.
  iAssert I with "[Hloop_i i Hr]" as "Hloop".
  { iExists (W64 0), (W64 0). iFrame. iPureIntro. split; first word.
    simpl. intros Hmember. inversion Hmember. }
  wp_for "Hloop". wp_if_destruct.
  - assert (0 ≤ sint.Z loop_i < length r.(LabelRequirementV.Values')) as Hibounds by word.
    assert (0 ≤ sint.Z loop_i < sint.Z (slice.len c.(labels.Requirement.strValues')))
      as Hslice_bounds by word.
    list_elem r.(LabelRequirementV.Values') (sint.Z loop_i) as current.
    rewrite decide_True; [exact Hslice_bounds|].
    wp_apply (wp_load_slice_index with "[$Hvalues]");
      [word|iPureIntro; exact Hcurrent_lookup|].
    iIntros "_". wp_auto.
    rewrite decide_True; [exact Hslice_bounds|].
    wp_apply (wp_load_slice_index with "[$Hvalues]");
      [word|iPureIntro; exact Hcurrent_lookup|].
    iIntros "_". wp_auto. wp_if_destruct.
    + iApply wp_for_post_return.
      rewrite return_val_unseal /return_val_def. wp_auto.
      rewrite exception_seq_unseal /exception.exception_seq_def. wp_auto.
      iApply "HΦ". iFrame. iFrame "#". iPureIntro.
      assert (value ∈ r.(LabelRequirementV.Values')) as Hmember.
      { eapply list_elem_of_lookup_2. exact Hcurrent_lookup. }
      rewrite bool_decide_true; done.
    + iApply wp_for_post_do. wp_auto.
      iFrame "HΦ r value".
      iExists (word.add loop_i (W64 1)), loop_i. iFrame.
      iPureIntro. split; first word.
      assert (sint.nat (word.add loop_i (W64 1)) = S (sint.nat loop_i)) as -> by word.
      rewrite (take_S_r _ _ current Hcurrent_lookup).
      apply not_elem_of_app. split; first done.
      rewrite list_elem_of_singleton. intros Heq.
      apply n. symmetry. exact Heq.
  - assert (sint.nat loop_i = length r.(LabelRequirementV.Values')) as Hi_len by word.
    assert (take (sint.nat loop_i) r.(LabelRequirementV.Values') =
      r.(LabelRequirementV.Values')) as Htake.
    { apply take_ge. rewrite Hi_len. done. }
    rewrite Htake in Hnot_found.
    rewrite return_val_unseal /return_val_def. wp_auto.
    iApply "HΦ". iFrame. iFrame "#". iPureIntro.
    rewrite bool_decide_false; done.
Qed.

Lemma wp_Requirement__Matches_impl r_l c r dq labels_l ls labels_dq :
  LabelRequirementV.supported r →
  {{{ r_l ↦{dq} c ∗
      label_requirement_rep c r ∗
      labels_set_rep labels_l ls labels_dq
  }}}
    (labels.Requirement__Matchesⁱᵐᵖˡ #r_l)
      #(interface.ok (interface.mk labels.Set' #labels_l))
  {{{ b, RET #b;
      r_l ↦{dq} c ∗
      label_requirement_rep c r ∗
      labels_set_rep labels_l ls labels_dq ∗
      ⌜ b = bool_decide (LabelRequirementV.matches r ls) ⌝
  }}}.
Proof.
  intros Hsupported.
  wp_start as "H".
  iDestruct "H" as "(r_l & label_requirement_rep & labels_set_rep)".
  iEval (rewrite /label_requirement_rep) in "label_requirement_rep".
  iDestruct "label_requirement_rep" as "(%Hkey & %Hop & #Hvalues)".
  iAssert (label_requirement_rep c r) as "#Hrep".
  { rewrite /label_requirement_rep. iFrame "#%". }
  rewrite exception_do_unseal /exception_do_def.
  wp_auto.
  destruct Hsupported as [Hin|[Heq|[Hdeq|[Hnotin|[Hneq|[Hexists|Hnotexists]]]]]];
    rewrite Hop; rewrite ?Hin ?Heq ?Hdeq ?Hnotin ?Hneq ?Hexists ?Hnotexists;
    wp_auto; rewrite Hkey.
  - wp_apply (wp_Set__Lookup with "[$labels_set_rep]").
    iIntros (found_value found) "[Hlabels %Hfound]".
    destruct Hfound as [[-> Hfound]|[-> Hfound]].
    + wp_auto.
      wp_apply (wp_Requirement__hasValue with "[$r_l $Hvalues //]").
      iIntros (b) "(Hr & _ & %Hb)".
      wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
      iApply "HΦ". iFrame. iFrame "#". iPureIntro.
      rewrite Hb. apply bool_decide_ext.
      unfold LabelRequirementV.matches. rewrite Hin Hfound.
      split.
      * intros Hmember. left. split; [left; reflexivity|exact Hmember].
      * intros [Hgood|[Hnot|[Hexists'|Hdoesnot]]].
        { destruct Hgood as [_ Hmember]. exact Hmember. }
        { destruct Hnot as [[Hbad|Hbad] _]; discriminate. }
        { destruct Hexists' as [Hbad _]. discriminate. }
        { destruct Hdoesnot as [Hbad _]. discriminate. }
    + wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
      iApply "HΦ". iFrame. iFrame "#". iPureIntro.
      symmetry. apply bool_decide_eq_false_2.
      unfold LabelRequirementV.matches. rewrite Hin Hfound.
      intros [Hgood|[Hnot|[Hexists'|Hdoesnot]]].
      * destruct Hgood as [_ Hfalse]. exact Hfalse.
      * destruct Hnot as [[Hbad|Hbad] _]; discriminate.
      * destruct Hexists' as [Hbad _]. discriminate.
      * destruct Hdoesnot as [Hbad _]. discriminate.
  - wp_apply (wp_Set__Lookup with "[$labels_set_rep]").
    iIntros (found_value found) "[Hlabels %Hfound]".
    destruct Hfound as [[-> Hfound]|[-> Hfound]].
    + wp_auto.
      wp_apply (wp_Requirement__hasValue with "[$r_l $Hvalues //]").
      iIntros (b) "(Hr & _ & %Hb)".
      wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
      iApply "HΦ". iFrame. iFrame "#". iPureIntro.
      rewrite Hb. apply bool_decide_ext.
      unfold LabelRequirementV.matches. rewrite Heq Hfound.
      split.
      * intros Hmember. left. split; [right; left; reflexivity|exact Hmember].
      * intros [Hgood|[Hnot|[Hexists'|Hdoesnot]]].
        { destruct Hgood as [_ Hmember]. exact Hmember. }
        { destruct Hnot as [[Hbad|Hbad] _]; discriminate. }
        { destruct Hexists' as [Hbad _]. discriminate. }
        { destruct Hdoesnot as [Hbad _]. discriminate. }
    + wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
      iApply "HΦ". iFrame. iFrame "#". iPureIntro.
      symmetry. apply bool_decide_eq_false_2.
      unfold LabelRequirementV.matches. rewrite Heq Hfound.
      intros [Hgood|[Hnot|[Hexists'|Hdoesnot]]].
      * destruct Hgood as [_ Hfalse]. exact Hfalse.
      * destruct Hnot as [[Hbad|Hbad] _]; discriminate.
      * destruct Hexists' as [Hbad _]. discriminate.
      * destruct Hdoesnot as [Hbad _]. discriminate.
  - wp_apply (wp_Set__Lookup with "[$labels_set_rep]").
    iIntros (found_value found) "[Hlabels %Hfound]".
    destruct Hfound as [[-> Hfound]|[-> Hfound]].
    + wp_auto.
      wp_apply (wp_Requirement__hasValue with "[$r_l $Hvalues //]").
      iIntros (b) "(Hr & _ & %Hb)".
      wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
      iApply "HΦ". iFrame. iFrame "#". iPureIntro.
      rewrite Hb. apply bool_decide_ext.
      unfold LabelRequirementV.matches. rewrite Hdeq Hfound.
      split.
      * intros Hmember. left. split; [right; right; reflexivity|exact Hmember].
      * intros [Hgood|[Hnot|[Hexists'|Hdoesnot]]].
        { destruct Hgood as [_ Hmember]. exact Hmember. }
        { destruct Hnot as [[Hbad|Hbad] _]; discriminate. }
        { destruct Hexists' as [Hbad _]. discriminate. }
        { destruct Hdoesnot as [Hbad _]. discriminate. }
    + wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
      iApply "HΦ". iFrame. iFrame "#". iPureIntro.
      symmetry. apply bool_decide_eq_false_2.
      unfold LabelRequirementV.matches. rewrite Hdeq Hfound.
      intros [Hgood|[Hnot|[Hexists'|Hdoesnot]]].
      * destruct Hgood as [_ Hfalse]. exact Hfalse.
      * destruct Hnot as [[Hbad|Hbad] _]; discriminate.
      * destruct Hexists' as [Hbad _]. discriminate.
      * destruct Hdoesnot as [Hbad _]. discriminate.
  - wp_apply (wp_Set__Lookup with "[$labels_set_rep]").
    iIntros (found_value found) "[Hlabels %Hfound]".
    destruct Hfound as [[-> Hfound]|[-> Hfound]].
    + wp_auto.
      wp_apply (wp_Requirement__hasValue with "[$r_l $Hvalues //]").
      iIntros (b) "(Hr & _ & %Hb)".
      wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
      iApply "HΦ". iFrame. iFrame "#". iPureIntro.
      destruct (decide (found_value ∈ r.(LabelRequirementV.Values'))) as [Hmem|Hmem].
      * assert (bool_decide (found_value ∈ r.(LabelRequirementV.Values')) = true)
          as Hbool by (apply bool_decide_eq_true_2; exact Hmem).
        rewrite Hb Hbool. simpl.
        symmetry. apply bool_decide_eq_false_2.
        unfold LabelRequirementV.matches. rewrite Hnotin Hfound.
        intros [Hfirst|[Hsecond|[Hexists'|Hdoesnot]]].
        { destruct Hfirst as [[Hbad|[Hbad|Hbad]] _]; discriminate. }
        { destruct Hsecond as [_ Hnotmember]. exact (Hnotmember Hmem). }
        { destruct Hexists' as [Hbad _]. discriminate. }
        { destruct Hdoesnot as [Hbad _]. discriminate. }
      * assert (bool_decide (found_value ∈ r.(LabelRequirementV.Values')) = false)
          as Hbool by (apply bool_decide_eq_false_2; exact Hmem).
        rewrite Hb Hbool. simpl.
        symmetry. apply bool_decide_eq_true_2.
        unfold LabelRequirementV.matches. rewrite Hnotin Hfound.
        right. left. split; [left; reflexivity|exact Hmem].
    + wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
      iApply "HΦ". iFrame. iFrame "#". iPureIntro.
      symmetry. apply bool_decide_eq_true_2.
      unfold LabelRequirementV.matches. rewrite Hnotin Hfound.
      right. left. split; [left; reflexivity|done].
  - wp_apply (wp_Set__Lookup with "[$labels_set_rep]").
    iIntros (found_value found) "[Hlabels %Hfound]".
    destruct Hfound as [[-> Hfound]|[-> Hfound]].
    + wp_auto.
      wp_apply (wp_Requirement__hasValue with "[$r_l $Hvalues //]").
      iIntros (b) "(Hr & _ & %Hb)".
      wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
      iApply "HΦ". iFrame. iFrame "#". iPureIntro.
      destruct (decide (found_value ∈ r.(LabelRequirementV.Values'))) as [Hmem|Hmem].
      * assert (bool_decide (found_value ∈ r.(LabelRequirementV.Values')) = true)
          as Hbool by (apply bool_decide_eq_true_2; exact Hmem).
        rewrite Hb Hbool. simpl.
        symmetry. apply bool_decide_eq_false_2.
        unfold LabelRequirementV.matches. rewrite Hneq Hfound.
        intros [Hfirst|[Hsecond|[Hexists'|Hdoesnot]]].
        { destruct Hfirst as [[Hbad|[Hbad|Hbad]] _]; discriminate. }
        { destruct Hsecond as [_ Hnotmember]. exact (Hnotmember Hmem). }
        { destruct Hexists' as [Hbad _]. discriminate. }
        { destruct Hdoesnot as [Hbad _]. discriminate. }
      * assert (bool_decide (found_value ∈ r.(LabelRequirementV.Values')) = false)
          as Hbool by (apply bool_decide_eq_false_2; exact Hmem).
        rewrite Hb Hbool. simpl.
        symmetry. apply bool_decide_eq_true_2.
        unfold LabelRequirementV.matches. rewrite Hneq Hfound.
        right. left. split; [right; reflexivity|exact Hmem].
    + wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
      iApply "HΦ". iFrame. iFrame "#". iPureIntro.
      symmetry. apply bool_decide_eq_true_2.
      unfold LabelRequirementV.matches. rewrite Hneq Hfound.
      right. left. split; [right; reflexivity|done].
  - wp_apply (wp_Set__Has with "[$labels_set_rep]").
    iIntros (b) "[Hlabels %Hb]".
    wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
    iApply "HΦ". iFrame. iFrame "#". iPureIntro.
    rewrite Hb. apply bool_decide_ext.
    unfold LabelRequirementV.matches. rewrite Hexists.
    split.
    + intros Hsome. right. right. left. split; [reflexivity|exact Hsome].
    + intros [Hfirst|[Hsecond|[Hexists'|Hdoesnot]]].
      * destruct Hfirst as [[Hbad|[Hbad|Hbad]] _]; discriminate.
      * destruct Hsecond as [[Hbad|Hbad] _]; discriminate.
      * destruct Hexists' as [_ Hsome]. exact Hsome.
      * destruct Hdoesnot as [Hbad _]. discriminate.
  - wp_apply (wp_Set__Has with "[$labels_set_rep]").
    iIntros (b) "[Hlabels %Hb]".
    wp_auto. rewrite return_val_unseal /return_val_def. wp_auto.
    iApply "HΦ". iFrame. iFrame "#". iPureIntro.
    destruct (LabelRequirementV.selected_label ls r.(LabelRequirementV.Key'))
      as [value'|] eqn:Hselected.
    + assert (bool_decide (is_Some (Some value')) = true) as Hsome by done.
      rewrite Hb Hsome. simpl.
      symmetry. apply bool_decide_eq_false_2.
      unfold LabelRequirementV.matches. rewrite Hnotexists.
      intros [Hfirst|[Hsecond|[Hexists'|Hdoesnot]]].
      * destruct Hfirst as [[Hbad|[Hbad|Hbad]] _]; discriminate.
      * destruct Hsecond as [[Hbad|Hbad] _]; discriminate.
      * destruct Hexists' as [Hbad _]. discriminate.
      * destruct Hdoesnot as [_ Hnone]. rewrite Hselected in Hnone. discriminate.
    + assert (bool_decide (is_Some (None : option go_string)) = false) as Hnone by done.
      rewrite Hb Hnone. simpl.
      symmetry. apply bool_decide_eq_true_2.
      unfold LabelRequirementV.matches. rewrite Hnotexists.
      right. right. right. split; [reflexivity|exact Hselected].
Qed.

Lemma wp_Requirement__Matches r_l c r dq labels_l ls labels_dq :
  LabelRequirementV.supported r →
  {{{ r_l ↦{dq} c ∗
      label_requirement_rep c r ∗
      labels_set_rep labels_l ls labels_dq
  }}}
    r_l @! (go.PointerType labels.Requirement) @! "Matches"
      #(interface.ok (interface.mk labels.Set' #labels_l))
  {{{ b, RET #b;
      r_l ↦{dq} c ∗
      label_requirement_rep c r ∗
      labels_set_rep labels_l ls labels_dq ∗
      ⌜ b = bool_decide (LabelRequirementV.matches r ls) ⌝
  }}}.
Proof.
  intros Hsupported.
  iIntros (Φ) "H HΦ".
  wp_method_call. wp_call.
  wp_apply (wp_Requirement__Matches_impl r_l c r dq labels_l ls labels_dq
    Hsupported with "H").
  iIntros (b) "H". iApply "HΦ". iExact "H".
Qed.

Lemma wp_internalSelector__Matches_impl sl cs requirements labels_l ls labels_dq :
  Forall LabelRequirementV.supported requirements →
  {{{ sl ↦*□ cs ∗
      ([∗ list] c;r ∈ cs;requirements, label_requirement_rep c r) ∗
      labels_set_rep labels_l ls labels_dq
  }}}
    (labels.internalSelector__Matchesⁱᵐᵖˡ #sl)
      #(interface.ok (interface.mk labels.Set' #labels_l))
  {{{ b, RET #b;
      sl ↦*□ cs ∗
      ([∗ list] c;r ∈ cs;requirements, label_requirement_rep c r) ∗
      labels_set_rep labels_l ls labels_dq ∗
      ⌜ b = bool_decide (selector_matches requirements ls) ⌝
  }}}.
Proof.
  intros Hsupported.
  wp_start as "H".
  iDestruct "H" as "(#Hsl & #Hrequirements & Hlabels)".
  iDestruct (own_slice_len with "Hsl") as %(Hcs_len1 & Hcs_len2).
  iDestruct (big_sepL2_length with "Hrequirements") as %Hrequirements_len.
  rewrite exception_do_unseal /exception_do_def.
  wp_auto.
  set I := (∃ (loop_i source_i : w64),
    "Hloop_i" ∷ i_ptr ↦ loop_i ∗
    "Hix" ∷ ix_ptr ↦ source_i ∗
    "Hlabels" ∷ labels_set_rep labels_l ls labels_dq ∗
    "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z loop_i ≤ sint.Z (slice.len sl) ⌝ ∗
    "%Hprefix" ∷ ⌜ selector_matches (take (sint.nat loop_i) requirements) ls ⌝)%I.
  iAssert I with "[i ix Hlabels]" as "Hloop".
  { iExists (W64 0), (W64 0). iFrame. iPureIntro.
    split; [word|constructor]. }
  wp_for "Hloop". wp_if_destruct.
  - assert (0 ≤ sint.Z loop_i < sint.Z (slice.len sl)) as Hslice_bounds by word.
    list_elem cs (sint.Z loop_i) as current_c.
    assert (∃ current_r, requirements !! sint.nat loop_i = Some current_r)
      as [current_r Hcurrent_r_lookup].
    { apply lookup_lt_is_Some_2.
      rewrite <-Hrequirements_len. rewrite Hcs_len1. word. }
    iDestruct (big_sepL2_lookup _ _ _ (sint.nat loop_i) current_c current_r
      with "Hrequirements") as "#Hcurrent";
      [exact Hcurrent_c_lookup|exact Hcurrent_r_lookup|].
    iDestruct (own_slice_elem_acc (sint.Z loop_i) with "Hsl")
      as "[#Hcell _]"; [word|exact Hcurrent_c_lookup|].
    rewrite -> decide_True by exact Hslice_bounds.
    wp_apply (wp_load_slice_index (V:=labels.Requirement.t)
      (t:=labels.Requirement) sl (sint.Z loop_i) cs with "[$Hsl]");
      [word|iPureIntro; exact Hcurrent_c_lookup|].
    iIntros "_". wp_auto.
    rewrite -> decide_True by exact Hslice_bounds.
    wp_bind ((MethodResolve (go.PointerType labels.Requirement) "Matches"
      #(slice_index_ref labels.Requirement.t (sint.Z loop_i) sl))
      #(interface.ok (interface.mk labels.Set' #labels_l)))%E.
    assert (LabelRequirementV.supported current_r) as Hcurrent_supported.
    { rewrite Forall_forall in Hsupported. apply Hsupported.
      rewrite <-list_elem_of_In.
      eapply list_elem_of_lookup_2. exact Hcurrent_r_lookup. }
    wp_pures. wp_method_call. wp_call.
    wp_apply (wp_Requirement__Matches_impl
      (slice_index_ref labels.Requirement.t (sint.Z loop_i) sl)
      current_c current_r DfracDiscarded labels_l ls labels_dq Hcurrent_supported with
      "[$Hcell $Hcurrent $Hlabels]").
    iIntros (matches) "(_ & _ & Hlabels & %Hmatches)".
    wp_auto.
    destruct (decide (LabelRequirementV.matches current_r ls))
      as [Hcurrent_matches|Hcurrent_not_matches].
    + rewrite -> bool_decide_true in Hmatches by exact Hcurrent_matches.
      subst matches. wp_auto.
      iApply wp_for_post_do. wp_auto.
      iFrame "HΦ s l Hlabels".
      iExists (word.add loop_i (W64 1)), loop_i. iFrame.
      iPureIntro. split; first word.
      assert (sint.nat (word.add loop_i (W64 1)) = S (sint.nat loop_i)) as -> by word.
      rewrite (take_S_r _ _ current_r Hcurrent_r_lookup).
      rewrite /selector_matches Forall_app Forall_singleton.
      split; first exact Hprefix. exact Hcurrent_matches.
    + rewrite -> bool_decide_false in Hmatches by exact Hcurrent_not_matches.
      subst matches. wp_auto.
      iApply wp_for_post_return.
      rewrite return_val_unseal /return_val_def. wp_auto.
      rewrite exception_seq_unseal /exception.exception_seq_def. wp_auto.
      iApply "HΦ". iFrame "# Hlabels". iPureIntro.
      assert (¬ selector_matches requirements ls) as Hnot_matches.
      { intros Hall.
        rewrite /selector_matches Forall_forall in Hall.
        specialize (Hall current_r).
        rewrite <-list_elem_of_In in Hall.
        assert (current_r ∈ requirements) as Hin_requirement.
        { eapply list_elem_of_lookup_2. exact Hcurrent_r_lookup. }
        exact (Hcurrent_not_matches (Hall Hin_requirement)). }
      rewrite bool_decide_false; done.
  - assert (sint.nat loop_i = length requirements) as Hi_len.
    { rewrite <-Hrequirements_len. rewrite Hcs_len1. word. }
    assert (take (sint.nat loop_i) requirements = requirements) as Htake.
    { apply take_ge. rewrite Hi_len. done. }
    rewrite Htake in Hprefix.
    rewrite return_val_unseal /return_val_def. wp_auto.
    iApply "HΦ". iFrame "# Hlabels". iPureIntro.
    rewrite bool_decide_true; done.
Qed.

Lemma wp_internalSelector__Matches sl cs requirements labels_l ls labels_dq :
  Forall LabelRequirementV.supported requirements →
  {{{ sl ↦*□ cs ∗
      ([∗ list] c;r ∈ cs;requirements, label_requirement_rep c r) ∗
      labels_set_rep labels_l ls labels_dq
  }}}
    sl @! labels.internalSelector @! "Matches"
      #(interface.ok (interface.mk labels.Set' #labels_l))
  {{{ b, RET #b;
      sl ↦*□ cs ∗
      ([∗ list] c;r ∈ cs;requirements, label_requirement_rep c r) ∗
      labels_set_rep labels_l ls labels_dq ∗
      ⌜ b = bool_decide (selector_matches requirements ls) ⌝
  }}}.
Proof.
  intros Hsupported.
  iIntros (Φ) "H HΦ".
  wp_method_call. wp_call.
  wp_apply (wp_internalSelector__Matches_impl sl cs requirements labels_l ls labels_dq
    Hsupported with "H").
  iIntros (b) "H". iApply "HΦ". iExact "H".
Qed.

Lemma wp_Selector__Matches_resolved selector P
    `{!∀ ls, Decision (P ls)} labels_l ls labels_dq :
  {{{ is_selector selector P ∗ labels_set_rep labels_l ls labels_dq }}}
    (match selector with
    | interface.ok i => Val (#(methods i.(interface.ty) "Matches" i.(interface.v)))
    | interface.nil => Panic "nil interface"
    end) #(interface.ok (interface.mk labels.Set' #labels_l))
  {{{ b, RET #b;
      is_selector selector P ∗
      labels_set_rep labels_l ls labels_dq ∗
      ⌜ b = bool_decide (P ls) ⌝
  }}}.
Proof.
  wp_start as "H".
  iDestruct "H" as "[#Hselector Hlabels]".
  rewrite /is_selector.
  iDestruct "Hselector" as
    "[(%sl & %cs & %requirements & %Hselector & #Hsl & #Hrequirements &
       %Hsupported & %HP)|(%Hselector & %HP)]".
  - subst selector. simpl.
    wp_apply (wp_internalSelector__Matches sl cs requirements labels_l ls labels_dq
      Hsupported with "[$Hsl $Hrequirements $Hlabels]").
    iIntros (b) "(_ & _ & Hlabels & %Hb)".
    iApply "HΦ". iSplit.
    { iLeft. iExists sl, cs, requirements. iFrame "#%". done. }
    iFrame "# Hlabels". iPureIntro.
    rewrite Hb. apply bool_decide_ext. symmetry. apply HP.
  - subst selector. simpl.
    pose proof (labels.nothingSelector_Matches_unfold
      (nothingSelector_Assumptions:=
        labels.nothingSelector_instance (Assumptions:=package_sem))) as Hmethod.
    pose proof (@method_unfold _ _ _ _ _ _ Hmethod) as Hmethod_unfold.
    iEval (rewrite Hmethod_unfold). wp_call.
    rewrite /labels.nothingSelector__Matchesⁱᵐᵖˡ. wp_call. wp_auto.
    iApply "HΦ". iSplit.
    { iRight. iFrame "#%". done. }
    iFrame "# Hlabels". iPureIntro.
    symmetry. apply bool_decide_eq_false_2. apply HP.
Qed.

Lemma wp_Selector__Matches selector P
    `{!∀ ls, Decision (P ls)} labels_l ls labels_dq :
  {{{ is_selector selector P ∗ labels_set_rep labels_l ls labels_dq }}}
    (MethodResolve labels.Selector "Matches" #selector)
      #(interface.ok (interface.mk labels.Set' #labels_l))
  {{{ b, RET #b;
      is_selector selector P ∗
      labels_set_rep labels_l ls labels_dq ∗
      ⌜ b = bool_decide (P ls) ⌝
  }}}.
Proof.
  wp_start as "H".
  iDestruct "H" as "[#Hselector Hlabels]".
  rewrite /is_selector.
  iDestruct "Hselector" as
    "[(%sl & %cs & %requirements & %Hselector & #Hsl & #Hrequirements &
       %Hsupported & %HP)|(%Hselector & %HP)]".
  - subst selector. wp_pures.
    wp_apply (wp_internalSelector__Matches sl cs requirements labels_l ls labels_dq
      Hsupported with "[$Hsl $Hrequirements $Hlabels]").
    iIntros (b) "(_ & _ & Hlabels & %Hb)".
    iApply "HΦ". iSplit.
    { iLeft. iExists sl, cs, requirements. iFrame "#%". done. }
    iFrame "# Hlabels". iPureIntro.
    rewrite Hb. apply bool_decide_ext. symmetry. apply HP.
  - subst selector. wp_pures.
    pose proof (labels.nothingSelector_Matches_unfold
      (nothingSelector_Assumptions:=
        labels.nothingSelector_instance (Assumptions:=package_sem))) as Hmethod.
    pose proof (@method_unfold _ _ _ _ _ _ Hmethod) as Hmethod_unfold.
    iEval (rewrite Hmethod_unfold). wp_call.
    rewrite /labels.nothingSelector__Matchesⁱᵐᵖˡ. wp_call. wp_auto.
    iApply "HΦ". iSplit.
    { iRight. iFrame "#%". done. }
    iFrame "# Hlabels". iPureIntro.
    symmetry. apply bool_decide_eq_false_2. apply HP.
Qed.

Lemma wp_Everything :
  {{{ is_pkg_init labels }}}
    @! labels.Everything #()
  {{{ selector, RET #selector; is_selector selector everything_matches }}}.
Proof.
  wp_start.
  iDestruct (is_pkg_init_access with "[$]") as "Hinit".
  simpl. iNamed "Hinit".
  wp_auto.
  iApply "HΦ".
  iLeft.
  iExists slice.nil, [], [].
  iSplit; first done.
  iSplit; first iApply own_slice_nil.
  iSplit; first done.
  iSplit; first (iPureIntro; constructor).
  iPureIntro. intros ls. split; intros; constructor.
Qed.

Lemma wp_Nothing :
  {{{ is_pkg_init labels }}}
    @! labels.Nothing #()
  {{{ selector, RET #selector; is_selector selector nothing_matches }}}.
Proof.
  wp_start.
  iDestruct (is_pkg_init_access with "[$]") as "Hinit".
  simpl. iNamed "Hinit".
  wp_auto.
  iApply "HΦ".
  iRight. iSplit; first done.
  iPureIntro. intros ls Hfalse. unfold nothing_matches in Hfalse.
  contradiction.
Qed.

End proof.
