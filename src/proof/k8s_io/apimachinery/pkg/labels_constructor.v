From New.proof Require Import prelude empty_ffi sort.
From New.proof.k8s_io.apimachinery.pkg Require Export labels.
From New.proof.k8s_io.apimachinery.pkg.util Require Import validation.
From New.proof.k8s_io.apimachinery.pkg.util.validation Require Import field.
From New.proof.kubernetes_types Require Import common.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : labels.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

Definition valid_requirement_inputs (key : go_string)
    (operator : selection.Operator.t) (values : list go_string) : Prop :=
  valid_label_name key ∧
  Forall valid_label_value values ∧
  (((operator = "in"%go ∨ operator = "notin"%go) ∧ values ≠ []) ∨
    (operator = "="%go ∧ length values = 1%nat) ∨
    ((operator = "exists"%go ∨ operator = "!"%go) ∧
      values = [])).

Lemma wp_validateLabelKey_valid key (path : loc) :
  valid_label_name key →
  {{{ is_pkg_init labels }}}
    @! labels.validateLabelKey #key #path
  {{{ RET #null; True }}}.
Proof.
  intros Hvalid.
  wp_start as "#Hinit".
  iAssert (is_pkg_init validation) as "#Hvalidation_init".
  { iPkgInit. }
  wp_auto.
  wp_apply (wp_IsQualifiedName with "[$Hvalidation_init]").
  iIntros (sl errs) "[Herrs %Herrs]".
  apply Herrs in Hvalid. subst errs.
  iDestruct (own_slice_len with "Herrs") as %[Hlen Hlen_nonnegative].
  wp_auto.
  wp_if_destruct.
  - iApply "HΦ". done.
  - exfalso. apply n.
    assert (sint.nat (slice.len sl) = 0%nat) as Hzero.
    { symmetry. exact Hlen. }
    word.
Qed.

Lemma wp_validateLabelValue_valid (key value : go_string) (path : loc) :
  valid_label_value value →
  {{{ is_pkg_init labels }}}
    @! labels.validateLabelValue #key #value #path
  {{{ RET #null; True }}}.
Proof.
  intros Hvalid.
  wp_start as "#Hinit".
  iAssert (is_pkg_init validation) as "#Hvalidation_init".
  { iPkgInit. }
  wp_auto.
  wp_apply (wp_IsValidLabelValue with "[$Hvalidation_init]").
  iIntros (sl errs) "[Herrs %Herrs]".
  apply Herrs in Hvalid. subst errs.
  iDestruct (own_slice_len with "Herrs") as %[Hlen Hlen_nonnegative].
  wp_auto.
  wp_if_destruct.
  - iApply "HΦ". done.
  - exfalso. apply n.
    assert (sint.nat (slice.len sl) = 0%nat) as Hzero.
    { symmetry. exact Hlen. }
    word.
Qed.

Lemma wp_NewSelector :
  {{{ True }}}
    @! labels.NewSelector #()
  {{{ selector, RET #selector;
      ⌜ selector = interface.ok
          (interface.mk labels.internalSelector #slice.nil) ⌝ ∗
      is_selector selector everything_matches
  }}}.
Proof.
  wp_start as "_".
  iApply "HΦ". iSplit; first done.
  iLeft.
  iExists slice.nil, [], [].
  iSplit; first done.
  iSplit; first iApply own_slice_nil.
  iSplit; first done.
  iSplit; first (iPureIntro; constructor).
  iPureIntro. intros ls. split; intros; constructor.
Qed.

Lemma wp_NewRequirement key operator values_sl values :
  valid_requirement_inputs key operator values →
  {{{ is_pkg_init labels ∗ values_sl ↦* values }}}
    @! labels.NewRequirement #key #operator #values_sl #slice.nil
  {{{ requirement_l c, RET (#requirement_l, #interface.nil);
      requirement_l ↦ c ∗
      label_requirement_rep c (LabelRequirementV.mk key operator values)
  }}}.
Proof.
  intros (Hkey & Hvalues_valid & Harity).
  wp_start as "Hvalues".
  iAssert (is_pkg_init labels) as "#Hinit".
  { iPkgInit. }
  iAssert (is_pkg_init field) as "#Hfield_init".
  { iPkgInit. }
  iDestruct (own_slice_len with "Hvalues") as %[Hvalues_len Hvalues_nonnegative].
  iMod (own_slice_persist with "Hvalues") as "#Hvalues".
  wp_auto.
  wp_apply (wp_ToPath_nil with "[$Hfield_init]").
  wp_pures.
  wp_apply (wp_Path__Child null "key"%go with "[$Hfield_init]").
  iIntros (key_path) "_".
  wp_pures.
  wp_apply (wp_validateLabelKey_valid with "[$Hinit]"); first done.
  wp_pures.
  wp_apply (wp_Path__Child null "values"%go with "[$Hfield_init]").
  iIntros (values_path) "_".
  destruct Harity as
    [[[Hoperator | Hoperator] Hcardinality] |
      [[Hoperator Hcardinality] |
        [[Hoperator | Hoperator] Hcardinality]]].
  all: rewrite Hoperator.
  all: lazymatch type of Hcardinality with
  | ?xs ≠ [] =>
      assert (slice.len values_sl ≠ W64 0) as Harity_len;
      [intros Hzero; apply Hcardinality; apply nil_length_inv;
       rewrite Hvalues_len; word|]
  | length ?xs = 1%nat =>
      assert (sint.nat (slice.len values_sl) = 1%nat) as Hnat_len;
      [rewrite -Hvalues_len; exact Hcardinality|];
      assert (slice.len values_sl = W64 1) as Harity_len by word
  | ?xs = [] =>
      assert (sint.nat (slice.len values_sl) = 0%nat) as Hnat_len;
      [rewrite -Hvalues_len Hcardinality; done|];
      assert (slice.len values_sl = W64 0) as Harity_len by word
  end.
  all: wp_auto.
  all: lazymatch type of Harity_len with
  | ?actual ≠ W64 0 =>
      rewrite bool_decide_false; try exact Harity_len
  | ?actual = ?expected =>
      rewrite Harity_len bool_decide_true; try done
  end.
  all: wp_pures.
  all: wp_auto.
  all: wp_alloc loop_i_ptr as "Hloop_i"; wp_auto.
  all: set I := (∃ (loop_i source_i : w64),
    "Hloop_i" ∷ loop_i_ptr ↦ loop_i ∗
    "Hi" ∷ i_ptr ↦ source_i ∗
    "Hvalues" ∷ values_sl ↦*□ values ∗
    "Hvals" ∷ vals_ptr ↦ values_sl ∗
    "Hop" ∷ op_ptr ↦ operator ∗
    "Hkey_ptr" ∷ key_ptr ↦ key ∗
    "HallErrs" ∷ allErrs_ptr ↦ (zero_val field.ErrorList.t) ∗
    "HvaluePath" ∷ valuePath_ptr ↦ values_path ∗
    "%Hloop_bounds" ∷
      ⌜ 0 ≤ sint.Z loop_i ≤ length values ⌝)%I.
  Ltac initialize_requirement_loop invariant hop :=
    iAssert invariant with
      "[Hloop_i i Hvalues vals op key allErrs valuePath]" as "Hloop";
    [iExists (W64 0), (W64 0); rewrite hop; iFrame; iFrame "#";
     iPureIntro; word|].
  all: initialize_requirement_loop I Hoperator.
  all: subst I.
  all: wp_for "Hloop"; wp_if_destruct.
  all: iDestruct "Hloop" as
    "(Hi & #Hvalues_loop & Hvals & Hop & Hkey_ptr & HallErrs &
      HvaluePath & %Hloop_bounds)".
  all: iNamed "Hi".
  all: iNamed "Hvals".
  all: iNamed "Hop".
  all: iNamed "Hkey_ptr".
  all: iNamed "HallErrs".
  all: iNamed "HvaluePath".
  all: lazymatch goal with
  | Hbounds : 0 ≤ sint.Z ?idx ≤ _,
    Hzero : slice.len ?sl = W64 0,
    Hlt : sint.Z ?idx < sint.Z (slice.len ?sl) |- _ =>
      destruct Hbounds as [Hloop_nonnegative _];
      rewrite Hzero in Hlt; exfalso; word
  | _ => idtac
  end.
  all: lazymatch goal with
  | Hlt : sint.Z ?idx < _ |- _ =>
      rename Hlt into Hloop_lt;
      destruct Hloop_bounds as [Hloop_nonnegative Hloop_upper];
      assert (0 ≤ sint.Z idx < length values) as Hvalue_bounds by word;
      assert (0 ≤ sint.Z idx < sint.Z (slice.len values_sl))
        as Hslice_bounds by word;
      list_elem values (sint.Z idx) as current_value;
      rewrite decide_True; try exact Hslice_bounds;
      wp_apply (wp_load_slice_index with "[$Hvalues]");
        [word|iPureIntro; exact Hcurrent_value_lookup|];
      iIntros "#Hvalues_read1";
      wp_auto;
      rewrite decide_True; try exact Hslice_bounds;
      wp_apply (wp_load_slice_index with "[$Hvalues]");
        [word|iPureIntro; exact Hcurrent_value_lookup|];
      iIntros "#Hvalues_read2";
      wp_auto;
      wp_pures;
      wp_apply (wp_Path__Index values_path idx with "[$Hfield_init]");
      iIntros (indexed_path) "_";
      wp_pures;
      rewrite Forall_forall in Hvalues_valid;
      assert (valid_label_value current_value) as Hcurrent_valid;
      [apply Hvalues_valid; rewrite <-list_elem_of_In;
       eapply list_elem_of_lookup_2; exact Hcurrent_value_lookup|];
      wp_apply (wp_validateLabelValue_valid key current_value indexed_path
        with "[$Hinit]"); first exact Hcurrent_valid;
      wp_pures;
      iApply wp_for_post_do;
      wp_auto;
      iFrame "HΦ";
      iExists (word.add idx (W64 1)), idx;
      iFrame;
      iFrame "#";
      iPureIntro;
      word
  | _ => idtac
  end.
  all: wp_auto.
  all: wp_alloc requirement_l as "Hrequirement".
  all: wp_pures.
  all: wp_apply (wp_ErrorList__ToAggregate_nil
    with "[$Hfield_init $HallErrs]").
  all: iIntros "HallErrs".
  all: wp_pures.
  all: iApply "HΦ".
  all: iFrame "Hrequirement".
  all: rewrite /label_requirement_rep /=.
  all: iFrame "#".
  all: done.
Qed.

End proof.
