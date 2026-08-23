From New.proof Require Import prelude empty_ffi sort util.
From New.proof.k8s_io.apimachinery.pkg Require Export labels_constructor.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : labels.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

Definition requirement_entry :=
  (labels.Requirement.t * LabelRequirementV.t)%type.

Definition by_key_contents (sl : slice.t)
    (entries : list requirement_entry) : iProp Σ :=
  sl ↦* (fst <$> entries) ∗
  ([∗ list] entry ∈ entries,
    label_requirement_rep entry.1 entry.2).

Lemma wp_ByKey__Len sl entries :
  {{{ by_key_contents sl entries }}}
    sl @! labels.ByKey @! "Len" #()
  {{{ (n : w64), RET #n;
      by_key_contents sl entries ∗
      ⌜ sint.nat n = length entries ∧ 0 ≤ sint.Z n ⌝
  }}}.
Proof.
  wp_start as "[Hsl #Hentries]".
  wp_pures. wp_auto.
  iDestruct (own_slice_len with "Hsl") as %[Hlen Hnonnegative].
  iApply "HΦ". iFrame "# Hsl". iPureIntro.
  rewrite length_fmap in Hlen. split; [symmetry|]; done.
Qed.

Lemma wp_ByKey__Less sl entries (i j : w64) :
  0 ≤ sint.Z i < length entries → 0 ≤ sint.Z j < length entries →
  {{{ by_key_contents sl entries }}}
    sl @! labels.ByKey @! "Less" #i #j
  {{{ (b : bool), RET #b; by_key_contents sl entries }}}.
Proof.
  intros Hi Hj.
  destruct Hi as [Hi_nonnegative Hi_upper].
  destruct Hj as [Hj_nonnegative Hj_upper].
  wp_start as "[Hsl #Hentries]".
  wp_pures.
  iDestruct (own_slice_len with "Hsl") as %[Hlen Hnonnegative].
  rewrite length_fmap in Hlen.
  assert (sint.Z (slice.len sl) = Z.of_nat (length entries)) as Hlen_Z.
  { replace (sint.Z (slice.len sl)) with
      (Z.of_nat (sint.nat (slice.len sl))) by word.
    rewrite <-Hlen. done. }
  wp_auto.
  assert (∃ ci, (fst <$> entries) !! sint.nat i = Some ci)
    as [ci Hci_lookup].
  { apply lookup_lt_is_Some_2. rewrite length_fmap.
    apply Nat2Z.inj_lt.
    replace (Z.of_nat (sint.nat i)) with (sint.Z i) by word. exact Hi_upper. }
  assert (∃ cj, (fst <$> entries) !! sint.nat j = Some cj)
    as [cj Hcj_lookup].
  { apply lookup_lt_is_Some_2. rewrite length_fmap.
    apply Nat2Z.inj_lt.
    replace (Z.of_nat (sint.nat j)) with (sint.Z j) by word. exact Hj_upper. }
  rewrite -> decide_True by
    (split; [exact Hi_nonnegative|rewrite Hlen_Z; exact Hi_upper]).
  iDestruct (own_slice_elem_acc (sint.Z i) with "Hsl") as
    "[Hci Hrestore]";
    [exact Hi_nonnegative|exact Hci_lookup|].
  wp_auto.
  iDestruct ("Hrestore" with "Hci") as "Hsl".
  iEval (rewrite (list_insert_id _ _ _ Hci_lookup)) in "Hsl".
  rewrite -> decide_True by
    (split; [exact Hj_nonnegative|rewrite Hlen_Z; exact Hj_upper]).
  iDestruct (own_slice_elem_acc (sint.Z j) with "Hsl") as
    "[Hcj Hrestore]";
    [exact Hj_nonnegative|exact Hcj_lookup|].
  wp_auto.
  iDestruct ("Hrestore" with "Hcj") as "Hsl".
  iEval (rewrite (list_insert_id _ _ _ Hcj_lookup)) in "Hsl".
  iApply "HΦ". iFrame "# Hsl".
Qed.

Lemma wp_ByKey__Swap sl entries (i j : w64) :
  0 ≤ sint.Z i < length entries → 0 ≤ sint.Z j < length entries →
  {{{ by_key_contents sl entries }}}
    sl @! labels.ByKey @! "Swap" #i #j
  {{{ RET #();
      by_key_contents sl (list_swap entries (sint.nat i) (sint.nat j))
  }}}.
Proof.
  intros Hi Hj.
  destruct Hi as [Hi_nonnegative Hi_upper].
  destruct Hj as [Hj_nonnegative Hj_upper].
  wp_start as "[Hsl #Hentries]".
  wp_pures.
  iDestruct (own_slice_len with "Hsl") as %[Hlen Hnonnegative].
  rewrite length_fmap in Hlen.
  assert (sint.Z (slice.len sl) = Z.of_nat (length entries)) as Hlen_Z.
  { replace (sint.Z (slice.len sl)) with
      (Z.of_nat (sint.nat (slice.len sl))) by word.
    rewrite <-Hlen. done. }
  wp_auto.
  assert (∃ ci, (fst <$> entries) !! sint.nat i = Some ci)
    as [ci Hci_lookup].
  { apply lookup_lt_is_Some_2. rewrite length_fmap.
    apply Nat2Z.inj_lt.
    replace (Z.of_nat (sint.nat i)) with (sint.Z i) by word. exact Hi_upper. }
  assert (∃ cj, (fst <$> entries) !! sint.nat j = Some cj)
    as [cj Hcj_lookup].
  { apply lookup_lt_is_Some_2. rewrite length_fmap.
    apply Nat2Z.inj_lt.
    replace (Z.of_nat (sint.nat j)) with (sint.Z j) by word. exact Hj_upper. }
  rewrite -> decide_True by
    (split; [exact Hj_nonnegative|rewrite Hlen_Z; exact Hj_upper]).
  wp_apply (wp_load_slice_index with "[$Hsl]");
    [exact Hj_nonnegative|iPureIntro; exact Hcj_lookup|].
  iIntros "Hsl". wp_auto.
  rewrite -> decide_True by
    (split; [exact Hi_nonnegative|rewrite Hlen_Z; exact Hi_upper]).
  wp_apply (wp_load_slice_index with "[$Hsl]");
    [exact Hi_nonnegative|iPureIntro; exact Hci_lookup|].
  iIntros "Hsl". wp_auto.
  rewrite -> decide_True by
    (split; [exact Hi_nonnegative|rewrite Hlen_Z; exact Hi_upper]).
  wp_auto.
  wp_apply (wp_store_slice_index with "[$Hsl]").
  { iPureIntro. rewrite length_fmap.
    split; [exact Hi_nonnegative|exact Hi_upper]. }
  iIntros "Hsl". wp_auto.
  rewrite -> decide_True by
    (split; [exact Hj_nonnegative|rewrite Hlen_Z; exact Hj_upper]).
  wp_auto.
  wp_apply (wp_store_slice_index with "[$Hsl]").
  { iPureIntro. rewrite length_insert length_fmap.
    split; [exact Hj_nonnegative|exact Hj_upper]. }
  iIntros "Hsl". wp_auto.
  iApply "HΦ". rewrite /by_key_contents list_swap_fmap.
  iSplit.
  { rewrite /list_swap Hci_lookup Hcj_lookup. iFrame "Hsl". }
  iEval (rewrite (big_sepL_permutation
    (fun entry => label_requirement_rep entry.1 entry.2)
    entries (list_swap entries (sint.nat i) (sint.nat j))
    (list_swap_permutation entries (sint.nat i) (sint.nat j))))
    in "Hentries".
  iFrame "#".
Qed.

#[global] Instance by_key_sort_interface :
  SortInterfaceSpec labels.ByKey by_key_contents.
Proof.
  constructor.
  - apply wp_ByKey__Len.
  - apply wp_ByKey__Less.
  - apply wp_ByKey__Swap.
Qed.

End proof.
