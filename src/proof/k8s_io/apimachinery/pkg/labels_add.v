From New.proof Require Import prelude empty_ffi sort.
From New.proof.k8s_io.apimachinery.pkg Require Export labels_sort.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : labels.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

Lemma selector_matches_permutation requirements requirements' :
  requirements ≡ₚ requirements' →
  ∀ ls, selector_matches requirements ls ↔
    selector_matches requirements' ls.
Proof.
  intros Hperm ls. rewrite /selector_matches.
  split; intros Hall.
  - eapply Permutation_Forall; [exact Hperm|exact Hall].
  - eapply Permutation_Forall; [symmetry; exact Hperm|exact Hall].
Qed.

Lemma is_selector_ext selector P Q :
  (∀ labels_set, P labels_set ↔ Q labels_set) →
  is_selector selector P -∗ is_selector selector Q.
Proof.
  intros HPQ. iIntros "Hselector".
  iDestruct "Hselector" as
    "[(%sl & %cs & %requirements & %Hselector & #Hsl & #Hrequirements &
       %Hsupported & %HP)|(%Hselector & %HP)]".
  - iLeft. iExists sl, cs, requirements. iFrame "#%".
    iPureIntro. intros labels_set. rewrite -HP. symmetry. apply HPQ.
  - iRight. iFrame "%". iPureIntro. intros labels_set HQ.
    apply (HP labels_set). apply (proj2 (HPQ labels_set)). exact HQ.
Qed.

Lemma big_sepL_requirement_entries entries :
  ([∗ list] entry ∈ entries,
    label_requirement_rep entry.1 entry.2) ⊣⊢
  ([∗ list] c;r ∈ (fst <$> entries);(snd <$> entries),
    label_requirement_rep c r).
Proof.
  induction entries as [|[c r] entries IH]; simpl; first done.
  rewrite IH. done.
Qed.

(** The only receiver produced by [NewSelector] is the empty internal
    selector.  This specialization proves the complete implementation of
    [Add] along that controller-relevant path, including both appends and the
    call to [sort.Sort]. *)
Lemma wp_empty_internalSelector__Add reqs_sl entries :
  Z.of_nat (length entries) ≤ 2 ^ 63 - 1 →
  Forall LabelRequirementV.supported (snd <$> entries) →
  {{{ is_pkg_init labels ∗
      by_key_contents reqs_sl entries
  }}}
    slice.nil @! labels.internalSelector @! "Add" #reqs_sl
  {{{ selector, RET #selector;
      is_selector selector (selector_matches (snd <$> entries))
  }}}.
Proof.
  intros Hsize Hsupported.
  wp_start as "[Hreqs #Hentries]".
  iAssert (is_pkg_init sort) as "#Hsort_init".
  { iPkgInit. }
  iDestruct (own_slice_len with "Hreqs") as %[Hreqs_len Hreqs_nonnegative].
  rewrite length_fmap in Hreqs_len.
  wp_auto.
  wp_apply (wp_slice_make3 (V:=labels.Requirement.t)
    (t:=labels.Requirement)); first word.
  iIntros (ret_sl) "(Hret & Hret_cap & %Hret_cap)".
  wp_auto.
  iAssert (slice.nil ↦* ([] : list labels.Requirement.t))%I
    as "Hsource_nil".
  { iApply own_slice_nil. }
  wp_apply (wp_slice_append with "[$Hret $Hret_cap $Hsource_nil]").
  iIntros (ret_sl') "(Hret & Hret_cap & _)". wp_auto.
  wp_apply (wp_slice_append with "[$Hret $Hret_cap $Hreqs]").
  iIntros (ret_sl'') "(Hret & Hret_cap & Hreqs)". wp_auto.
  iEval (simpl) in "Hret".
  iAssert (by_key_contents ret_sl'' entries)
    with "[$Hret $Hentries]" as "Hsort_contents".
  wp_bind ((let: "$a0" := Convert labels.ByKey sort.Interface #ret_sl'' in
    (FuncResolve sort.Sort [] #()) "$a0")%E).
  iApply (wp_Sort labels.ByKey by_key_contents ret_sl'' entries
    with "[$Hsort_init $Hsort_contents]").
  iNext.
  iIntros (sorted_entries) "[Hsort_contents %Hperm]".
  iDestruct "Hsort_contents" as "[Hret #Hsorted_entries]".
  iEval (rewrite big_sepL_requirement_entries) in "Hsorted_entries".
  iMod (own_slice_persist with "Hret") as "#Hret".
  wp_auto.
  iApply "HΦ". iLeft.
  iExists ret_sl'', (fst <$> sorted_entries), (snd <$> sorted_entries).
  iSplit; first done.
  iFrame "#".
  iSplit.
  { iPureIntro. eapply Permutation_Forall.
    - apply Permutation_map. exact Hperm.
    - exact Hsupported. }
  iPureIntro. intros ls.
  apply selector_matches_permutation.
  apply Permutation_map. exact Hperm.
Qed.

End proof.
