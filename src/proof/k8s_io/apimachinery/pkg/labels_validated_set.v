From New.proof Require Import prelude empty_ffi sort.
From New.proof.map Require Import len for_range.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_label_selector_conversion.
From New.proof.kubernetes_types Require Import labelselector objectmeta.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {labels_sem : labels.Assumptions}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Local Set Default Proof Using "All".

(* Borrow the label set of an object's metadata as a [labels_set_rep]. *)
Lemma objectmeta_labels_rep (c : v1.ObjectMeta.t) (m : ObjectMetaV.t) dq :
  ObjectMetaV.deepown c m dq ⊢
    labels_set_rep c.(v1.ObjectMeta.Labels') m.(ObjectMetaV.Labels') dq ∗
    (labels_set_rep c.(v1.ObjectMeta.Labels') m.(ObjectMetaV.Labels') dq -∗
      ObjectMetaV.deepown c m dq).
Proof.
  rewrite /ObjectMetaV.deepown. iIntros "H". iNamed "H".
  iSplitL "Hdeepown_labels_some".
  - rewrite /labels_set_rep. iSplit; first done.
    destruct (m.(ObjectMetaV.Labels')); last done.
    iDestruct "Hdeepown_labels_some" as (cl) "[H ->]". iExact "H".
  - iIntros "[_ Hl]". iFrame "∗ %".
    destruct (m.(ObjectMetaV.Labels')); last done.
    iExists _. iFrame. done.
Qed.

Lemma match_labels_empty labels_set :
  LabelSelectorV.match_labels (Some ∅) labels_set ↔ selector_matches [] labels_set.
Proof.
  rewrite /LabelSelectorV.match_labels /selector_matches.
  destruct labels_set; split; intros; try done; try constructor.
Qed.

(* The selector built from a validated label set matches exactly the label
   sets containing it. The set size must fit in a Go [int], as for
   [LabelSelectorV.extra_valid]. *)
Lemma wp_SelectorFromValidatedSet l ls dq :
  Z.of_nat (size (default ∅ ls)) ≤ 2 ^ 63 - 1 →
  {{{ is_pkg_init labels ∗ labels_set_rep l ls dq }}}
    @! labels.SelectorFromValidatedSet #l
  {{{ selector, RET #selector;
      labels_set_rep l ls dq ∗
      is_selector selector (LabelSelectorV.match_labels (Some (default ∅ ls)))
  }}}.
Proof.
  intros Hsize_bound.
  wp_start as "Hls".
  iApply wp_fupd.
  iAssert (is_pkg_init sort) as "#Hsort_init".
  { iPkgInit. }
  iDestruct "Hls" as "[%Hnil Hm]".
  wp_auto.
  destruct ls as [m|]; last first.
  { (* nil set: the empty selector *)
    assert (l = map.nil) as -> by (by apply Hnil).
    rewrite bool_decide_true //. wp_auto.
    wp_bind (CompositeLiteral labels.internalSelector _).
    iApply (wp_slice_literal (V:=labels.Requirement.t) (t:=labels.Requirement) []). wp_auto.
    iSplitR; first done.
    iIntros (sel_ptr) "[Hsel _]". wp_auto.
    iMod (own_slice_persist with "Hsel") as "#Hsel".
    iModIntro. iApply "HΦ". iSplitL "Hm"; first (iSplit; done).
    iLeft. iExists _, [], []. iSplit; first done.
    iFrame "Hsel".
    iSplit; first done. iSplit; first (iPureIntro; constructor).
    iPureIntro. intros ls'. apply match_labels_empty. }
  assert (l ≠ map.nil) as Hl_nonnil.
  { intros Heq. by apply Hnil in Heq. }
  rewrite bool_decide_false //. wp_auto.
  rewrite go.len_underlying (go.is_underlying (t := labels.Set') (tunder := labels.Set'ⁱᵐᵖˡ)).
  wp_apply (wp_map_len_resolved (K:=go_string) (V:=go_string) go.string go.string with "Hm").
  iIntros "Hm". wp_auto.
  destruct (bool_decide (W64 (size m) = W64 0)) eqn:Hsize0.
  { (* empty set: the empty selector *)
    apply bool_decide_eq_true in Hsize0.
    wp_auto.
    wp_bind (CompositeLiteral labels.internalSelector _).
    iApply (wp_slice_literal (V:=labels.Requirement.t) (t:=labels.Requirement) []). wp_auto.
    iSplitR; first done.
    iIntros (sel_ptr) "[Hsel _]". wp_auto.
    iMod (own_slice_persist with "Hsel") as "#Hsel".
    simpl in Hsize_bound.
    assert (size m = 0%nat) as Hsize by word.
    apply map_size_empty_iff in Hsize. subst m.
    iModIntro. iApply "HΦ". iSplitL "Hm"; first (iSplit; done).
    iLeft. iExists _, [], []. iSplit; first done.
    iFrame "Hsel".
    iSplit; first done. iSplit; first (iPureIntro; constructor).
    iPureIntro. intros ls'. apply match_labels_empty. }
  wp_auto.
  rewrite go.len_underlying (go.is_underlying (t := labels.Set') (tunder := labels.Set'ⁱᵐᵖˡ)).
  wp_apply (wp_map_len_resolved (K:=go_string) (V:=go_string) go.string go.string with "Hm").
  iIntros "Hm". wp_auto.
  simpl in Hsize_bound.
  wp_apply (wp_slice_make3 (V:=labels.Requirement.t) (t:=labels.Requirement)); first word.
  iIntros (requirements_sl) "(Hrequirements & Hrequirements_cap & %)".
  wp_auto.
  set P := (λ (keys : list go_string) (i : Z),
    ∃ (last_value last_key : go_string) (current_sl : slice.t)
      (entries : list (labels.Requirement.t * LabelRequirementV.t)),
      "Hv" ∷ value_ptr ↦ last_value ∗
      "Hk" ∷ label_ptr ↦ last_key ∗
      "Hrequirements_ptr" ∷ requirements_ptr ↦ current_sl ∗
      "Hrequirements" ∷ current_sl ↦* (fst <$> entries) ∗
      "Hrequirements_cap" ∷ own_slice_cap labels.Requirement.t current_sl (DfracOwn 1) ∗
      "Hentries" ∷ ([∗ list] entry ∈ entries, label_requirement_rep entry.1 entry.2) ∗
      "%Hentries_pure" ∷ ⌜ snd <$> entries = map_requirements (take (Z.to_nat i) keys) m ⌝)%I.
  wp_apply (wp_map_for_range_return_func (key_type:=go.string) P with "Hm"); first done.
  iIntros (keys) "%Hkeys".
  destruct Hkeys as (Hkeys_dom & Hkeys_len & Hkeys_nodup).
  iSplitL "value label requirements Hrequirements Hrequirements_cap".
  { iExists ""%go, ""%go, requirements_sl, [].
    rewrite /P fmap_nil take_0 /=. iFrame. done. }
  iSplitL "".
  { iModIntro. iIntros (i key value) "%Hiter Hloop".
    destruct Hiter as (Hi_bounds & Hkey_lookup & Hvalue_lookup).
    iDestruct "Hloop" as (last_value last_key current_sl entries)
      "(Hv & Hk & Hrequirements_ptr & Hrequirements & Hrequirements_cap & #Hentries & %Hentries_pure)".
    simpl subst'.
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros (value_sl) "[Hvalue_sl _]". wp_auto.
    iMod (own_slice_persist with "Hvalue_sl") as "#Hvalue_sl".
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros (one_sl) "[Hone_sl _]". wp_auto.
    wp_apply (wp_slice_append with "[$Hrequirements $Hrequirements_cap $Hone_sl]").
    iIntros (current_sl') "(Hrequirements & Hrequirements_cap & Hone_sl)".
    wp_auto.
    iRight. iSplit; first done.
    iExists value, key, current_sl',
      (entries ++ [(_, map_label_requirement key value)]).
    iFrame.
    iSplit.
    { iExactEq "Hrequirements". rewrite /named. f_equal. rewrite fmap_app /=. done. }
    iSplit.
    { rewrite big_sepL_snoc /=. iFrame "#".
      rewrite /label_requirement_rep /map_label_requirement /=.
      iFrame "#". done. }
    iPureIntro.
    rewrite fmap_app /= Hentries_pure.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite (take_S_r _ _ _ Hkey_lookup).
    symmetry. apply map_requirements_snoc. exact Hvalue_lookup. }
  iIntros "Hm Hloop".
  iDestruct "Hloop" as (last_value last_key map_requirements_sl map_entries)
    "(Hv & Hk & Hrequirements_ptr & Hrequirements & Hrequirements_cap & #Hmap_entries & %Hmap_entries_pure)".
  assert (snd <$> map_entries = map_requirements keys m) as Hmap_entries_all.
  { rewrite Hmap_entries_pure.
    replace (Z.to_nat (Z.of_nat (size m))) with (length keys) by lia.
    rewrite take_ge //. }
  wp_auto.
  iAssert (by_key_contents map_requirements_sl map_entries)
    with "[$Hrequirements $Hmap_entries]" as "Hsort_contents".
  wp_bind ((let: "$a0" := Convert labels.ByKey sort.Interface #map_requirements_sl in
    (FuncResolve sort.Sort [] #()) "$a0")%E).
  iApply (wp_Sort labels.ByKey by_key_contents map_requirements_sl map_entries
    with "[$Hsort_init $Hsort_contents]").
  iNext.
  iIntros (sorted_entries) "[Hsort_contents %Hperm]".
  iDestruct "Hsort_contents" as "[Hret #Hsorted_entries]".
  iEval (rewrite big_sepL_requirement_entries) in "Hsorted_entries".
  iMod (own_slice_persist with "Hret") as "#Hret".
  wp_auto.
  iModIntro. iApply "HΦ". iSplitL "Hm"; first (iSplit; done).
  iLeft.
  iExists map_requirements_sl, (fst <$> sorted_entries), (snd <$> sorted_entries).
  iSplit; first done.
  iFrame "#".
  assert (snd <$> map_entries ≡ₚ snd <$> sorted_entries) as Hperm_snd.
  { apply Permutation_map. exact Hperm. }
  iSplit.
  { iPureIntro. rewrite -Hperm_snd Hmap_entries_all. apply map_requirements_supported. }
  iPureIntro. intros ls'. change (default ∅ (Some m)) with m.
  rewrite -(map_requirements_match keys m ls' Hkeys_dom) -Hmap_entries_all.
  apply selector_matches_permutation. exact Hperm_snd.
Qed.

Lemma wp_Set__AsSelectorPreValidated l ls dq :
  Z.of_nat (size (default ∅ ls)) ≤ 2 ^ 63 - 1 →
  {{{ is_pkg_init labels ∗ labels_set_rep l ls dq }}}
    (l @! labels.Set' @! "AsSelectorPreValidated" #())%E
  {{{ selector, RET #selector;
      labels_set_rep l ls dq ∗
      is_selector selector (LabelSelectorV.match_labels (Some (default ∅ ls)))
  }}}.
Proof.
  intros Hsize_bound.
  wp_start as "Hls".
  wp_auto.
  wp_apply (wp_SelectorFromValidatedSet with "[$Hls]"); first done.
  iIntros (selector) "H". wp_auto.
  iApply "HΦ". iExact "H".
Qed.

End proof.
