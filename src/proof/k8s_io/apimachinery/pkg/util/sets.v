From New.proof Require Import prelude empty_ffi.
From New.proof.k8s_io.apimachinery.pkg.util Require Export sets_init.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : sets.Assumptions}.
Collection W := sem + package_sem.

Lemma wp_Set__Has_string (s : loc) (m : gmap go_string sets.Empty.t) dq (item : go_string) :
  {{{ s ↦${dq} m }}}
    s @! (sets.Set' go.string) @! "Has" #item
  {{{ RET #(bool_decide (item ∈ dom m)); s ↦${dq} m }}}.
Proof using W.
  wp_start as "Hs".
  wp_auto.
  wp_apply (wp_map_lookup2 with "Hs").
  iIntros "Hs".
  wp_auto.
  assert (bool_decide (is_Some (m !! item)) = bool_decide (item ∈ dom m)) as ->.
  { apply bool_decide_ext. symmetry. apply elem_of_dom. }
  iApply "HΦ". iFrame.
Qed.

Lemma wp_Set__HasAll_string (s : loc) (m : gmap go_string sets.Empty.t) dq sl items dq_sl :
  {{{ s ↦${dq} m ∗
      sl ↦*{dq_sl} items ∗
      ⌜ Forall (λ item, item ∈ dom m) items ⌝
  }}}
    s @! (sets.Set' go.string) @! "HasAll" #sl
  {{{ RET #true;
      s ↦${dq} m ∗
      sl ↦*{dq_sl} items
  }}}.
Proof using W.
  wp_start as "(Hs & Hitems & %Hall)".
  wp_auto.
  iDestruct (own_slice_len with "Hitems") as %[Hlen Hlen_nonneg].
  set I := (∃ (i : w64) (item : go_string),
    "Hi" ∷ i_ptr ↦ i ∗
    "Hitem" ∷ item_ptr ↦ item ∗
    "Hs" ∷ s ↦${dq} m ∗
    "Hitems" ∷ sl ↦*{dq_sl} items ∗
    "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z i ≤ length items ⌝)%I.
  iAssert I with "[i item Hs Hitems]" as "Hloop".
  { iExists (W64 0), ""%go. iFrame. iPureIntro. word. }
  wp_for "Hloop". wp_if_destruct.
  - list_elem items (sint.Z i) as current.
    assert (0 ≤ sint.Z i < sint.Z (slice.len sl)) as Hbounds by word.
    rewrite decide_True; [exact Hbounds|].
    wp_apply (wp_load_slice_index with "[$Hitems]"); [word|iPureIntro; exact Hcurrent_lookup|].
    iIntros "Hitems". wp_auto.
    wp_method_call. wp_auto.
    wp_apply (wp_Set__Has_string with "Hs"). iIntros "Hs".
    assert (current ∈ dom m) as Hcurrent.
    { rewrite Forall_lookup in Hall. exact (Hall _ _ Hcurrent_lookup). }
    rewrite bool_decide_true //.
    wp_auto.
    iApply wp_for_post_do. wp_auto.
    iFrame "HΦ s".
    iExists (word.add i (W64 1)), current. iFrame. iPureIntro. word.
  - iApply "HΦ". iFrame.
Qed.

Lemma wp_String__HasAll (s : loc) (m : gmap go_string sets.Empty.t) dq sl items dq_sl :
  {{{ s ↦${dq} m ∗
      sl ↦*{dq_sl} items ∗
      ⌜ Forall (λ item, item ∈ dom m) items ⌝
  }}}
    s @! sets.String @! "HasAll" #sl
  {{{ RET #true;
      s ↦${dq} m ∗
      sl ↦*{dq_sl} items
  }}}.
Proof using W.
  wp_start as "(Hs & Hitems & %Hall)". wp_auto.
  wp_func_call. rewrite /sets.castⁱᵐᵖˡ. wp_call. wp_auto.
  wp_apply (wp_Set__HasAll_string with "[$Hs $Hitems]"); first done.
  iIntros "[Hs Hitems]". wp_auto. iApply "HΦ". iFrame.
Qed.

End proof.
