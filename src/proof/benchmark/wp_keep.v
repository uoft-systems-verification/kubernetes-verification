From New.proof Require Import prelude empty_ffi wp_apply_keep.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}.
Local Set Default Proof Using "All".

Lemma wp_apply_keep_later (l : loc) (n : w64) (P : iProp Σ) :
  {{{ l ↦ n ∗
      ▷ P
  }}}
    (let: "n" := GoLoad go.uint64 #l in "n")%E
  {{{ RET #n;
      l ↦ n ∗
      ▷ P
  }}}.
Proof.
  wp_start_folded as "[Hl HP]".
  wp_apply_keep (wp_load with "Hl") as "Hl".
  iApply "HΦ". iSplitL "Hl"; [iExact "Hl"|iExact "HP"].
Qed.

Lemma wp_apply_keep_no_auto (l : loc) (n : w64) (P : iProp Σ) :
  {{{ l ↦ n ∗
      ▷ P
  }}}
    (let: "n" := GoLoad go.uint64 #l in "n")%E
  {{{ RET #n;
      l ↦ n ∗
      ▷ P
  }}}.
Proof.
  wp_start_folded as "[Hl HP]".
  wp_apply_keep (wp_load with "Hl") as "Hl" --no-auto.
  wp_auto_keep.
  iApply "HΦ". iSplitL "Hl"; [iExact "Hl"|iExact "HP"].
Qed.

Lemma wp_if_destruct_keep_later (b : bool) (P : iProp Σ) :
  ▷ P -∗ WP (if: #(bool_decide (b = true)) then #() else #())%E {{ _, ▷ P }}.
Proof.
  iIntros "HP".
  wp_if_destruct_keep.
  all: iExact "HP".
Qed.

Lemma wp_for_keep_later (P : iProp Σ) :
  ▷ P -∗
  WP (for: (λ: <>, #false); (λ: <>, #()) := (λ: <>, #()))%E {{ _, ▷ P }}.
Proof.
  iIntros "HP".
  wp_auto_keep.
  wp_for_keep.
  iExact "HP".
Qed.
End proof.
