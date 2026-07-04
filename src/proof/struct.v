From New.proof Require Import prelude empty_ffi.

Lemma struct_fields_split `{hG: heapGS Σ} {V} `{!TypedPointsto (Σ:=Σ) V} l (v : V) dq :
  l ↦{dq} v ⊢@{iProp Σ} typed_pointsto_def l v dq ∗ ⌜l ≠ null⌝.
Proof. rewrite typed_pointsto_unseal /typed_pointsto_wrap. iIntros "[$ $]". Qed.

Lemma struct_fields_combine `{hG: heapGS Σ} {V} `{!TypedPointsto (Σ:=Σ) V} l (v : V) dq :
  l ≠ null →
  typed_pointsto_def l v dq ⊢@{iProp Σ} l ↦{dq} v.
Proof. intros Hnot_null. iApply (typed_pointsto_combine l v dq Hnot_null). Qed.
