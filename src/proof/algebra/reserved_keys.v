From New.proof Require Import prelude.
From New.proof Require Export pure_objects.
From New.ghost Require Import auth_set.

Section reserved_keys.
Context `{!allG Σ}.

Definition own_auth γ (reserved_keys : gset KKey.t) : iProp Σ :=
  auth_set_auth γ reserved_keys.

Definition own_frag γ (key : KKey.t) : iProp Σ :=
  auth_set_frag γ key.

Global Instance own_auth_timeless γ reserved_keys :
  Timeless (own_auth γ reserved_keys).
Proof. unfold own_auth. apply _. Qed.

Global Instance own_frag_timeless γ key :
  Timeless (own_frag γ key).
Proof. unfold own_frag. apply _. Qed.

Lemma init :
  ⊢ |==> ∃ γ, own_auth γ (∅ : gset KKey.t).
Proof.
  unfold own_auth.
  apply auth_set_init.
Qed.

Lemma frag_elem_of_auth {γ reserved_keys} key :
  own_auth γ reserved_keys -∗
  own_frag γ key -∗
  ⌜ key ∈ reserved_keys ⌝.
Proof.
  unfold own_auth, own_frag.
  apply auth_set_elem.
Qed.

Lemma reserve_key_vs {γ reserved_keys} key :
  key ∉ reserved_keys →
  own_auth γ reserved_keys ==∗
    own_auth γ ({[key]} ∪ reserved_keys) ∗
    own_frag γ key.
Proof.
  unfold own_auth, own_frag.
  apply auth_set_alloc.
Qed.

Lemma consume_reserved_key_vs {γ reserved_keys} key :
  own_auth γ reserved_keys -∗
  own_frag γ key ==∗
    own_auth γ (reserved_keys ∖ {[key]}).
Proof.
  unfold own_auth, own_frag.
  iIntros "Hauth Hfrag".
  iApply (auth_set_dealloc with "[$Hauth $Hfrag]").
Qed.

End reserved_keys.
