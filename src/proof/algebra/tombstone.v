From New.proof Require Import prelude empty_ffi.
From New.proof.algebra Require Export mono_gset.
From New.proof.k8s_io.apimachinery.pkg.types Require Export types_init.

Section tombstone.

Definition tombstoneUR : ucmra := mono_gsetUR types.UID.t.

Class tombstoneG Σ :=
  { #[global] tombstone_mono_gsetG :: mono_gsetG types.UID.t Σ; }.

Definition tombstoneΣ :=
  mono_gsetΣ types.UID.t.

#[global]
Instance subG_tombstoneG Σ :
  subG tombstoneΣ Σ → tombstoneG Σ.
Proof.
  intros Hsub.
  constructor.
  exact (subG_mono_gsetG types.UID.t Σ Hsub).
Qed.

Context `{!tombstoneG Σ}.

Definition own_auth γ (tombed_uid: gset types.UID.t) : iProp Σ :=
  mono_gset.own_auth types.UID.t γ tombed_uid.

Definition own_frag γ (uid: types.UID.t) : iProp Σ :=
  mono_gset.own_frag types.UID.t γ uid.

Global Instance own_auth_timeless γ tombed_uid : Timeless (own_auth γ tombed_uid).
Proof. unfold own_auth. apply _. Qed.

Global Instance own_frag_timeless γ uid : Timeless (own_frag γ uid).
Proof. unfold own_frag. apply _. Qed.

Global Instance own_frag_persistent γ uid : Persistent (own_frag γ uid).
Proof. unfold own_frag. apply _. Qed.

Lemma frag_elem_of_auth {γ tombed_uid} uid:
  own_auth γ tombed_uid -∗ own_frag γ uid -∗ ⌜ uid ∈ tombed_uid ⌝.
Proof.
  unfold own_auth, own_frag.
  apply (mono_gset.frag_elem_of_auth types.UID.t uid).
Qed.

Lemma insert_vs {γ tombed_uid} uid:
  own_auth γ tombed_uid ==∗ own_auth γ (tombed_uid ∪ {[uid]}) ∗ own_frag γ uid.
Proof.
  unfold own_auth, own_frag.
  apply (mono_gset.insert_vs types.UID.t uid).
Qed.

End tombstone.
