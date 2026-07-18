From New.proof Require Import prelude.
From New.proof Require Export pure_objects.
From New.proof.algebra Require Import constrained_gset.

(* This predicate is intentionally axiomatized. The concrete definition is
   irrelevant here; the model only relies on API-server generated names never
   forming keys that satisfy it. *)
Axiom reserved_key_pred : KKey.t → Prop.

Class reserved_keysG Σ :=
  { #[global] reserved_keys_constrained_gsetG ::
      constrained_gset.constrained_gsetG reserved_key_pred Σ; }.

Definition reserved_keysΣ :=
  constrained_gset.constrained_gsetΣ reserved_key_pred.

#[global]
Instance subG_reserved_keysG Σ :
  subG reserved_keysΣ Σ → reserved_keysG Σ.
Proof.
  intros Hsub. constructor.
  exact (constrained_gset.subG_constrained_gsetG reserved_key_pred Σ Hsub).
Qed.

Section reserved_keys.
Context `{!reserved_keysG Σ}.

Definition own_auth γ (reserved_keys : gset KKey.t) : iProp Σ :=
  constrained_gset.own_auth reserved_key_pred γ reserved_keys.

Definition own_frag γ (key : KKey.t) : iProp Σ :=
  constrained_gset.own_frag reserved_key_pred γ key.

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
  apply (constrained_gset.init reserved_key_pred).
Qed.

Lemma auth_set_Forall {γ reserved_keys} :
  own_auth γ reserved_keys -∗
  ⌜ set_Forall reserved_key_pred reserved_keys ⌝.
Proof.
  unfold own_auth.
  apply (constrained_gset.auth_set_Forall reserved_key_pred).
Qed.

Lemma frag_elem_of_auth {γ reserved_keys} key :
  own_auth γ reserved_keys -∗
  own_frag γ key -∗
  ⌜ key ∈ reserved_keys ⌝.
Proof.
  unfold own_auth, own_frag.
  apply (constrained_gset.frag_elem_of_auth reserved_key_pred key).
Qed.

Lemma frag_pred {γ} key :
  own_frag γ key -∗
  ⌜ reserved_key_pred key ⌝.
Proof.
  unfold own_frag.
  apply (constrained_gset.frag_pred reserved_key_pred key).
Qed.

Lemma reserve_key_vs {γ reserved_keys} key :
  key ∉ reserved_keys →
  reserved_key_pred key →
  own_auth γ reserved_keys ==∗
    own_auth γ ({[key]} ∪ reserved_keys) ∗
    own_frag γ key.
Proof.
  unfold own_auth, own_frag.
  apply (constrained_gset.reserve_key_vs reserved_key_pred key).
Qed.

Lemma consume_reserved_key_vs {γ reserved_keys} key :
  own_auth γ reserved_keys -∗
  own_frag γ key ==∗
    own_auth γ (reserved_keys ∖ {[key]}).
Proof.
  unfold own_auth, own_frag.
  apply (constrained_gset.consume_key_vs reserved_key_pred key).
Qed.

End reserved_keys.
