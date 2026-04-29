From New.proof Require Import prelude.
From iris.algebra Require Import auth gset.

Section mono_gset.
Context (A : Type) `{Countable A}.

Definition mono_gsetUR : ucmra := authUR (gsetUR A).
Implicit Types a : A.
Implicit Types s : gset A.

Lemma auth_frag_valid s a:
✓ (● s ⋅ ◯ {[a]}) → a ∈ s.
Proof.
  intros Hvalid.
  pose proof (proj1 (auth_both_valid_discrete s ({[a]})) Hvalid) as [Hincl _].
  apply gset_included in Hincl.
  apply Hincl.
  apply elem_of_singleton.
  reflexivity.
Qed.

Lemma insert s a:
● s ~~> ● (s ∪ {[a]}) ⋅ ◯ {[a]}.
Proof.
  eapply auth_update_alloc.
  apply local_update_unital_discrete.
  intros z _ Hz.
  apply leibniz_equiv in Hz.
  rewrite left_id_L in Hz.
  subst z.
  split; [done|].
  rewrite gset_op.
  set_solver.
Qed.

Class mono_gsetG Σ :=
  { #[global] mono_gset_inG :: inG Σ mono_gsetUR; }.

Definition mono_gsetΣ :=
  #[GFunctor mono_gsetUR].

#[global]
Instance subG_mono_gsetG Σ :
  subG mono_gsetΣ Σ → mono_gsetG Σ.
Proof. solve_inG. Qed.

Context `{!mono_gsetG Σ}.

Global Instance own_auth_timeless γ s : Timeless (own γ (● s)).
Proof. apply _. Qed.

Global Instance own_frag_timeless γ s : Timeless (own γ (◯ s)).
Proof. apply _. Qed.

Global Instance own_frag_persistent γ s : Persistent (own γ (◯ s)).
Proof. apply _. Qed.

Definition own_auth γ s : iProp Σ :=
  own γ (● s).

Definition own_frag γ a : iProp Σ :=
  own γ (◯ {[a]}).

Lemma frag_elem_of_auth {γ s} a:
  own_auth γ s -∗ own_frag γ a -∗ ⌜ a ∈ s ⌝.
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
  iPureIntro.
  eapply auth_frag_valid.
  done.
Qed.

Lemma insert_vs {γ s} a:
  own_auth γ s ==∗ own_auth γ (s ∪ {[a]}) ∗ own_frag γ a.
Proof.
  iIntros "Hauth".
  iMod (own_update with "Hauth") as "H".
  { apply insert. }
  iModIntro.
  iDestruct (own_op with "H") as "[$ $]".
Qed.

End mono_gset.
