From New.proof Require Import prelude.
From iris.algebra Require Import cmra gset view.
From iris.base_logic.lib Require Import own.

(* A linear ghost set whose authoritative set is constrained by [P]. Fragments
   own individual elements, imply membership in the authoritative set, and can be
   consumed to remove that element from the authoritative set. *)
Section constrained_gset.
Context {K : Type} `{Countable K}.
Context (P : K → Prop).

Definition authO : ofe := gsetO (leibnizO K).
Definition fragUR : ucmra := gset_disjUR K.

Implicit Types (a : authO) (b : fragUR).

Local Definition view_rel_raw (n : nat) a b : Prop :=
  set_Forall P a ∧ ∃ frag_keys, b = GSet frag_keys ∧ frag_keys ⊆ a.

Local Lemma view_rel_raw_mono n1 n2 a1 a2 b1 b2 :
  view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  (n2 ≤ n1)%nat →
  view_rel_raw n2 a2 b2.
Proof.
  intros [Hvalid_auth [frag_keys1 [Hb1 Hfrag_in_auth1]]] Ha Hb _.
  assert (Ha_equiv : a1 ≡ a2).
  { apply (proj2 (discrete_iff n2 a1 a2)). done. }
  assert (Ha_elem : ∀ key, key ∈ a1 ↔ key ∈ a2).
  { exact (proj1 (set_equiv a1 a2) Ha_equiv). }
  subst b1.
  apply cmra_discrete_included_iff in Hb.
  destruct b2 as [frag_keys2|].
  - split.
    { intros key Hkey.
      apply Hvalid_auth.
      apply Ha_elem.
      done. }
    exists frag_keys2. split; [done|].
    apply gset_disj_included in Hb.
    intros key Hkey.
    apply Ha_elem.
    apply Hfrag_in_auth1.
    apply Hb.
    done.
  - exfalso.
    destruct Hb as [[extra|] Hop]; simpl in Hop; try done.
Qed.

Local Lemma view_rel_raw_valid n a b :
  view_rel_raw n a b → ✓{n} b.
Proof.
  intros [_ [frag_keys [-> _]]].
  done.
Qed.

Local Lemma view_rel_raw_unit n :
  ∃ a, view_rel_raw n a ε.
Proof.
  exists (∅ : gset K).
  split.
  - intros key Hkey. Timeout 10 set_solver.
  - exists (∅ : gset K). split; [done|].
    Timeout 10 set_solver.
Qed.

Canonical Structure view_rel : view_rel authO fragUR :=
  ViewRel view_rel_raw view_rel_raw_mono
          view_rel_raw_valid view_rel_raw_unit.

Definition auth dq a : viewR view_rel := ●V{dq} a.
Definition frag b : viewR view_rel := ◯V b.

Local Notation "●CG a" := (auth 1 a) (at level 20).
Local Notation "◯CG b" := (frag b) (at level 20).

Class constrained_gsetG Σ :=
  { #[global] constrained_gset_inG :: inG Σ (viewR view_rel); }.

Definition constrained_gsetΣ :=
  #[GFunctor (viewR view_rel)].

#[global]
Instance subG_constrained_gsetG Σ :
  subG constrained_gsetΣ Σ → constrained_gsetG Σ.
Proof. solve_inG. Qed.

Context `{!constrained_gsetG Σ}.

Definition own_auth γ (reserved_keys : gset K) : iProp Σ :=
  own γ (●CG reserved_keys).

Definition own_frag γ (key : K) : iProp Σ :=
  own γ (◯CG (GSet {[key]})).

Global Instance own_auth_timeless γ reserved_keys :
  Timeless (own_auth γ reserved_keys).
Proof. unfold own_auth. apply _. Qed.

Global Instance own_frag_timeless γ key :
  Timeless (own_frag γ key).
Proof. unfold own_frag. apply _. Qed.

Lemma init :
  ⊢ |==> ∃ γ, own_auth γ (∅ : gset K).
Proof.
  unfold own_auth.
  iMod (own_alloc (●CG (∅ : gset K))) as (γ) "Hauth".
  { apply (proj2 (view_auth_dfrac_valid view_rel 1 (∅ : gset K))).
    split; [done|].
    intros n. split.
    - intros key Hkey. Timeout 10 set_solver.
    - exists (∅ : gset K). split; [done|].
      Timeout 10 set_solver.
  }
  iModIntro. iExists γ. iExact "Hauth".
Qed.

Lemma auth_set_Forall {γ reserved_keys} :
  own_auth γ reserved_keys -∗
  ⌜ set_Forall P reserved_keys ⌝.
Proof.
  unfold own_auth.
  iIntros "Hauth".
  iDestruct (own_valid with "Hauth") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid.
  iPureIntro.
  pose proof (proj1 (view_auth_dfrac_validN view_rel 0%nat 1 reserved_keys) Hvalid)
    as [_ Hrel].
  exact (proj1 Hrel).
Qed.

Lemma frag_elem_of_auth {γ reserved_keys} key :
  own_auth γ reserved_keys -∗
  own_frag γ key -∗
  ⌜ key ∈ reserved_keys ⌝.
Proof.
  unfold own_auth, own_frag.
  iIntros "Hauth Hfrag".
  iDestruct (own_valid_2 with "Hauth Hfrag") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid.
  iPureIntro.
  pose proof (proj1 (view_both_validN view_rel 0%nat reserved_keys (GSet {[key]})) Hvalid)
    as [_ [frag_keys [Hfrag_eq Hfrag_in_auth]]].
  injection Hfrag_eq as <-.
  apply Hfrag_in_auth.
  Timeout 10 set_solver.
Qed.

Lemma frag_pred {γ} key :
  own_frag γ key -∗
  ⌜ P key ⌝.
Proof.
  unfold own_frag.
  iIntros "Hfrag".
  iDestruct (own_valid with "Hfrag") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid.
  iPureIntro.
  pose proof (proj1 (view_frag_validN view_rel 0%nat (GSet {[key]})) Hvalid)
    as [reserved_keys [Hvalid_auth [frag_keys [Hfrag_eq Hfrag_in_auth]]]].
  injection Hfrag_eq as <-.
  apply Hvalid_auth.
  apply Hfrag_in_auth.
  Timeout 10 set_solver.
Qed.

Lemma reserve_key_vs {γ reserved_keys} key :
  key ∉ reserved_keys →
  P key →
  own_auth γ reserved_keys ==∗
    own_auth γ ({[key]} ∪ reserved_keys) ∗
    own_frag γ key.
Proof.
  unfold own_auth, own_frag.
  iIntros (Hkey_not_reserved Hkey_pred) "Hauth".
  rewrite -own_op.
  iApply (own_update with "Hauth").
  apply view_update_alloc.
  intros n bf [Hvalid_auth [frag_keys [-> Hfrag_in_auth]]].
  assert (Hdisj : {[key]} ## frag_keys).
  {
    intros key' Hkey' Hfrag.
    apply elem_of_singleton in Hkey'. subst.
    apply Hkey_not_reserved.
    apply Hfrag_in_auth.
    done.
  }
  rewrite (gset_disj_union {[key]} frag_keys Hdisj).
  split.
  - intros key' Hkey'.
    rewrite elem_of_union elem_of_singleton in Hkey'.
    destruct Hkey' as [->|Hkey']; [done|].
    apply Hvalid_auth. done.
  - exists ({[key]} ∪ frag_keys).
    split; [done|].
    Timeout 10 set_solver.
Qed.

Lemma consume_key_vs {γ reserved_keys} key :
  own_auth γ reserved_keys -∗
  own_frag γ key ==∗
    own_auth γ (reserved_keys ∖ {[key]}).
Proof.
  unfold own_auth, own_frag.
  iIntros "Hauth Hfrag".
  iApply (own_update_2 with "Hauth Hfrag").
  apply view_update_dealloc.
  intros n bf [Hvalid_auth [frag_keys [Hop Hfrag_in_auth]]].
  assert (Hvalid_op : ✓ (GSet {[key]} ⋅ bf)).
  { rewrite Hop. done. }
  destruct (gset_disj_valid_inv_l {[key]} bf Hvalid_op)
    as [other_frag_keys [-> Hdisj]].
  rewrite (gset_disj_union {[key]} other_frag_keys Hdisj) in Hop.
  injection Hop as <-.
  split.
  - intros key' Hkey'.
    apply Hvalid_auth. Timeout 10 set_solver.
  - exists other_frag_keys. split; [done|].
    Timeout 10 set_solver.
Qed.

End constrained_gset.
