From New.proof Require Import prelude.
From iris.algebra Require Import agree auth gmap.
From iris.base_logic.lib Require Import own.

Section mono_gmap.
Context (K V : Type) `{Countable K}.

Definition mono_gmapUR : ucmra := authUR (gmapUR K (agreeR (leibnizO V))).

Implicit Types k : K.
Implicit Types v : V.
Implicit Types m : gmap K V.

Definition to_mono_gmap (m : gmap K V) : gmap K (agreeR (leibnizO V)) :=
  to_agree <$> m.

Lemma to_mono_gmap_valid m:
  ✓ to_mono_gmap m.
Proof.
  intros k.
  rewrite /to_mono_gmap lookup_fmap.
  destruct (m !! k); done.
Qed.

Lemma singleton_included_lookup m k v:
  {[k := to_agree (v : leibnizO V)]} ≼ to_mono_gmap m →
  m !! k = Some v.
Proof.
  rewrite singleton_included_l /to_mono_gmap lookup_fmap.
  intros (av & Hav & Hincl).
  apply fmap_Some_equiv in Hav as (v' & Hlookup & Hav).
  rewrite Hlookup.
  f_equal.
  apply Some_included in Hincl as [Hagree|Hincl].
  - assert (to_agree (v : leibnizO V) ≡ to_agree (v' : leibnizO V)) as Hagree'.
    { etrans; [exact Hagree|exact Hav]. }
    apply (inj to_agree), leibniz_equiv in Hagree'.
    done.
  - assert (to_agree (v : leibnizO V) ≼ to_agree (v' : leibnizO V)) as Hincl'.
    { rewrite -Hav. exact Hincl. }
    apply to_agree_included_L in Hincl'.
    done.
Qed.

Lemma auth_frag_lookup_valid m k v:
  ✓ (● (to_mono_gmap m) ⋅ ◯ {[k := to_agree (v : leibnizO V)]}) →
  m !! k = Some v.
Proof.
  intros Hvalid.
  pose proof (proj1 (auth_both_valid_discrete
    (to_mono_gmap m) ({[k := to_agree (v : leibnizO V)]})) Hvalid) as [Hincl _].
  by apply singleton_included_lookup in Hincl.
Qed.

Lemma insert m k v:
  m !! k = None →
  ● (to_mono_gmap m) ~~>
    ● (to_mono_gmap (<[k := v]> m)) ⋅ ◯ {[k := to_agree (v : leibnizO V)]}.
Proof.
  intros Hlookup.
  rewrite /to_mono_gmap fmap_insert.
  apply auth_update_alloc.
  eapply (@alloc_singleton_local_update _ K _ _ (agreeR (leibnizO V))
    (to_agree <$> m) k (to_agree (v : leibnizO V))).
  - rewrite lookup_fmap Hlookup.
    reflexivity.
  - done.
Qed.

Lemma lookup_alloc m k v:
  m !! k = Some v →
  ● (to_mono_gmap m) ~~>
    ● (to_mono_gmap m) ⋅ ◯ {[k := to_agree (v : leibnizO V)]}.
Proof.
  intros Hlookup.
  apply auth_update_dfrac_alloc.
  - apply _.
  - rewrite singleton_included_l /to_mono_gmap lookup_fmap Hlookup.
    exists (to_agree (v : leibnizO V)).
    split; reflexivity.
Qed.

Class mono_gmapG Σ :=
  { #[global] mono_gmap_inG :: inG Σ mono_gmapUR; }.

Definition mono_gmapΣ :=
  #[GFunctor mono_gmapUR].

#[global]
Instance subG_mono_gmapG Σ :
  subG mono_gmapΣ Σ → mono_gmapG Σ.
Proof. solve_inG. Qed.

Context `{!mono_gmapG Σ}.

Global Instance own_auth_timeless γ m : Timeless (own γ (● (to_mono_gmap m))).
Proof. apply _. Qed.

Global Instance own_frag_timeless γ k v :
  Timeless (own γ (◯ {[k := to_agree (v : leibnizO V)]})).
Proof. apply _. Qed.

Global Instance own_frag_persistent γ k v :
  Persistent (own γ (◯ {[k := to_agree (v : leibnizO V)]})).
Proof. apply _. Qed.

Definition own_auth γ m : iProp Σ :=
  own γ (● (to_mono_gmap m)).

Definition own_frag γ k v : iProp Σ :=
  own γ (◯ {[k := to_agree (v : leibnizO V)]}).

Lemma alloc m:
  ⊢ |==> ∃ γ, own_auth γ m.
Proof.
  iMod (own_alloc (● (to_mono_gmap m))) as (γ) "Hauth".
  { apply auth_auth_valid. apply to_mono_gmap_valid. }
  iModIntro.
  iExists γ.
  iFrame.
Qed.

Lemma frag_elem_of_auth {γ m k v}:
  own_auth γ m -∗ own_frag γ k v -∗ ⌜ m !! k = Some v ⌝.
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
  iPureIntro.
  by apply auth_frag_lookup_valid.
Qed.

Lemma frag_agree {γ k v1 v2}:
  own_frag γ k v1 -∗ own_frag γ k v2 -∗ ⌜ v1 = v2 ⌝.
Proof.
  iIntros "Hfrag1 Hfrag2".
  iDestruct (own_valid_2 with "Hfrag1 Hfrag2") as %Hvalid.
  iPureIntro.
  apply (iffLR (auth_frag_valid _)) in Hvalid.
  rewrite singleton_op singleton_valid to_agree_op_valid_L in Hvalid.
  done.
Qed.

Lemma insert_vs {γ m} k v:
  m !! k = None →
  own_auth γ m ==∗ own_auth γ (<[k := v]> m) ∗ own_frag γ k v.
Proof.
  iIntros (Hlookup) "Hauth".
  iMod (own_update with "Hauth") as "H".
  { by apply insert. }
  iModIntro.
  iDestruct (own_op with "H") as "[$ $]".
Qed.

Lemma lookup_vs {γ m} k v:
  m !! k = Some v →
  own_auth γ m ==∗ own_auth γ m ∗ own_frag γ k v.
Proof.
  iIntros (Hlookup) "Hauth".
  iMod (own_update with "Hauth") as "H".
  { by apply lookup_alloc. }
  iModIntro.
  iDestruct (own_op with "H") as "[$ $]".
Qed.

End mono_gmap.
