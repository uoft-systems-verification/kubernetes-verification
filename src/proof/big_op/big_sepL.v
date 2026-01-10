From iris.algebra Require Export big_op.
From Perennial.Helpers Require Import ipm.

Set Default Proof Using "Type".

Section list.
  Context {PROP : bi}.
  Implicit Types (A : Type).

  Lemma big_sepL_head_tail {A} (Φ: nat → A → PROP) (l : list A) (v : A) :
    l !! 0 = Some v →
      ⊢ ([∗ list] k ↦ x ∈ l, Φ k x) -∗
        Φ 0 v ∗ ([∗ list] k ↦ x ∈ drop 1 l, Φ (S k) x).
  Proof.
    intros l_lookup. iIntros "big_sep".
    assert (l = v :: drop 1 l) as ->.
    { destruct l as [|x l]; simpl in l_lookup; [congruence|]. inversion l_lookup. reflexivity. }
    rewrite big_sepL_cons. iFrame.
  Qed.

Section list2.
  Context {A B : Type}.
  Implicit Types Φ Ψ : nat → A → B → PROP.


  Lemma big_sepL2_head_tail Φ (l1 : list A) (l2 : list B) (v1 : A) (v2 : B) :
    l1 !! 0 = Some v1 ∧ l2 !! 0 = Some v2 →
      ⊢ ([∗ list] k ↦ x ; y ∈ l1; l2, Φ k x y) -∗
        Φ 0 v1 v2 ∗ ([∗ list] k ↦ x ; y ∈ drop 1 l1; drop 1 l2, Φ (S k) x y).
  Proof.
    intros [l1_lookup l2_lookup]. iIntros "big_sep".
    assert (l1 = v1 :: drop 1 l1) as ->.
    { destruct l1 as [|x l1]; simpl in l1_lookup; [congruence|]. inversion l1_lookup. reflexivity. }
    assert (l2 = v2 :: drop 1 l2) as ->.
    { destruct l2 as [|x l2]; simpl in l2_lookup; [congruence|]. inversion l2_lookup. reflexivity. }
    rewrite big_sepL2_cons. iFrame.
  Qed.

End list2.

End list.
