From iris.algebra Require Export big_op.
From Perennial.Helpers Require Import ipm.
From Perennial.algebra.big_op Require Import big_sepM.

Set Default Proof Using "Type".

Section map2.
  Context {PROP : bi} `{!BiAffine PROP, !BiPersistentlyForall PROP}.
  Context `{Countable K} {A B : Type}.
  Implicit Types Φ Ψ : K → A → B → PROP.

  Lemma big_sepM2_split_singleton Φ (key : K) (v1: A) (v2: B) (m1 : gmap K A) (m2 : gmap K B) :
    m1 !! key = Some v1 → m2 !! key = Some v2 →
      ⊢
      ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) ∗-∗
      (Φ key v1 v2 ∗ ([∗ map] k↦y1;y2 ∈ delete key m1;delete key m2, Φ k y1 y2)).
  Proof using BiAffine0 BiPersistentlyForall0.
    intros m1_lookup m2_lookup.
    iSplit.
    - iIntros "big_sep".
      iDestruct (big_sepM2_filter Φ (λ k, k = key) m1 m2 with "big_sep") as "[Hkey Hrest]".
      iSplitL "Hkey".
      + assert (filter (λ x, x.1 = key) m1 = {[ key := v1 ]}) as ->.
        { apply map_eq. intros k.
          rewrite map_lookup_filter lookup_singleton.
          destruct (decide (key = k)); subst.
          - rewrite m1_lookup. unfold guard. simpl.
            case_decide; done.
          - destruct (m1 !! k) as [v|] eqn:Hlook; simpl; auto.
            unfold guard. simpl.
            case_decide; auto; congruence. }
        assert (filter (λ x, x.1 = key) m2 = {[ key := v2 ]}) as ->.
        { apply map_eq. intros k.
          rewrite map_lookup_filter lookup_singleton.
          destruct (decide (key = k)); subst.
          - rewrite m2_lookup. unfold guard. simpl.
            case_decide; done.
          - destruct (m2 !! k) as [v|] eqn:Hlook; simpl; auto.
            unfold guard. simpl.
            case_decide; auto; congruence. }
        rewrite big_sepM2_singleton. iFrame.
      + assert (filter (λ x, x.1 ≠ key) m1 = delete key m1) as ->.
        { apply map_eq. intros k.
          rewrite map_lookup_filter lookup_delete.
          destruct (decide (k = key)) as [Heq|Hneq]; subst.
          - destruct (m1 !! key) as [v'|] eqn:Hlook1; simpl.
            + rewrite m1_lookup. unfold guard. simpl.
              destruct (decide (key = key)); simpl; [ | congruence ].
              case_decide; [ contradiction | reflexivity ].
            + done.
          - destruct (m1 !! k) as [v|] eqn:Hlook; simpl.
            + unfold guard.
              destruct (decide (key = k)); [ congruence | ].
              case_decide; [ reflexivity | contradiction ].
            + destruct (decide (key = k)); congruence. }
        assert (filter (λ x, x.1 ≠ key) m2 = delete key m2) as ->.
        { apply map_eq. intros k.
          rewrite map_lookup_filter lookup_delete.
          destruct (decide (k = key)) as [Heq|Hneq]; subst.
          - destruct (m2 !! key) as [v'|] eqn:Hlook2; simpl.
            + rewrite m2_lookup. unfold guard.
              destruct (decide (key = key)); simpl; [ | congruence ].
              case_decide; [ contradiction | reflexivity ].
            + done.
          - destruct (m2 !! k) as [v|] eqn:Hlook; simpl.
            + unfold guard.
              destruct (decide (key = k)); [ congruence | ].
              case_decide; [ reflexivity | contradiction ].
            + destruct (decide (key = k)); congruence. }
        iFrame.
    - iIntros "[Hkey Hrest]".
      iApply (big_sepM2_filter Φ (λ k, k = key) m1 m2). iSplitL "Hkey".
      + assert (filter (λ x, x.1 = key) m1 = {[ key := v1 ]}) as ->.
        { apply map_eq. intros k.
          rewrite map_lookup_filter lookup_singleton.
          destruct (decide (key = k)); subst.
          - rewrite m1_lookup. unfold guard. simpl.
            case_decide; done.
          - destruct (m1 !! k) as [v|] eqn:Hlook; simpl; auto.
            unfold guard. simpl.
            case_decide; auto; congruence. }
        assert (filter (λ x, x.1 = key) m2 = {[ key := v2 ]}) as ->.
        { apply map_eq. intros k.
          rewrite map_lookup_filter lookup_singleton.
          destruct (decide (key = k)); subst.
          - rewrite m2_lookup. unfold guard. simpl.
            case_decide; done.
          - destruct (m2 !! k) as [v|] eqn:Hlook; simpl; auto.
            unfold guard. simpl.
            case_decide; auto; congruence. }
        rewrite big_sepM2_singleton. iFrame.
      + assert (filter (λ x, x.1 ≠ key) m1 = delete key m1) as ->.
        { apply map_eq. intros k.
          rewrite map_lookup_filter lookup_delete.
          destruct (decide (k = key)) as [Heq|Hneq]; subst.
          - destruct (m1 !! key) as [v'|] eqn:Hlook1; simpl.
            + rewrite m1_lookup. unfold guard. simpl.
            destruct (decide (key = key)); simpl; [ | congruence ].
            case_decide; [ contradiction | reflexivity ].
            + done.
          - destruct (m1 !! k) as [v|] eqn:Hlook; simpl.
            + unfold guard, guard_or. simpl.
              destruct (decide (key = k)); [ congruence | ]. simpl.
              case_decide; [ reflexivity | contradiction ].
            + destruct (decide (key = k)); congruence. }
        assert (filter (λ x, x.1 ≠ key) m2 = delete key m2) as ->.
        { apply map_eq. intros k.
          rewrite map_lookup_filter lookup_delete.
          destruct (decide (k = key)) as [Heq|Hneq]; subst.
          - destruct (m2 !! key) as [v'|] eqn:Hlook2; simpl.
            + rewrite m2_lookup. unfold guard. simpl.
              destruct (decide (key = key)); simpl; [ | congruence ].
              case_decide; [ contradiction | reflexivity ].
            + done.
          - destruct (m2 !! k) as [v|] eqn:Hlook; simpl.
            + unfold guard. simpl.
              destruct (decide (key = k)); [ congruence | ]. simpl.
              case_decide; [ reflexivity | contradiction ].
            + destruct (decide (key = k)); congruence. }
        iFrame.
  Qed.

End map2.
