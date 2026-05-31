From New.proof Require Import prelude.
From iris.algebra Require Import cmra gmap gset.
From iris.base_logic.lib Require Import own.
From New.proof.algebra Require Import counted_reversed_reference.

(*
  reversed_reference is the set-shaped specialization of
  counted_reversed_reference. Each value extracts a set of references; the
  counted core represents each set member with count 1. The public fragment
  shape remains [r ↦ gset K].
*)

Section reversed_reference_frag.
Context (K : Type) `{Countable K} (R : Type) `{Countable R}.

Definition fragUR : ucmra := gmapUR R (prodR dfracR (agreeR (gset K))).

Definition mk_frag (p : R) (dq : dfrac) (ks : gset K) : fragUR :=
  {[p := (dq, to_agree ks)]}.

End reversed_reference_frag.

Arguments fragUR _ {_ _} _ {_ _}.
Arguments mk_frag {_ _ _ _ _ _} _ _ _.

Section reversed_reference.
Context (K : Type) `{Countable K} (R : Type) `{Countable R} (V : Type).
Context (extract_reference_set : V → gset R) (to_reference : K → V → R).

Definition reverse_index (state : gmap K V) (r : R) : gset K :=
  dom (filter (λ '(_, v), r ∈ extract_reference_set v) state).

Definition extract_reference_count (v : V) : gmap R nat :=
  gset_to_gmap 1 (extract_reference_set v).

Definition counted_reverse_index (state : gmap K V) (r : R) : gmap K nat :=
  @counted_reversed_reference.reverse_index
    K _ _ R _ _ V extract_reference_count state r.

Lemma counted_reverse_index_eq state r :
  counted_reverse_index state r = gset_to_gmap 1 (reverse_index state r).
Proof.
  apply map_eq. intros k.
  unfold counted_reverse_index, counted_reversed_reference.reverse_index,
    counted_reversed_reference.reference_count, extract_reference_count,
    reverse_index.
  rewrite map_lookup_imap lookup_gset_to_gmap.
  destruct (state !! k) as [v|] eqn:Hlookup; simpl.
  - rewrite lookup_gset_to_gmap.
    assert (Hdom : k ∈ dom (filter (λ '(_, v0), r ∈ extract_reference_set v0) state) ↔
      r ∈ extract_reference_set v).
    { rewrite elem_of_dom. split.
      - intros [v0 Hfilter].
        apply map_lookup_filter_Some in Hfilter as [Hlookup0 Hr].
        rewrite Hlookup in Hlookup0. inversion Hlookup0. done.
      - intros Hr.
        exists v. apply map_lookup_filter_Some. done.
    }
    destruct (decide (r ∈ extract_reference_set v)) as [Hr|Hnot];
      destruct (decide (k ∈ dom (filter (λ '(_, v0), r ∈ extract_reference_set v0) state))) as [Hk|Hknot];
      simpl.
    + rewrite (option_guard_True (r ∈ extract_reference_set v) (Some 1) Hr).
      rewrite (option_guard_True
        (k ∈ dom (filter (λ '(_, v0), r ∈ extract_reference_set v0) state))
        (Some 1) Hk).
      simpl. destruct (decide (0 < 1)%nat); [reflexivity|lia].
    + exfalso. apply Hknot. by apply Hdom.
    + exfalso. apply Hnot. by apply Hdom.
    + rewrite (option_guard_False (r ∈ extract_reference_set v) Hnot).
      rewrite (option_guard_False
        (k ∈ dom (filter (λ '(_, v0), r ∈ extract_reference_set v0) state))
        Hknot).
      done.
  - destruct (decide (k ∈ dom (filter (λ '(_, v0), r ∈ extract_reference_set v0) state))) as [Hk|Hk].
    + exfalso.
      apply elem_of_dom in Hk as [v Hfilter].
      apply map_lookup_filter_Some in Hfilter as [Hlookup0 _].
      rewrite Hlookup in Hlookup0. done.
    + rewrite (option_guard_False
        (k ∈ dom (filter (λ '(_, v0), r ∈ extract_reference_set v0) state))
        Hk).
      done.
Qed.

Class reversed_referenceG Σ :=
  { #[global] reversed_reference_countedG ::
      @counted_reversed_reference.counted_reversed_referenceG
        K _ _ R _ _ V extract_reference_count to_reference Σ; }.

Definition reversed_referenceΣ :=
  @counted_reversed_reference.counted_reversed_referenceΣ
    K _ _ R _ _ V extract_reference_count to_reference.

#[global]
Instance subG_reversed_referenceG Σ :
  subG reversed_referenceΣ Σ → reversed_referenceG Σ.
Proof.
  intros Hsub.
  constructor.
  exact (@counted_reversed_reference.subG_counted_reversed_referenceG
    K _ _ R _ _ V extract_reference_count to_reference Σ Hsub).
Qed.

Context `{!reversed_referenceG Σ}.

Definition own_auth γ (state: gmap K V) (used_reference: gset R) : iProp Σ :=
  @counted_reversed_reference.own_auth
    K _ _ R _ _ V extract_reference_count to_reference Σ _
    γ (state, used_reference).

Definition own_frag γ r dq ks : iProp Σ :=
  @counted_reversed_reference.own_frag
    K _ _ R _ _ V extract_reference_count to_reference Σ _
    γ r dq (gset_to_gmap 1 ks).

Global Instance own_auth_timeless γ state used_reference :
  Timeless (own_auth γ state used_reference).
Proof. apply _. Qed.

Global Instance own_frag_timeless γ r dq ks :
  Timeless (own_frag γ r dq ks).
Proof. apply _. Qed.

Definition map_reverse_index (state : gmap K V) (r : R) : gset K :=
  dom (filter (λ '(_, v), r ∈ extract_reference_set v) state).

Local Lemma map_raw_reverse_index_eq state r :
  @counted_reversed_reference.reverse_index
    K _ _ R _ _ V extract_reference_count state r =
    gset_to_gmap 1 (map_reverse_index state r).
Proof.
  apply counted_reverse_index_eq.
Qed.

Lemma own_auth_frag_valid {γ state used_reference r dq ks}:
  own_auth γ state used_reference -∗
  own_frag γ r dq ks -∗
  ⌜ ks = map_reverse_index state r ⌝ ∗
  ⌜ r ∈ used_reference ⌝.
Proof.
  unfold own_auth, own_frag.
  iIntros "Hauth Hfrag".
  iDestruct (@counted_reversed_reference.own_auth_frag_valid
    K _ _ R _ _ V extract_reference_count to_reference Σ _
    γ (state, used_reference) r dq (gset_to_gmap 1 ks)
    with "Hauth Hfrag") as "[%Hks %Hr]".
  iPureIntro. split; [|done].
  simpl in Hks.
  rewrite map_raw_reverse_index_eq in Hks.
  apply (f_equal dom) in Hks.
  rewrite !dom_gset_to_gmap in Hks.
  done.
Qed.

Local Lemma dom_filter_insert_preserve
    (m : gmap K V) k v v' r :
  m !! k = Some v →
  (r ∈ extract_reference_set v' ↔ r ∈ extract_reference_set v) →
  map_reverse_index (<[k := v']> m) r = map_reverse_index m r.
Proof.
  intros Hlookup Hiff.
  apply set_eq. intros k0.
  rewrite /map_reverse_index !elem_of_dom.
  split.
  - intros [v0 Hlookup0].
    apply map_lookup_filter_Some in Hlookup0 as [Hlookup0 Hr0].
    destruct (decide (k0 = k)) as [->|Hneq].
    + rewrite lookup_insert_eq in Hlookup0. inversion Hlookup0; subst v0.
      exists v. apply map_lookup_filter_Some. split; [done|].
      exact (proj1 Hiff Hr0).
    + apply lookup_insert_Some in Hlookup0 as [[Heq _]|[_ Hlookup0]].
      * done.
      * exists v0. apply map_lookup_filter_Some. done.
  - intros [v0 Hlookup0].
    apply map_lookup_filter_Some in Hlookup0 as [Hlookup0 Hr0].
    destruct (decide (k0 = k)) as [->|Hneq].
    + rewrite Hlookup in Hlookup0. inversion Hlookup0; subst v0.
      exists v'. apply map_lookup_filter_Some. split.
      * rewrite lookup_insert_eq. done.
      * exact (proj2 Hiff Hr0).
    + exists v0. apply map_lookup_filter_Some. split; [|done].
      rewrite lookup_insert_ne; done.
Qed.

Local Lemma map_reverse_index_insert_new_singleton state k v r :
  state !! k = None →
  r ∈ extract_reference_set v →
  map_reverse_index (<[k := v]> state) r =
    map_reverse_index state r ∪ {[k]}.
Proof.
  intros Hlookup Hr.
  rewrite /map_reverse_index.
  replace (filter (λ '(_, v0), r ∈ extract_reference_set v0) (<[k:=v]> state))
    with (<[k:=v]> (filter (λ '(_, v0), r ∈ extract_reference_set v0) state)).
  2:{ symmetry. apply map_filter_insert_True. exact Hr. }
  rewrite dom_insert_L. Timeout 10 set_solver.
Qed.

Local Lemma map_reverse_index_insert_new_not state k v r :
  state !! k = None →
  r ∉ extract_reference_set v →
  map_reverse_index (<[k := v]> state) r = map_reverse_index state r.
Proof.
  intros Hlookup Hr.
  rewrite /map_reverse_index.
  apply f_equal.
  apply map_filter_insert_not'; [done|].
  intros y Hy. rewrite Hlookup in Hy. done.
Qed.

Local Lemma map_reverse_index_insert_add state k v v' r :
  state !! k = Some v →
  r ∉ extract_reference_set v →
  r ∈ extract_reference_set v' →
  map_reverse_index (<[k := v']> state) r =
    map_reverse_index state r ∪ {[k]}.
Proof.
  intros Hlookup Hnotin Hin.
  apply set_eq. intros k0.
  rewrite /map_reverse_index elem_of_union !elem_of_dom elem_of_singleton.
  split.
  - intros [v0 Hlookup0].
    apply map_lookup_filter_Some in Hlookup0 as [Hlookup0 Hr0].
    destruct (decide (k0 = k)) as [->|Hneq].
    + right. done.
    + left. exists v0. apply map_lookup_filter_Some. split; [|done].
      rewrite lookup_insert_ne in Hlookup0; done.
  - intros Hk0.
    destruct Hk0 as [[v0 Hlookup0]|Heq]; [|subst k0].
    + apply map_lookup_filter_Some in Hlookup0 as [Hlookup0 Hr0].
      exists v0. apply map_lookup_filter_Some. split; [|done].
      destruct (decide (k0 = k)) as [->|Hneq].
      * rewrite Hlookup in Hlookup0. inversion Hlookup0. subst v0.
        exfalso. apply Hnotin. done.
      * rewrite lookup_insert_ne; done.
    + exists v'. apply map_lookup_filter_Some. split; [|done].
      rewrite lookup_insert_eq. done.
Qed.

Local Lemma map_reverse_index_insert_remove state k v v' r :
  state !! k = Some v →
  r ∈ extract_reference_set v →
  extract_reference_set v' = extract_reference_set v ∖ {[r]} →
  map_reverse_index (<[k := v']> state) r =
    map_reverse_index state r ∖ {[k]}.
Proof.
  intros Hlookup Hr Hrefs.
  apply set_eq. intros k0.
  rewrite /map_reverse_index elem_of_difference !elem_of_dom elem_of_singleton.
  split.
  - intros [v0 Hlookup0].
    apply map_lookup_filter_Some in Hlookup0 as [Hlookup0 Hr0].
    destruct (decide (k0 = k)) as [->|Hneq].
    + rewrite lookup_insert_eq in Hlookup0. inversion Hlookup0. subst v0.
      rewrite Hrefs in Hr0. apply elem_of_difference in Hr0 as [_ Hnot].
      exfalso. apply Hnot. apply elem_of_singleton. done.
    + apply lookup_insert_Some in Hlookup0 as [[Heq _]|[_ Hlookup0]]; [done|].
      split; [|done].
      exists v0. apply map_lookup_filter_Some. done.
  - intros [[v0 Hlookup0] Hneq].
    apply map_lookup_filter_Some in Hlookup0 as [Hlookup0 Hr0].
    exists v0. apply map_lookup_filter_Some. split; [|done].
    rewrite lookup_insert_ne; done.
Qed.

Local Lemma map_reverse_index_delete_singleton state k v r :
  state !! k = Some v →
  extract_reference_set v = {[r]} →
  map_reverse_index (delete k state) r =
    map_reverse_index state r ∖ {[k]}.
Proof.
  intros Hlookup Hrefs.
  apply set_eq. intros k0.
  rewrite /map_reverse_index elem_of_difference !elem_of_dom elem_of_singleton.
  split.
  - intros [v0 Hlookup0].
    apply map_lookup_filter_Some in Hlookup0 as [Hlookup0 Hr0].
    apply lookup_delete_Some in Hlookup0 as [Hneq Hlookup0].
    split; [|done].
    exists v0. apply map_lookup_filter_Some. done.
  - intros [[v0 Hlookup0] Hneq].
    apply map_lookup_filter_Some in Hlookup0 as [Hlookup0 Hr0].
    exists v0. apply map_lookup_filter_Some. split; [|done].
    apply lookup_delete_Some. done.
Qed.

Local Lemma map_reverse_index_delete_not state k r :
  k ∉ map_reverse_index state r →
  map_reverse_index (delete k state) r = map_reverse_index state r.
Proof.
  intros Hnotin.
  apply set_eq. intros k0.
  rewrite /map_reverse_index !elem_of_dom.
  split.
  - intros [v0 Hlookup0].
    apply map_lookup_filter_Some in Hlookup0 as [Hlookup0 Hr0].
    apply lookup_delete_Some in Hlookup0 as [_ Hlookup0].
    exists v0. apply map_lookup_filter_Some. done.
  - intros [v0 Hlookup0].
    apply map_lookup_filter_Some in Hlookup0 as [Hlookup0 Hr0].
    destruct (decide (k0 = k)) as [->|Hneq].
    + exfalso. apply Hnotin.
      rewrite /map_reverse_index elem_of_dom.
      exists v0. apply map_lookup_filter_Some. done.
    + exists v0. apply map_lookup_filter_Some. split; [|done].
      apply lookup_delete_Some. done.
Qed.

Local Lemma map_reverse_index_delete_singleton_other state k v r r0 :
  state !! k = Some v →
  extract_reference_set v = {[r]} →
  r0 ≠ r →
  map_reverse_index (delete k state) r0 = map_reverse_index state r0.
Proof.
  intros Hlookup Hrefs Hneq.
  apply map_reverse_index_delete_not.
  intros Hk.
  rewrite /map_reverse_index elem_of_dom in Hk.
  destruct Hk as [v0 Hfilter].
  apply map_lookup_filter_Some in Hfilter as [Hlookup0 Hr0].
  rewrite Hlookup in Hlookup0. inversion Hlookup0. subst v0.
  rewrite Hrefs in Hr0. apply elem_of_singleton in Hr0. done.
Qed.

Lemma create_reference_vs {γ state used_reference r ks} k v cks:
  state !! k = None →
  extract_reference_set v = {[r]} →
  to_reference k v ≠ r →
  map_reverse_index state (to_reference k v) = cks →
  to_reference k v ∉ used_reference →
  own_auth γ state used_reference -∗
  own_frag γ r 1 ks ==∗
    own_auth γ (<[k := v]> state) (used_reference ∪ {[to_reference k v]}) ∗
    own_frag γ r 1 (ks ∪ {[k]}) ∗
    own_frag γ (to_reference k v) 1 cks.
Proof.
  iIntros (Hak Hrefs Hnself Hcks Hfresh) "Hauth Hfrag".
  iPoseProof (own_auth_frag_valid with "Hauth Hfrag") as "[%Hks %Hr_used]".
  unfold own_auth, own_frag.
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { eapply (@counted_reversed_reference.generic_reference_update_alloc_reference_from_old_obj
      K _ _ R _ _ V extract_reference_count to_reference)
      with (a := (state, used_reference))
           (a' := (<[k := v]> state, used_reference ∪ {[to_reference k v]}))
           (r := r)
           (ks := gset_to_gmap 1 ks)
           (ks' := gset_to_gmap 1 (ks ∪ {[k]}))
           (new_r := to_reference k v)
           (new_ks := gset_to_gmap 1 cks).
    - exact Hfresh.
    - intros Heq. apply Hnself. symmetry. exact Heq.
    - intros Hobj.
      rewrite map_Forall_lookup.
      intros k0 v0 Hlookup0.
      simpl in Hlookup0.
      destruct (decide (k0 = k)) as [->|Hneq].
      + apply lookup_insert_Some in Hlookup0 as [[_ Hv0]|[Hneq' _]].
        * symmetry in Hv0. subst v0. Timeout 10 set_solver.
        * exfalso. apply Hneq'. done.
      + apply lookup_insert_Some in Hlookup0 as [[Heq _]|[_ Hlookup_old]].
        * exfalso. apply Hneq. symmetry. done.
        * pose proof (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old) as Hused.
          Timeout 10 set_solver.
    - Timeout 10 set_solver.
    - Timeout 10 set_solver.
    - rewrite map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (<[k:=v]> state) r =
        map_reverse_index state r ∪ {[k]}).
      { apply map_reverse_index_insert_new_singleton; [done|].
        rewrite Hrefs. apply elem_of_singleton. done. }
      rewrite Hri. subst ks. done.
    - rewrite map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (<[k:=v]> state) (to_reference k v) =
        map_reverse_index state (to_reference k v)).
      { apply map_reverse_index_insert_new_not; [done|].
        rewrite Hrefs. intros Hin. apply elem_of_singleton in Hin. done. }
      rewrite Hri Hcks. done.
    - intros r0 Hneq Hr0. Timeout 10 set_solver.
    - intros r0 Hneq Hr0.
      rewrite !map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (<[k:=v]> state) r0 =
        map_reverse_index state r0).
      { apply map_reverse_index_insert_new_not; [done|].
        rewrite Hrefs. intros Hin. apply elem_of_singleton in Hin. done. }
      rewrite Hri. done.
  }
  iModIntro.
  iDestruct (own_op with "H") as "[H Hfrag_new]".
  iDestruct (own_op with "H") as "[Hauth Hfrag]".
  iFrame.
Qed.

Lemma set_reference_vs {γ state used_reference r ks} k v v':
  state !! k = Some v →
  r ∉ extract_reference_set v →
  extract_reference_set v' = extract_reference_set v ∪ {[r]} →
  to_reference k v = to_reference k v' →
  own_auth γ state used_reference -∗ own_frag γ r 1 ks ==∗
    own_auth γ (<[k := v']> state) used_reference ∗ own_frag γ r 1 (ks ∪ {[k]}).
Proof.
  iIntros (Hak Hnotin Hrefs Hg) "Hauth Hfrag".
  iPoseProof (own_auth_frag_valid with "Hauth Hfrag") as "[%Hks %Hr_used]".
  unfold own_auth, own_frag.
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { eapply (@counted_reversed_reference.generic_reference_update_from_old_obj
      K _ _ R _ _ V extract_reference_count to_reference)
      with (a := (state, used_reference))
           (a' := (<[k := v']> state, used_reference))
           (r := r)
           (ks := gset_to_gmap 1 ks)
           (ks' := gset_to_gmap 1 (ks ∪ {[k]})).
    - intros Hobj.
      rewrite map_Forall_lookup.
      intros k0 v0 Hlookup0.
      simpl in Hlookup0.
      destruct (decide (k0 = k)) as [->|Hneq].
      + apply lookup_insert_Some in Hlookup0 as [[_ Hv0]|[Hneq' _]].
        * symmetry in Hv0. subst v0. rewrite <- Hg.
          exact (map_Forall_lookup_1 _ _ _ _ Hobj Hak).
        * exfalso. apply Hneq'. done.
      + apply lookup_insert_Some in Hlookup0 as [[Heq _]|[_ Hlookup_old]].
        * exfalso. apply Hneq. symmetry. done.
        * exact (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old).
    - exact Hr_used.
    - rewrite map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (<[k:=v']> state) r =
        map_reverse_index state r ∪ {[k]}).
      { apply (map_reverse_index_insert_add state k v v' r); [done|done|].
        rewrite Hrefs. Timeout 10 set_solver. }
      rewrite Hri. subst ks. done.
    - done.
    - intros r0 Hneq Hr0.
      rewrite !map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (<[k:=v']> state) r0 =
        map_reverse_index state r0).
      { apply (dom_filter_insert_preserve state k v v' r0); [done|].
        rewrite Hrefs. split; intros Hin.
        - apply elem_of_union in Hin as [Hin|Hin]; [done|].
          apply elem_of_singleton in Hin. subst. done.
        - apply elem_of_union. left. done. }
      rewrite Hri. done.
  }
  iModIntro. iDestruct (own_op with "H") as "[Hauth Hfrag]". iFrame.
Qed.

Lemma unset_reference_vs {γ state used_reference r ks} k v v':
  state !! k = Some v →
  r ∈ extract_reference_set v →
  extract_reference_set v' = extract_reference_set v ∖ {[r]} →
  to_reference k v = to_reference k v' →
  own_auth γ state used_reference -∗ own_frag γ r 1 ks ==∗
    own_auth γ (<[k := v']> state) used_reference ∗ own_frag γ r 1 (ks ∖ {[k]}).
Proof.
  iIntros (Hak Hin Hrefs Hg) "Hauth Hfrag".
  iPoseProof (own_auth_frag_valid with "Hauth Hfrag") as "[%Hks %Hr_used]".
  unfold own_auth, own_frag.
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { eapply (@counted_reversed_reference.generic_reference_update_from_old_obj
      K _ _ R _ _ V extract_reference_count to_reference)
      with (a := (state, used_reference))
           (a' := (<[k := v']> state, used_reference))
           (r := r)
           (ks := gset_to_gmap 1 ks)
           (ks' := gset_to_gmap 1 (ks ∖ {[k]})).
    - intros Hobj.
      rewrite map_Forall_lookup.
      intros k0 v0 Hlookup0.
      simpl in Hlookup0.
      destruct (decide (k0 = k)) as [->|Hneq].
      + apply lookup_insert_Some in Hlookup0 as [[_ Hv0]|[Hneq' _]].
        * symmetry in Hv0. subst v0. rewrite <- Hg.
          exact (map_Forall_lookup_1 _ _ _ _ Hobj Hak).
        * exfalso. apply Hneq'. done.
      + apply lookup_insert_Some in Hlookup0 as [[Heq _]|[_ Hlookup_old]].
        * exfalso. apply Hneq. symmetry. done.
        * exact (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old).
    - exact Hr_used.
    - rewrite map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (<[k:=v']> state) r =
        map_reverse_index state r ∖ {[k]}).
      { apply (map_reverse_index_insert_remove state k v v' r); done. }
      rewrite Hri. subst ks. done.
    - done.
    - intros r0 Hneq Hr0.
      rewrite !map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (<[k:=v']> state) r0 =
        map_reverse_index state r0).
      { apply (dom_filter_insert_preserve state k v v' r0); [done|].
        rewrite Hrefs. split; intros Hin0.
        - apply elem_of_difference in Hin0 as [Hin0 _]. done.
        - apply elem_of_difference. split; [done|].
          intros Heq. apply elem_of_singleton in Heq. subst. done. }
      rewrite Hri. done.
  }
  iModIntro. iDestruct (own_op with "H") as "[Hauth Hfrag]". iFrame.
Qed.

Lemma delete_reference_vs {γ state used_reference r ks} k v:
  state !! k = Some v →
  extract_reference_set v = {[r]} →
  own_auth γ state used_reference -∗ own_frag γ r 1 ks ==∗
    own_auth γ (delete k state) used_reference ∗ own_frag γ r 1 (ks ∖ {[k]}).
Proof.
  iIntros (Hak Hrefs) "Hauth Hfrag".
  iPoseProof (own_auth_frag_valid with "Hauth Hfrag") as "[%Hks %Hr_used]".
  unfold own_auth, own_frag.
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { eapply (@counted_reversed_reference.generic_reference_update_from_old_obj
      K _ _ R _ _ V extract_reference_count to_reference)
      with (a := (state, used_reference))
           (a' := (delete k state, used_reference))
           (r := r)
           (ks := gset_to_gmap 1 ks)
           (ks' := gset_to_gmap 1 (ks ∖ {[k]})).
    - intros Hobj.
      rewrite map_Forall_lookup.
      intros k0 v0 Hlookup0.
      simpl in Hlookup0.
      apply lookup_delete_Some in Hlookup0 as [_ Hlookup0].
      exact (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup0).
    - exact Hr_used.
    - rewrite map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (delete k state) r =
        map_reverse_index state r ∖ {[k]}).
      { apply (map_reverse_index_delete_singleton state k v r); done. }
      rewrite Hri. subst ks. done.
    - done.
    - intros r0 Hneq Hr0.
      rewrite !map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (delete k state) r0 =
        map_reverse_index state r0).
      { apply (map_reverse_index_delete_singleton_other state k v r r0); done. }
      rewrite Hri. done.
  }
  iModIntro. iDestruct (own_op with "H") as "[Hauth Hfrag]". iFrame.
Qed.

Lemma delete_reference_vs2 {γ state used_reference r ks} k:
  k ∈ ks →
  (∀ v, r ∈ extract_reference_set v → extract_reference_set v = {[r]}) →
  own_auth γ state used_reference -∗ own_frag γ r 1 ks ==∗
    own_auth γ (delete k state) used_reference ∗ own_frag γ r 1 (ks ∖ {[k]}).
Proof.
  iIntros (Hk Hsingleton) "Hauth Hfrag".
  iPoseProof (own_auth_frag_valid with "Hauth Hfrag") as "[%Hks %Hr_used]".
  assert (∃ v, state !! k = Some v ∧ r ∈ extract_reference_set v) as (v & Hak & Hr).
  { rewrite Hks /map_reverse_index elem_of_dom in Hk.
    destruct Hk as [v Hfilter].
    apply map_lookup_filter_Some in Hfilter as [Hak Hr].
    eauto.
  }
  iApply (delete_reference_vs k v with "Hauth Hfrag"); [done|].
  apply Hsingleton. done.
Qed.

Lemma simple_update_vs {γ state used_reference} k v v':
  state !! k = Some v →
  extract_reference_set v = extract_reference_set v' →
  to_reference k v = to_reference k v' →
  own_auth γ state used_reference ==∗ own_auth γ (<[k := v']> state) used_reference.
Proof.
  iIntros (Hak Hrefs Hg) "Hauth".
  unfold own_auth.
  iMod (own_update with "Hauth") as "Hauth".
  { eapply (@counted_reversed_reference.generic_update_from_old_obj
      K _ _ R _ _ V extract_reference_count to_reference)
      with (a := (state, used_reference))
           (a' := (<[k := v']> state, used_reference)).
    - intros Hobj.
      rewrite map_Forall_lookup.
      intros k0 v0 Hlookup0.
      simpl in Hlookup0.
      destruct (decide (k0 = k)) as [->|Hneq].
      + apply lookup_insert_Some in Hlookup0 as [[_ Hv0]|[Hneq' _]].
        * symmetry in Hv0. subst v0. rewrite <- Hg.
          exact (map_Forall_lookup_1 _ _ _ _ Hobj Hak).
        * exfalso. apply Hneq'. done.
      + apply lookup_insert_Some in Hlookup0 as [[Heq _]|[_ Hlookup_old]].
        * exfalso. apply Hneq. symmetry. done.
        * exact (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old).
    - done.
    - intros r0 Hr0.
      rewrite !map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (<[k:=v']> state) r0 =
        map_reverse_index state r0).
      { apply (dom_filter_insert_preserve state k v v' r0); [done|].
        rewrite Hrefs. done. }
      rewrite Hri. done.
  }
  iModIntro. iExact "Hauth".
Qed.

Lemma simple_create_vs {γ state used_reference} k v cks:
  state !! k = None →
  extract_reference_set v = ∅ →
  map_reverse_index state (to_reference k v) = cks →
  to_reference k v ∉ used_reference →
  own_auth γ state used_reference ==∗
    own_auth γ (<[k := v]> state) (used_reference ∪ {[to_reference k v]}) ∗
    own_frag γ (to_reference k v) 1 cks.
Proof.
  iIntros (Hak Hrefs Hcks Hfresh) "Hauth".
  unfold own_auth, own_frag.
  iMod (own_update with "Hauth") as "H".
  { eapply (@counted_reversed_reference.generic_alloc_reference_from_old_obj
      K _ _ R _ _ V extract_reference_count to_reference)
      with (a := (state, used_reference))
           (a' := (<[k := v]> state, used_reference ∪ {[to_reference k v]}))
           (r := to_reference k v)
           (ks := gset_to_gmap 1 cks).
    - exact Hfresh.
    - intros Hobj.
      rewrite map_Forall_lookup.
      intros k0 v0 Hlookup0.
      simpl in Hlookup0.
      destruct (decide (k0 = k)) as [->|Hneq].
      + apply lookup_insert_Some in Hlookup0 as [[_ Hv0]|[Hneq' _]].
        * symmetry in Hv0. subst v0. Timeout 10 set_solver.
        * exfalso. apply Hneq'. done.
      + apply lookup_insert_Some in Hlookup0 as [[Heq _]|[_ Hlookup_old]].
        * exfalso. apply Hneq. symmetry. done.
        * pose proof (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old) as Hused.
          Timeout 10 set_solver.
    - Timeout 10 set_solver.
    - rewrite map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (<[k:=v]> state) (to_reference k v) =
        map_reverse_index state (to_reference k v)).
      { apply map_reverse_index_insert_new_not; [done|].
        rewrite Hrefs. Timeout 10 set_solver. }
      rewrite Hri Hcks. done.
    - intros r0 Hr0. Timeout 10 set_solver.
    - intros r0 Hr0.
      rewrite !map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (<[k:=v]> state) r0 =
        map_reverse_index state r0).
      { apply map_reverse_index_insert_new_not; [done|].
        rewrite Hrefs. Timeout 10 set_solver. }
      rewrite Hri. done.
  }
  iModIntro.
  iDestruct (own_op with "H") as "[Hauth Hfrag]".
  iFrame.
Qed.

Lemma simple_delete_vs {γ state used_reference} k v:
  state !! k = Some v →
  extract_reference_set v = ∅ →
  own_auth γ state used_reference ==∗ own_auth γ (delete k state) used_reference.
Proof.
  iIntros (Hak Hrefs) "Hauth".
  unfold own_auth.
  iMod (own_update with "Hauth") as "Hauth".
  { eapply (@counted_reversed_reference.generic_update_from_old_obj
      K _ _ R _ _ V extract_reference_count to_reference)
      with (a := (state, used_reference))
           (a' := (delete k state, used_reference)).
    - intros Hobj.
      rewrite map_Forall_lookup.
      intros k0 v0 Hlookup0.
      simpl in Hlookup0.
      apply lookup_delete_Some in Hlookup0 as [_ Hlookup0].
      exact (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup0).
    - done.
    - intros r0 Hr0.
      rewrite !map_raw_reverse_index_eq.
      assert (Hri :
        map_reverse_index (delete k state) r0 =
        map_reverse_index state r0).
      { apply map_reverse_index_delete_not.
        intros Hk.
        rewrite /map_reverse_index elem_of_dom in Hk.
        destruct Hk as [v0 Hfilter].
        apply map_lookup_filter_Some in Hfilter as [Hlookup Hr].
        rewrite Hak in Hlookup. inversion Hlookup. subst v0.
        rewrite Hrefs in Hr. Timeout 10 set_solver. }
      rewrite Hri. done.
  }
  iModIntro. iExact "Hauth".
Qed.

End reversed_reference.
