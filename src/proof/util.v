From New.proof Require Import prelude empty_ffi.

Lemma prod_map_id_fmap_values {K A B} (f : A → B) (l : list (K * A)) :
  (prod_map id f <$> l).*2 = f <$> l.*2.
Proof.
  induction l as [|[k x] l IH]; simpl; [done|].
  f_equal.
  exact IH.
Qed.

Lemma pair_fmap_keys {A B C} (f : A → B) (g : A → C) (l : list A) :
  (map (λ x, (f x, g x)) l).*1 = map f l.
Proof.
  induction l as [|x l IH]; simpl; [done|].
  f_equal.
  exact IH.
Qed.

Lemma pair_fmap_values {A B C} (f : A → B) (g : A → C) (l : list A) :
  (map (λ x, (f x, g x)) l).*2 = map g l.
Proof.
  induction l as [|x l IH]; simpl; [done|].
  f_equal.
  exact IH.
Qed.

Lemma fmap_pair_values {A B C} (f : B → C) (l : list (A * B)) :
  map (λ kv, f kv.2) l = f <$> l.*2.
Proof.
  induction l as [|[x y] l IH]; simpl; [done|].
  f_equal.
  exact IH.
Qed.

Lemma snd_fmap_eq_values {A B} (l : list (A * B)) :
  snd <$> l = l.*2.
Proof.
  change (snd <$> l) with (map (λ kv, id kv.2) l).
  rewrite fmap_pair_values.
  rewrite list_fmap_id.
  done.
Qed.

Lemma snd_fmap_map_to_list_fmap {K A B} `{Countable K} (f : A → B) (m : gmap K A) :
  snd <$> map_to_list (f <$> m) = f <$> (map_to_list m).*2.
Proof.
  rewrite map_to_list_fmap.
  change (snd <$> (prod_map id f <$> map_to_list m))
    with ((prod_map id f <$> map_to_list m).*2).
  rewrite prod_map_id_fmap_values.
  done.
Qed.

Lemma perm_filter {A} (P : A → Prop) `{!∀ x, Decision (P x)} l1 l2 :
  l1 ≡ₚ l2 →
  filter P l1 ≡ₚ filter P l2.
Proof.
  intros Hperm.
  induction Hperm.
  - done.
  - rewrite !filter_cons.
    destruct (decide (P x)); simpl.
    + apply perm_skip. exact IHHperm.
    + exact IHHperm.
  - rewrite !filter_cons.
    destruct (decide (P y)); destruct (decide (P x)); simpl; try done.
    apply perm_swap.
  - eapply Permutation_trans with (l' := filter P l'); done.
Qed.

Lemma big_sepL_permutation {PROP : bi} {A}
    (P : A → PROP) xs ys :
  xs ≡ₚ ys →
  ([∗ list] x ∈ xs, P x) ⊣⊢ ([∗ list] x ∈ ys, P x).
Proof.
  intros Hperm.
  induction Hperm; simpl.
  - done.
  - by rewrite IHHperm.
  - rewrite !(assoc bi_sep).
    by rewrite (comm bi_sep (P x) (P y)).
  - by rewrite IHHperm1 IHHperm2.
Qed.

Lemma filter_fmap_comm {A B} (f : A → B)
    (P : A → Prop) (Q : B → Prop)
    `{!∀ x, Decision (P x)} `{!∀ y, Decision (Q y)} (xs : list A) :
  (∀ x, P x ↔ Q (f x)) →
  filter Q (f <$> xs) = f <$> filter P xs.
Proof.
  intros HPQ.
  induction xs as [|x xs IH]; simpl; first done.
  rewrite !filter_cons.
  destruct (decide (P x)) as [HP|HP];
    destruct (decide (Q (f x))) as [HQ|HQ]; simpl.
  - by rewrite IH.
  - exfalso. apply HQ. by apply HPQ.
  - exfalso. apply HP. by apply HPQ.
  - exact IH.
Qed.

Lemma Forall_filter {A} (P Q : A → Prop) `{!∀ x, Decision (Q x)} xs :
  Forall P xs →
  Forall P (filter Q xs).
Proof.
  intros Hxs.
  induction Hxs as [|x xs HP Hxs IH]; simpl; [done|].
  rewrite filter_cons.
    destruct (decide (Q x)); simpl; [constructor; done|done].
Qed.

Lemma Forall_reverse {A} (P : A → Prop) (xs : list A) :
  Forall P xs →
  Forall P (reverse xs).
Proof.
  rewrite !Forall_forall.
  intros Hforall x Hin.
  apply Hforall.
  rewrite -list_elem_of_In in Hin.
  rewrite elem_of_reverse in Hin.
  by rewrite -list_elem_of_In.
Qed.

Lemma filter_all {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) :
  (∀ x, x ∈ l → P x) →
  filter P l = l.
Proof.
  intros Hall.
  induction l as [|x l IH]; simpl; first done.
  assert (P x) as HPx.
  { apply Hall. left. }
  rewrite (filter_cons_True P x l HPx).
  f_equal. apply IH. intros y Hy. apply Hall. right. exact Hy.
Qed.

Lemma filter_length_le' {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (xs : list A) :
  length (filter P xs) ≤ length xs.
Proof.
  induction xs as [|x xs IH]; simpl; first lia.
  rewrite filter_cons.
  destruct (decide (P x)); simpl; lia.
Qed.

Lemma filter_length_eq_Forall {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (xs : list A) :
  length (filter P xs) = length xs →
  Forall P xs.
Proof.
  induction xs as [|x xs IH]; simpl; intros Hlen; first constructor.
  rewrite filter_cons in Hlen.
  destruct (decide (P x)) as [HP|HnotP]; simpl in Hlen.
  - constructor; [exact HP|]. apply IH. lia.
  - pose proof (filter_length_le' P xs). lia.
Qed.

Lemma filter_length_zero_not_elem {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (xs : list A) x :
  length (filter P xs) = 0%nat →
  x ∈ xs →
  ¬ P x.
Proof.
  intros Hlen Hin HP.
  assert (x ∈ filter P xs) as Hin_filter.
  { apply list_elem_of_filter. split; done. }
  destruct (filter P xs) eqn:Hfilter.
  - inversion Hin_filter.
  - simpl in Hlen. lia.
Qed.

Lemma NoDup_fmap_filter {A B} (f : A → B) (P : A → Prop)
    `{∀ x, Decision (P x)} (xs : list A) :
  NoDup (f <$> xs) →
  NoDup (f <$> filter P xs).
Proof.
  induction xs as [|x xs IH]; intros Hnodup; [done|].
  rewrite (filter_cons P x xs).
  inversion Hnodup as [|? ? Hnotin Hnodup_tail]; subst.
  destruct (decide (P x)) as [_|_].
  - simpl. constructor.
    + intros Hin.
      apply Hnotin.
      apply list_elem_of_fmap_1 in Hin as (y & Hkey_eq & Hy_filter).
      apply list_elem_of_filter in Hy_filter as [_ Hy].
      rewrite Hkey_eq.
      apply list_elem_of_fmap_2. exact Hy.
    + by apply IH.
  - by apply IH.
Qed.

Lemma filter_none {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) :
  (∀ x, x ∈ l → ¬ P x) →
  filter P l = [].
Proof.
  intros Hnone.
  induction l as [|x l IH]; simpl; first done.
  assert (¬ P x) as HPx.
  { apply Hnone. left. }
  rewrite (filter_cons_False P x l HPx).
  apply IH. intros y Hy. apply Hnone. right. exact Hy.
Qed.

Lemma filter_partition_perm {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) :
  filter P l ++ filter (λ x, not (P x)) l ≡ₚ l.
Proof.
  induction l as [|x l IH]; first done.
  destruct (decide (P x)) as [HPx|HnotPx].
  - rewrite (filter_cons_True P x l HPx).
    rewrite (filter_cons_False (λ x, not (P x)) x l (λ Hcontra, Hcontra HPx)).
    apply perm_skip. exact IH.
  - rewrite (filter_cons_False P x l HnotPx).
    rewrite (filter_cons_True (λ x, not (P x)) x l HnotPx).
    etrans.
    + symmetry. apply Permutation_middle.
    + apply perm_skip. exact IH.
Qed.

Lemma lookup_filter_ge {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (l : list A) (n : nat) x :
  filter P l !! n = Some x →
  ∃ k : nat, n ≤ k ∧ l !! k = Some x.
Proof.
  revert n.
  induction l as [|y l IH]; intros n Hlookup.
  - destruct n; inversion Hlookup.
  - rewrite filter_cons in Hlookup.
    destruct (decide (P y)) as [Hy|Hy].
    + destruct n as [|n].
      * simpl in Hlookup. inversion Hlookup; subst.
        exists O. split; done.
      * simpl in Hlookup.
        destruct (IH n Hlookup) as (k & Hle & Hk).
        exists (S k). split; [lia|done].
    + destruct (IH n Hlookup) as (k & Hle & Hk).
      exists (S k). split; [lia|done].
Qed.

Lemma lookup_filter_elem_of_drop {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (l : list A) (n : nat) x :
  filter P l !! n = Some x →
  x ∈ drop n l.
Proof.
  intros Hlookup.
  destruct (lookup_filter_ge P l n x Hlookup) as (k & Hle & Hk).
  apply (list_elem_of_lookup_2 (drop n l) (k - n) x).
  rewrite lookup_drop.
  replace (n + (k - n))%nat with k by lia.
  done.
Qed.

Lemma take_drop_middle_slices {A} (l : list A) i x :
  l !! i = Some x →
  take i l = take i (take i l ++ x :: drop (S i) l) ∧
  drop (S i) (take i l ++ x :: drop (S i) l) = drop (S i) l.
Proof.
  intros Hlookup.
  pose proof (lookup_lt_Some _ _ _ Hlookup) as Hlt.
  split.
  - assert ((i <= length (take i l))%nat) as Hlen_take by (rewrite length_take_le; lia).
    rewrite (take_app_le (take i l) (x :: drop (S i) l) i Hlen_take).
    rewrite take_take Nat.min_id. done.
  - replace (S i) with (length (take i l) + 1)%nat by (rewrite length_take_le; lia).
    rewrite drop_app_add. done.
Qed.

Section big_sepL_helpers.
Context {Σ : gFunctors}.

Lemma big_sepL_filter_partition {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (Φ : A → iProp Σ) (l : list A) :
  ([∗ list] x ∈ l, Φ x) -∗
  ([∗ list] x ∈ filter P l, Φ x) ∗
  ([∗ list] x ∈ filter (λ x, not (P x)) l, Φ x).
Proof.
  iIntros "Hl".
  iInduction l as [|x l] "IH".
  - rewrite !big_sepL_nil. iSplit; done.
  - rewrite big_sepL_cons. iDestruct "Hl" as "[Hx Hl]".
    iDestruct ("IH" with "Hl") as "[HP HnotP]".
    destruct (decide (P x)) as [HPx|HnotPx].
    + rewrite (filter_cons_True P x l HPx).
      rewrite (filter_cons_False (λ x, not (P x)) x l (λ Hcontra, Hcontra HPx)).
      rewrite big_sepL_cons. iFrame.
    + rewrite (filter_cons_False P x l HnotPx).
      rewrite (filter_cons_True (λ x, not (P x)) x l HnotPx).
      rewrite big_sepL_cons. iFrame.
Qed.

Lemma big_sepL_split_lookup {A} (Φ : A → iProp Σ) (l : list A) i x :
  l !! i = Some x →
  ([∗ list] y ∈ l, Φ y) -∗
  ([∗ list] y ∈ take i l, Φ y) ∗ Φ x ∗ ([∗ list] y ∈ drop (S i) l, Φ y).
Proof.
  iIntros (Hlookup) "H".
  destruct (take_drop_middle_slices l i x Hlookup) as [Htake Hdrop].
  rewrite -(take_drop_middle l i x Hlookup) big_sepL_app /=.
  iDestruct "H" as "(Hbefore & Hx & Hafter)".
  iEval (rewrite Htake) in "Hbefore".
  iEval (rewrite -Hdrop) in "Hafter".
  iFrame.
Qed.

End big_sepL_helpers.

Lemma map_to_list_filter_perm {K A} `{Countable K} (m : gmap K A) (P : K * A → Prop) `{!∀ x, Decision (P x)} :
  map_to_list (filter P m) ≡ₚ filter P (map_to_list m).
Proof.
  rewrite map_filter_alt.
  apply map_to_list_to_map.
  apply NoDup_fmap_2_strong.
  - intros [k1 v1] [k2 v2] Hin1 Hin2 Hk_eq. simpl in Hk_eq.
    apply list_elem_of_filter in Hin1 as [_ Hin1].
    apply list_elem_of_filter in Hin2 as [_ Hin2].
    apply elem_of_map_to_list in Hin1, Hin2.
    subst k2.
    rewrite Hin1 in Hin2.
    inversion Hin2.
    reflexivity.
  - apply list.NoDup_filter.
    apply NoDup_map_to_list.
Qed.

Lemma filter_map_to_list_values {K A} (P : A → Prop) `{!∀ x, Decision (P x)} (l : list (K * A)) :
  (filter (λ '(_, x), P x) l).*2 = filter P l.*2.
Proof.
  induction l as [|[k x] l IH]; simpl; [done|].
  rewrite !filter_cons.
  destruct (decide (P x)); simpl.
  - f_equal. exact IH.
  - exact IH.
Qed.

Lemma filter_map_to_list_values_perm {K A} `{Countable K} (m : gmap K A) (P : A → Prop) `{!∀ x, Decision (P x)} :
  filter P (map_to_list m).*2 ≡ₚ (map_to_list (filter (λ '(_, x), P x) m)).*2.
Proof.
  rewrite <- filter_map_to_list_values.
  apply Permutation_sym.
  change ((map_to_list (filter (λ '(_, x), P x) m)).*2 ≡ₚ (filter (λ '(_, x), P x) (map_to_list m)).*2).
  apply Permutation_map.
  apply map_to_list_filter_perm.
Qed.
