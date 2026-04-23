From New.proof Require Import prelude empty_ffi.
From New.proof Require Export pure_objects.

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
  - eapply Permutation_trans; done.
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

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma filter_preserves_key_uniqueness {A} (key : A → KKey.t) (P : A → Prop) `{∀ x, Decision (P x)} (xs : list A) :
  (∀ i j x y, i ≠ j → xs !! i = Some x → xs !! j = Some y → key x ≠ key y) →
  (∀ i j x y, i ≠ j → filter P xs !! i = Some x → filter P xs !! j = Some y → key x ≠ key y).
Proof.
  intros Hno_dup i j x y Hneq Hi Hj Hkeys_eq.
  assert (x = y) as Heq.
  { apply list_elem_of_lookup_2 in Hi as Hi'. apply list_elem_of_filter in Hi' as [_ Hi_in].
    apply list_elem_of_lookup_2 in Hj as Hj'. apply list_elem_of_filter in Hj' as [_ Hj_in].
    apply list_elem_of_lookup_1 in Hi_in as [i_orig Hi_orig].
    apply list_elem_of_lookup_1 in Hj_in as [j_orig Hj_orig].
    destruct (decide (i_orig = j_orig)) as [|].
    - subst j_orig. congruence.
    - exfalso. apply (Hno_dup i_orig j_orig x y); done. }
  subst y.
  assert (NoDup xs) as HNoDup.
  { apply NoDup_alt. intros i' j' x' Hi' Hj'.
    destruct (decide (i' = j')) as [|]; [done|].
    exfalso. apply (Hno_dup i' j' x' x'); done. }
  assert (NoDup (filter P xs)) as HNoDup_filtered.
  { apply list.NoDup_filter. done. }
  assert (i = j) by (eapply NoDup_lookup; eauto).
  done.
Qed.

Lemma list_map_size_eq {K V} `{FinMap K M} (key_fn : V → K) (xs : list V) (m : M V) :
  (* Every element in xs appears in m with the right key *)
  (∀ x, x ∈ xs → m !! key_fn x = Some x) →
  (* Every element in m appears in xs (surjectivity) *)
  (∀ k v, m !! k = Some v → v ∈ xs) →
  (* Keys are canonical: if m maps k to v, then k = key_fn v *)
  (∀ k v, m !! k = Some v → k = key_fn v) →
  (* xs has no duplicate keys *)
  (∀ i j x y, i ≠ j → xs !! i = Some x → xs !! j = Some y → key_fn x ≠ key_fn y) →
  (* Then xs and m have the same length/size *)
  length xs = size m.
Proof.
  intros Hlist_in_map Hmap_in_list Hkey_canonical Hno_dup.
  assert ((map_to_list m).*2 ≡ₚ xs) as Hperm.
  { apply NoDup_Permutation.
    - apply NoDup_fmap_2_strong.
      + intros [k1 v1] [k2 v2] Hin1 Hin2. simpl. intros <-.
        apply elem_of_map_to_list in Hin1, Hin2.
        assert (k1 = key_fn v1) as -> by (apply Hkey_canonical; done).
        assert (k2 = key_fn v1) as -> by (apply Hkey_canonical; done).
        done.
      + apply NoDup_map_to_list.
    - apply NoDup_alt. intros i j x Hi Hj.
      destruct (decide (i = j)); [done|exfalso; eapply Hno_dup; eauto].
    - intros v. split.
      + intros Hv. apply list_elem_of_fmap_1 in Hv as [[k v'] [Heq Hkv]].
        simpl in Heq. subst v'.
        by apply elem_of_map_to_list, Hmap_in_list in Hkv.
      + intros Hv_in. apply Hlist_in_map in Hv_in as Hlookup.
        change v with ((key_fn v, v).2).
        apply (list_elem_of_fmap_2 snd).
        apply elem_of_map_to_list. done. }
  rewrite <- (Permutation_length Hperm).
  rewrite length_fmap.
  apply length_map_to_list.
Qed.

Lemma filter_list_map_size_eq {K V} `{FinMap K M} (key_fn : V → K) (P : V → Prop) `{∀ v, Decision (P v)} (xs : list V) (m : M V) :
  (* Every element in xs appears in m with the right key *)
  (∀ x, x ∈ xs → m !! key_fn x = Some x) →
  (* Every element in m appears in xs (surjectivity) *)
  (∀ k v, m !! k = Some v → v ∈ xs) →
  (* Keys are canonical: if m maps k to v, then k = key_fn v *)
  (∀ k v, m !! k = Some v → k = key_fn v) →
  (* xs has no duplicate keys *)
  (∀ i j x y, i ≠ j → xs !! i = Some x → xs !! j = Some y → key_fn x ≠ key_fn y) →
  (* Then filtering by compatible predicates yields same size *)
  length (filter P xs) = size (filter (λ kv, P kv.2) m).
Proof.
  intros Hin Hmap_in_list Hkey_eq Hno_dup.
  assert (length xs = size m) as Hlen_size_eq.
  { apply (list_map_size_eq key_fn). all: done. }
  rewrite map_filter_alt.
  assert (NoDup (filter (λ kv, P kv.2) (map_to_list m)).*1) as HNoDup_filtered.
  { cut (∀ l : list (K * V), NoDup l.*1 → NoDup (filter (λ kv, P kv.2) l).*1).
    { intro Hcut. apply Hcut. apply NoDup_fst_map_to_list. }
    clear. intros l. induction l as [|[k v] rest IH]; intro HNoDup; simpl.
    - done.
    - rewrite filter_cons. case_decide; simpl.
      + constructor.
        * intros Hin_k. apply NoDup_cons_1_1 in HNoDup.
          assert (k ∈ rest.*1) by
            (clear -Hin_k; induction rest as [|[k' v'] rest' IH']; [inversion Hin_k|];
             rewrite filter_cons in Hin_k; case_decide; simpl in Hin_k;
             [apply elem_of_cons in Hin_k as [->|Hin_k]; [left|right; apply IH']; done
             |right; apply IH'; done]).
          done.
        * apply IH. by apply NoDup_cons_1_2 in HNoDup.
      + apply IH. by apply NoDup_cons_1_2 in HNoDup. }
  rewrite (map_size_list_to_map _ HNoDup_filtered).
  assert ((filter (λ kv, P kv.2) (map_to_list m)).*2 ≡ₚ filter P xs) as Hperm.
  { apply NoDup_Permutation.
    - apply NoDup_fmap_2_strong.
      + intros [k1 v1] [k2 v2] Hin1 Hin2. simpl. intros <-.
        apply list_elem_of_filter in Hin1 as [_ Hin1].
        apply list_elem_of_filter in Hin2 as [_ Hin2].
        apply elem_of_map_to_list in Hin1, Hin2.
        assert (k1 = key_fn v1) as -> by (apply Hkey_eq; done).
        assert (k2 = key_fn v1) as -> by (apply Hkey_eq; done).
        done.
      + apply list.NoDup_filter, NoDup_map_to_list.
    - apply list.NoDup_filter, NoDup_alt. intros i j x Hi Hj.
      destruct (decide (i = j)); [done|exfalso; eapply Hno_dup; eauto].
    - intros v. split.
      + intros Hv. apply list_elem_of_fmap_1 in Hv as [kv [Heq Hkv]].
        destruct kv as [k v']. simpl in Heq. subst v'.
        apply list_elem_of_filter in Hkv as [HPkv Hkv].
        apply list_elem_of_filter. split; [done|].
        by apply elem_of_map_to_list, Hmap_in_list in Hkv.
      + intros Hv. apply list_elem_of_filter in Hv as [HPv Hv_in].
        apply Hin in Hv_in as Hlookup.
        change v with ((key_fn v, v).2).
        apply (list_elem_of_fmap_2 snd).
        apply list_elem_of_filter. split; [simpl; done|].
        apply elem_of_map_to_list. done. }
  rewrite -(Permutation_length Hperm).
  apply length_fmap.
Qed.

End proof.
