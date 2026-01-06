From New.proof Require Import prelude empty_ffi.
From New.proof Require Export pure_objects.

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

Lemma filter_list_map_size_eq {K V} `{FinMap K M} (key_fn : V → K) (P : V → Prop) `{∀ v, Decision (P v)} (xs : list V) (m : M V) :
  (* Every element in xs appears in m with the right key *)
  (∀ x, x ∈ xs → m !! key_fn x = Some x) →
  (* Every element in m appears in xs (surjectivity) *)
  (∀ k v, m !! k = Some v → v ∈ xs) →
  (* Keys are canonical: if m maps k to v, then k = key_fn v *)
  (∀ k v, m !! k = Some v → k = key_fn v) →
  (* xs has no duplicate keys *)
  (∀ i j x y, i ≠ j → xs !! i = Some x → xs !! j = Some y → key_fn x ≠ key_fn y) →
  (* Same size before filtering *)
  length xs = size m →
  (* Then filtering by compatible predicates yields same size *)
  length (filter P xs) = size (filter (λ kv, P kv.2) m).
Proof.
  intros Hin Hmap_in_list Hkey_eq Hno_dup Hlen_size_eq.
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
