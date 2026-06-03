From New.proof Require Import prelude empty_ffi.
From New.golang.theory Require Export map.
From iris.algebra Require Import gmap.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}.
Local Set Default Proof Using "All".

Definition for_map_postcondition_no_break (P : iProp Σ) (bv : val) : iProp Σ :=
  (⌜ bv = continue_val ⌝ ∗ P) ∨
  (⌜ bv = execute_val ⌝ ∗ P).

Definition for_map_postcondition_return (P : iProp Σ) (R : val → iProp Σ)
    (bv : val) : iProp Σ :=
  (⌜ bv = continue_val ⌝ ∗ P) ∨
  (⌜ bv = execute_val ⌝ ∗ P) ∨
  (∃ v, ⌜ bv = return_val v ⌝ ∗ R bv).

Lemma wp_map_for_range_return
    `{!ZeroVal K} `{!EqDecision K} `{!Countable K} `{!ZeroVal V}
    `{!go.IntoValInj K} `{!TypedPointsto K} `{!IntoValTyped K key_type}
    (P : list K → Z → iProp Σ) stk E (body : func.t) elem_type mref
    (m : gmap K V) dq :
  ∀ Φ,
  mref ↦${dq} m -∗
  (∀ keys,
     ⌜ list_to_set keys = dom m ∧ length keys = size m ∧ NoDup keys ⌝ -∗
     (P keys 0 ∗
      □ (∀ i key v, ⌜ (0 ≤ i < Z.of_nat (length keys))%Z ∧
          keys !! (Z.to_nat i) = Some key ∧ m !! key = Some v ⌝ -∗
          P keys i -∗
          WP #body #key #v @ stk; E
            {{ bv, for_map_postcondition_no_break (P keys (i + 1)%Z) bv }}) ∗
      (mref ↦${dq} m -∗ P keys (Z.of_nat (size m)) -∗ Φ execute_val))
  ) -∗
  WP map.for_range key_type elem_type #mref #body @ stk; E {{ Φ }}.
Proof.
  iIntros (Φ) "Hm HΦ".
  wp_call.
  iDestruct (own_map_not_nil with "[$]") as %?.
  wp_if_destruct; first by exfalso.
  rewrite own_map_unseal. iNamed "Hm".
  wp_apply (_internal_wp_untyped_start_read with "Hown") as "Hown".
  wp_apply (wp_InternalMapForRange with "[//]"). iIntros "%ks %Hdom'".
  eapply go.is_map_domain_pure in Hdom'; last done.
  destruct Hdom' as [Hks_nodup Hks].
  assert (Forall (λ kv, ∃ (k : K), kv = #k) ks) as Heq.
  { rewrite Forall_forall. intros kv Hk.
    specialize (Hks kv). specialize (Hdom kv).
    rewrite -Hks in Hk. apply Hdom in Hk. done. }
  apply Forall_exists_Forall2_l in Heq as [keys Heq].
  apply Forall2_fmap_2 in Heq. rewrite -list_eq_Forall2 in Heq.
  rewrite list_fmap_id in Heq. subst ks.
  iAssert (⌜ _ ⌝)%I with "[]" as "%Hfacts".
  2: iDestruct ("HΦ" $! keys with "[]") as "(HP & #Hiter & HΦ)".
  2: iPureIntro; exact Hfacts.
  { iPureIntro. eassert _ as Hl.
    2:{ split; first eexact Hl.
        apply NoDup_fmap in Hks_nodup; last tc_solve.
        rewrite <- (size_list_to_set (C:=gset K)); last done.
        rewrite Hl. rewrite size_dom //. }
    rewrite sets.set_eq. intros k.
    rewrite elem_of_list_to_set.
    specialize (Hks #k). specialize (Hagree k).
    rewrite list_elem_of_fmap_inj in Hks.
    rewrite -Hks Hagree elem_of_dom.
    destruct (m !! k); split; eauto; intros ?; done. }
  pose (i := 0%Z : Z).
  change (P keys 0) with (P keys i).
  iFreeze "Hiter".
  replace (into_val <$> keys) with (into_val <$> (drop (Z.to_nat i) keys)).
  2:{ rewrite drop_0 //. }
  iThaw "Hiter".
  iAssert (⌜ (0 ≤ i ≤ Z.of_nat (length keys))%Z ⌝)%I as "-#Hi".
  { subst i. iPureIntro. split; [lia|apply Nat2Z.is_nonneg]. }
  generalize i. clear i. intros i.
  iLöb as "IH" forall (i). iDestruct "Hi" as %Hi_bounds.
  destruct Hi_bounds as [Hi_nonneg Hi_upper].
  destruct (decide (i < Z.of_nat (length keys))%Z).
  2:{
    assert (i = Z.of_nat (length keys)) by lia. subst.
    rewrite Nat2Z.id drop_all /=.
    wp_auto. wp_apply "Hown". iIntros "Hown".
    wp_auto.
    destruct Hfacts as (_ & Hkeys_len & _).
    rewrite Hkeys_len.
    iAssert (own_map_def mref dq m) with "[Hown]" as "Hm".
    { iExists mv, mp. iFrame "Hown". iFrame "%". }
    iApply ("HΦ" with "Hm HP").
  }
  list_elem keys i as key.
  destruct (m !! key) eqn:Hlookup.
  2:{
    exfalso. apply not_elem_of_dom_2 in Hlookup as Hkey_m.
    destruct Hfacts as [Hfact _]. rewrite <- Hfact in Hkey_m.
    rewrite elem_of_list_to_set in Hkey_m.
    rewrite list_elem_of_lookup in Hkey_m.
    destruct Hkey_m. eexists. exact Hkey_lookup.
  }
  iSpecialize ("Hiter" $! i key v with "[] HP").
  { iPureIntro. split_and!; done. }
  erewrite drop_S; last done. rewrite fmap_cons foldr_cons.
  rewrite Hagree Hlookup /=. wp_apply (wp_wand with "Hiter").
  iIntros (execv) "Hpost".
  iDestruct "Hpost" as "[[-> H]|[-> H]]".
  - wp_auto. rewrite continue_val_unseal. wp_auto.
    replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
    iApply ("IH" with "[$Hown] H HΦ").
    iPureIntro. lia.
  - wp_auto. rewrite execute_val_unseal. wp_auto.
    replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
    iApply ("IH" with "[$Hown] H HΦ").
    iPureIntro. lia.
Qed.

Lemma wp_map_for_range_return_or_return
    `{!ZeroVal K} `{!EqDecision K} `{!Countable K} `{!ZeroVal V}
    `{!go.IntoValInj K} `{!TypedPointsto K} `{!IntoValTyped K key_type}
    (P : list K → Z → iProp Σ) (R : val → iProp Σ) stk E
    (body : func.t) elem_type mref (m : gmap K V) dq :
  ∀ Φ,
  mref ↦${dq} m -∗
  (∀ keys,
     ⌜ list_to_set keys = dom m ∧ length keys = size m ∧ NoDup keys ⌝ -∗
     (P keys 0 ∗
      □ (∀ i key v, ⌜ (0 ≤ i < Z.of_nat (length keys))%Z ∧
          keys !! (Z.to_nat i) = Some key ∧ m !! key = Some v ⌝ -∗
          P keys i -∗
          WP #body #key #v @ stk; E
            {{ bv, for_map_postcondition_return (P keys (i + 1)%Z) R bv }}) ∗
      (∀ bv, mref ↦${dq} m -∗
        ((⌜ bv = execute_val ⌝ ∗ P keys (Z.of_nat (size m))) ∨ R bv) -∗
        Φ bv))
  ) -∗
  WP map.for_range key_type elem_type #mref #body @ stk; E {{ Φ }}.
Proof.
  iIntros (Φ) "Hm HΦ".
  wp_call.
  iDestruct (own_map_not_nil with "[$]") as %?.
  wp_if_destruct; first by exfalso.
  rewrite own_map_unseal. iNamed "Hm".
  wp_apply (_internal_wp_untyped_start_read with "Hown") as "Hown".
  wp_apply (wp_InternalMapForRange with "[//]"). iIntros "%ks %Hdom'".
  eapply go.is_map_domain_pure in Hdom'; last done.
  destruct Hdom' as [Hks_nodup Hks].
  assert (Forall (λ kv, ∃ (k : K), kv = #k) ks) as Heq.
  { rewrite Forall_forall. intros kv Hk.
    specialize (Hks kv). specialize (Hdom kv).
    rewrite -Hks in Hk. apply Hdom in Hk. done. }
  apply Forall_exists_Forall2_l in Heq as [keys Heq].
  apply Forall2_fmap_2 in Heq. rewrite -list_eq_Forall2 in Heq.
  rewrite list_fmap_id in Heq. subst ks.
  iAssert (⌜ _ ⌝)%I with "[]" as "%Hfacts".
  2: iDestruct ("HΦ" $! keys with "[]") as
    "(HP & #Hiter & HΦ)".
  2: iPureIntro; exact Hfacts.
  { iPureIntro. eassert _ as Hl.
    2:{ split; first eexact Hl.
        apply NoDup_fmap in Hks_nodup; last tc_solve.
        rewrite <- (size_list_to_set (C:=gset K)); last done.
        rewrite Hl. rewrite size_dom //. }
    rewrite sets.set_eq. intros k.
    rewrite elem_of_list_to_set.
    specialize (Hks #k). specialize (Hagree k).
    rewrite list_elem_of_fmap_inj in Hks.
    rewrite -Hks Hagree elem_of_dom.
    destruct (m !! k); split; eauto; intros ?; done. }
  pose (i := 0%Z : Z).
  change (P keys 0) with (P keys i).
  iFreeze "Hiter".
  replace (into_val <$> keys) with (into_val <$> (drop (Z.to_nat i) keys)).
  2:{ rewrite drop_0 //. }
  iThaw "Hiter".
  iAssert (⌜ (0 ≤ i ≤ Z.of_nat (length keys))%Z ⌝)%I as "-#Hi".
  { subst i. iPureIntro. split; [lia|apply Nat2Z.is_nonneg]. }
  generalize i. clear i. intros i.
  iLöb as "IH" forall (i). iDestruct "Hi" as %Hi_bounds.
  destruct Hi_bounds as [Hi_nonneg Hi_upper].
  destruct (decide (i < Z.of_nat (length keys))%Z).
  2:{
    assert (i = Z.of_nat (length keys)) by lia. subst.
    rewrite Nat2Z.id drop_all /=.
    wp_auto. wp_apply "Hown". iIntros "Hown".
    wp_auto.
    destruct Hfacts as (_ & Hkeys_len & _).
    rewrite Hkeys_len.
    iAssert (own_map_def mref dq m) with "[Hown]" as "Hm".
    { iExists mv, mp. iFrame "Hown". iFrame "%". }
    iApply ("HΦ" $! execute_val with "Hm").
    iLeft. iFrame. done.
  }
  list_elem keys i as key.
  destruct (m !! key) eqn:Hlookup.
  2:{
    exfalso. apply not_elem_of_dom_2 in Hlookup as Hkey_m.
    destruct Hfacts as [Hfact _]. rewrite <- Hfact in Hkey_m.
    rewrite elem_of_list_to_set in Hkey_m.
    rewrite list_elem_of_lookup in Hkey_m.
    destruct Hkey_m. eexists. exact Hkey_lookup.
  }
  iSpecialize ("Hiter" $! i key v with "[] HP").
  { iPureIntro. split_and!; done. }
  erewrite drop_S; last done. rewrite fmap_cons foldr_cons.
  rewrite Hagree Hlookup /=. wp_apply (wp_wand with "Hiter").
  iIntros (execv) "Hpost".
  iDestruct "Hpost" as "[[-> H]|Hpost]".
  - wp_auto. rewrite continue_val_unseal. wp_auto.
    replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
    iApply ("IH" with "[$Hown] H HΦ").
    iPureIntro. lia.
  - wp_auto.
    iDestruct "Hpost" as "[[-> H]|Hpost]".
    + rewrite execute_val_unseal. wp_auto.
      replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
      iApply ("IH" with "[$Hown] H HΦ").
      iPureIntro. lia.
    + iDestruct "Hpost" as (rv) "(-> & HR)".
      rewrite return_val_unseal.
      wp_auto. wp_apply "Hown" as "Hown".
      iAssert (own_map_def mref dq m) with "[Hown]" as "Hm".
      { iExists mv, mp. iFrame "Hown". iFrame "%". }
      iApply ("HΦ" with "Hm").
      iRight. iExact "HR".
Qed.

Lemma wp_map_for_range_return_func
    `{!ZeroVal K} `{!EqDecision K} `{!Countable K} `{!ZeroVal V}
    `{!go.IntoValInj K} `{!TypedPointsto K} `{!IntoValTyped K key_type}
    (P : list K → Z → iProp Σ) stk E key_name value_name body elem_type
    mref (m : gmap K V) dq :
  key_name ≠ BNamed value_name →
  ∀ Φ,
  mref ↦${dq} m -∗
  (∀ keys,
     ⌜ list_to_set keys = dom m ∧ length keys = size m ∧ NoDup keys ⌝ -∗
     (P keys 0 ∗
      □ (∀ i key v, ⌜ (0 ≤ i < Z.of_nat (length keys))%Z ∧
          keys !! (Z.to_nat i) = Some key ∧ m !! key = Some v ⌝ -∗
          P keys i -∗
          WP subst' (BNamed value_name) #v
              (subst' key_name #key body) @ stk; E
            {{ bv, for_map_postcondition_no_break (P keys (i + 1)%Z) bv }}) ∗
      (mref ↦${dq} m -∗ P keys (Z.of_nat (size m)) -∗ Φ execute_val))
  ) -∗
  WP map.for_range key_type elem_type #mref
      #(func.mk <> key_name
          (λ: (BNamed value_name), body)%E)
      @ stk; E {{ Φ }}.
Proof.
  iIntros (Hnames Φ) "Hm HΦ".
  wp_apply (wp_map_for_range_return (key_type:=key_type) P with "Hm").
  iIntros (keys) "Hkeys".
  iDestruct ("HΦ" with "Hkeys") as "(HP & #Hiter & HΦ)".
  iFrame "HP HΦ".
  iModIntro. iIntros (i key v) "Hfacts HP".
  wp_pures.
  destruct key_name as [|key_name]; simpl in *; wp_pures.
  - iApply ("Hiter" with "Hfacts HP").
  - rewrite decide_True.
    { split; done. }
    iApply ("Hiter" with "Hfacts HP").
Qed.

End proof.
