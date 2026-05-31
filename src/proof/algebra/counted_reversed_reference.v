From New.proof Require Import prelude.
From iris.algebra Require Import cmra gmap gset.
From iris.base_logic.lib Require Import own.

(*
  counted_reversed_reference is the counted generalization of reversed_reference.

  For each reference [r], a fragment owns a map [K ↦ nat]. The count at key [k]
  is the number of times the projected value for [k] refers to [r]. Missing keys
  mean count zero. This is useful when one logical object can contain multiple
  references to the same target.
*)

Section counted_reversed_reference_frag.
Context (K : Type) `{Countable K} (R : Type) `{Countable R}.

Definition fragUR : ucmra := gmapUR R (prodR dfracR (agreeR (gmap K nat))).

Definition mk_frag (p : R) (dq : dfrac) (ks : gmap K nat) : fragUR :=
  {[p := (dq, to_agree ks)]}.

End counted_reversed_reference_frag.

Arguments fragUR _ {_ _} _ {_ _}.
Arguments mk_frag {_ _ _ _ _ _} _ _ _.

Section counted_reversed_reference.
Context (K : Type) `{Countable K} (R : Type) `{Countable R} (V : Type).
Context (extract_reference_count : V → gmap R nat) (to_reference : K → V → R).

Definition auth : Type := (gmap K V * gset R)%type.
Definition authO : ofe := leibnizO auth.

Definition proj_state (a : auth) : gmap K V := fst a.
Definition proj_used_reference_set (a : auth) : gset R := snd a.

Implicit Types (a : authO) (b : fragUR K R).
Implicit Types (k : K) (r : R) (v : V) (n : nat).

Definition reference_count (v : V) (r : R) : nat :=
  default 0 (extract_reference_count v !! r).

(* The counted inverse index for one reference: every key whose projected value
   contains [r], mapped to the positive number of occurrences of [r]. *)
Definition reverse_index (m : gmap K V) (r : R) : gmap K nat :=
  map_imap (λ _ v,
    let n := reference_count v r in
    if decide (0 < n)%nat then Some n else None) m.

Local Definition view_rel_raw n a b :=
  (map_Forall (λ k v, (to_reference k v) ∈ proj_used_reference_set a) (proj_state a)) ∧
  (map_Forall (λ _ '(dq, _), ✓ dq) b) ∧
  (map_Forall (λ r '(_, agree_ks),
    ∃ ks, agree_ks ≡ to_agree ks ∧ ks = reverse_index (proj_state a) r) b) ∧
  (map_Forall (λ r _, r ∈ proj_used_reference_set a) b).

Local Lemma view_rel_raw_mono n1 n2 a1 a2 b1 b2 :
  view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  (n2 ≤ n1)%nat →
  view_rel_raw n2 a2 b2.
Proof.
  intros [Hobj [Hvalid [Hchildren Hreferences]]] Ha Hb _.
  assert (Ha_eq : a1 = a2).
  { apply leibniz_equiv.
    apply (proj2 (discrete_iff n2 a1 a2)).
    exact Ha.
  }
  subst a2.
  split.
  - rewrite map_Forall_lookup.
    intros k v Hlookup.
    exact (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup).
  - split.
    + rewrite map_Forall_lookup.
      intros r [dq2 agree2] Hlookup2.
      destruct (lookup_includedN n2 b2 b1) as [Hlookup_incl _].
      specialize (Hlookup_incl Hb r).
      rewrite Hlookup2 in Hlookup_incl.
      destruct (Some_includedN_is_Some _ _ _ Hlookup_incl) as [da1 Hlookup1].
      destruct da1 as [dq1 agree1].
      destruct (Hchildren _ _ Hlookup1) as (ks & Hagree1 & _).
      pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup1) as Hvdq1.
      rewrite Hlookup1 in Hlookup_incl.
      assert (Hval1_n2 :
        ✓{n2} (Some (dq1, agree1) : option (dfrac * agree (gmap K nat)))).
      { simpl. apply cmra_valid_validN.
        apply pair_valid. split; [done|].
        rewrite Hagree1. done.
      }
      assert (Hval2_n2 :
        ✓{n2} (Some (dq2, agree2) : option (dfrac * agree (gmap K nat)))).
      { eapply cmra_validN_includedN.
        - exact Hval1_n2.
        - exact Hlookup_incl.
      }
      assert (Hvdq2_n2 : ✓{n2} dq2).
      { apply (proj1 (pair_validN dq2 agree2 n2)).
        simpl in Hval2_n2. done.
      }
      by apply (proj2 (cmra_discrete_valid_iff n2 dq2)).
    + split.
      * rewrite map_Forall_lookup.
        intros r [dq2 agree2] Hlookup2.
        destruct (lookup_includedN n2 b2 b1) as [Hlookup_incl _].
        specialize (Hlookup_incl Hb r).
        rewrite Hlookup2 in Hlookup_incl.
        destruct (Some_includedN_is_Some _ _ _ Hlookup_incl) as [da1 Hlookup1].
        destruct da1 as [dq1 agree1].
        destruct (Hchildren _ _ Hlookup1) as (ks & Hagree1 & Hdom1).
        rewrite Hlookup1 in Hlookup_incl.
        pose proof (Some_pair_includedN _ _ _ _ _ Hlookup_incl) as [_ Hagree_opt_incl].
        pose proof (proj1 (Some_includedN_total n2 agree2 agree1) Hagree_opt_incl)
          as Hagree_incl.
        assert (Hagree1_n2 : ✓{n2} agree1).
        { rewrite Hagree1. done. }
        pose proof (agree_valid_includedN n2 agree2 agree1 Hagree1_n2 Hagree_incl)
          as Hagree2_n2.
        exists ks.
        split.
        -- apply (proj2 (discrete_iff n2 agree2 (to_agree ks))).
           etrans; [exact Hagree2_n2|exact (Hagree1 n2)].
        -- done.
      * rewrite map_Forall_lookup.
        intros r da2 Hlookup2.
        destruct (lookup_includedN n2 b2 b1) as [Hlookup_incl _].
        specialize (Hlookup_incl Hb r).
        rewrite Hlookup2 in Hlookup_incl.
        destruct (Some_includedN_is_Some _ _ _ Hlookup_incl) as [da1 Hlookup1].
        exact (map_Forall_lookup_1 _ _ _ _ Hreferences Hlookup1).
Qed.

Local Lemma view_rel_raw_valid n a b :
  view_rel_raw n a b → ✓{n} b.
Proof.
  intros [_ [Hvalid [Hchildren _]]] r.
  destruct (b !! r) as [[dq agree_ks]|] eqn:Hlookup.
  - pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup) as Hvdq.
    pose proof (map_Forall_lookup_1 _ _ _ _ Hchildren Hlookup) as Hchild.
    destruct Hchild as (ks & Hagree & _).
    rewrite Hlookup.
    apply pair_validN. split.
    + apply cmra_valid_validN. done.
    + rewrite Hagree. done.
  - rewrite Hlookup. done.
Qed.

Local Lemma view_rel_raw_unit n :
  ∃ a, view_rel_raw n a ε.
Proof.
  exists (∅, ∅).
  rewrite /view_rel_raw /proj_state /proj_used_reference_set /=.
  split_and!.
  all: rewrite map_Forall_lookup; intros i x Hlookup;
    rewrite lookup_empty in Hlookup; done.
Qed.

Local Canonical Structure view_rel :
    view_rel authO (fragUR K R) :=
  ViewRel view_rel_raw view_rel_raw_mono
          view_rel_raw_valid view_rel_raw_unit.

Definition rr_auth dq a : viewR view_rel := ●V{dq} a.
Definition rr_frag b : viewR view_rel := ◯V b.
Notation "●RR a" := (rr_auth 1 a) (at level 20).
Notation "◯RR b" := (rr_frag b) (at level 20).

Lemma auth_frag_valid a r dq ks :
  ✓ (●RR a ⋅ ◯RR (mk_frag r dq ks)) →
  ks = reverse_index (proj_state a) r ∧
  r ∈ proj_used_reference_set a.
Proof.
  intros Hvalid.
  rewrite /rr_auth /rr_frag in Hvalid.
  pose proof (proj1 (view_both_dfrac_valid view_rel 1 a (mk_frag r dq ks)) Hvalid)
    as [_ Hrel].
  specialize (Hrel 0ᵢ).
  change (view_rel_raw 0ᵢ a (mk_frag r dq ks)) in Hrel.
  destruct Hrel as [_ [_ [Hchildren Hreferences]]].
  assert (Hlookup : mk_frag r dq ks !! r = Some (dq, to_agree ks)).
  { rewrite /mk_frag lookup_singleton_eq //. }
  destruct (Hchildren _ _ Hlookup) as (ks' & Hagree & Hdom).
  assert (Hks_eqv : ks ≡ ks').
  { apply (inj to_agree). by rewrite Hagree. }
  apply leibniz_equiv in Hks_eqv. subst ks'.
  split; [done|].
  eapply Hreferences; done.
Qed.

Lemma generic_update_from_old_obj a a' :
  (map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a) (proj_state a) →
    map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a') (proj_state a')) →
  (∀ r, r ∈ proj_used_reference_set a → r ∈ proj_used_reference_set a') →
  (∀ r, r ∈ proj_used_reference_set a → reverse_index (proj_state a') r = reverse_index (proj_state a) r) →
  ●RR a ~~> ●RR a'.
Proof.
  intros Hobj_transform Hused_preserve Hindex_preserve.
  apply view_update_auth.
  intros n bf [Hobj [Hvalid [Hchildren Hreferences]]].
  repeat split.
  - exact (Hobj_transform Hobj).
  - exact Hvalid.
  - rewrite map_Forall_lookup.
    intros r [dq agree_ks] Hb.
    destruct (Hchildren _ _ Hb) as (ks & Hagree & Hks).
    exists ks. split; [done|].
    pose proof (Hreferences _ _ Hb) as Hused.
    pose proof (Hindex_preserve r Hused) as Hindex.
    rewrite Hks. symmetry. exact Hindex.
  - rewrite map_Forall_lookup.
    intros r da Hb.
    apply Hused_preserve.
    eapply Hreferences; done.
Qed.

Lemma generic_update a a' :
  map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a') (proj_state a') →
  (∀ r, r ∈ proj_used_reference_set a → r ∈ proj_used_reference_set a') →
  (∀ r, r ∈ proj_used_reference_set a → reverse_index (proj_state a') r = reverse_index (proj_state a) r) →
  ●RR a ~~> ●RR a'.
Proof.
  intros Hobj' Hused_preserve Hindex_preserve.
  apply generic_update_from_old_obj; done.
Qed.

Lemma generic_reference_update_from_old_obj a a' r ks ks' :
  (map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a) (proj_state a) →
    map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a') (proj_state a')) →
  r ∈ proj_used_reference_set a' →
  reverse_index (proj_state a') r = ks' →
  (∀ r0, r0 ≠ r → r0 ∈ proj_used_reference_set a → r0 ∈ proj_used_reference_set a') →
  (∀ r0, r0 ≠ r → r0 ∈ proj_used_reference_set a → reverse_index (proj_state a') r0 = reverse_index (proj_state a) r0) →
  ●RR a ⋅ ◯RR (mk_frag r 1 ks) ~~>
    ●RR a' ⋅ ◯RR (mk_frag r 1 ks').
Proof.
  intros Hobj_transform Hused_r Hindex_r Hused_preserve Hindex_preserve.
  apply view_update.
  intros n bf [Hobj [Hvalid [Hchildren Hreferences]]].
  assert (Hbf_none : bf !! r = None).
  { destruct (bf !! r) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    assert (Hlookup :
      (mk_frag r 1 ks ⋅ bf) !! r = Some ((DfracOwn 1, to_agree ks) ⋅ (dqf, agf))).
    { rewrite lookup_op /mk_frag lookup_singleton_eq Hbf Some_op_opM //. }
    pose proof (Hvalid _ _ Hlookup) as Hvdq.
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dqf 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt.
    apply Hlt. reflexivity.
  }
  repeat split.
  - exact (Hobj_transform Hobj).
  - intros r0 [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks. done.
    + assert (Hlookup_new : mk_frag r 1 ks' !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some (dq, agree_ks)).
      { rewrite lookup_op.
        assert (Hlookup_old_frag : mk_frag r 1 ks !! r0 = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hlookup_old_frag Hb left_id //. }
      exact (map_Forall_lookup_1
        (λ _ '(dq0, _), ✓ dq0)
        (mk_frag r 1 ks ⋅ bf) r0 (dq, agree_ks)
        Hvalid Hlookup_old).
  - intros r0 [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks.
      exists ks'. split; [done|].
      symmetry. exact Hindex_r.
    + assert (Hlookup_new : mk_frag r 1 ks' !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some (dq, agree_ks)).
      { rewrite lookup_op.
        assert (Hlookup_old_frag : mk_frag r 1 ks !! r0 = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hlookup_old_frag Hb left_id //. }
      destruct (Hchildren _ _ Hlookup_old) as (ks0 & Hagree & Hdom).
      exists ks0. split; [done|].
      pose proof (Hreferences _ _ Hlookup_old) as Hused_old.
      pose proof (Hindex_preserve r0 Hneq Hused_old) as Hindex.
      rewrite Hdom. symmetry. exact Hindex.
  - intros r0 da Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + done.
    + rewrite lookup_op in Hb.
      assert (Hlookup_new : mk_frag r 1 ks' !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some da).
      { rewrite lookup_op.
        assert (Hlookup_old_frag : mk_frag r 1 ks !! r0 = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hlookup_old_frag Hb left_id //. }
      apply Hused_preserve; [done|].
      eapply Hreferences; done.
Qed.

Lemma generic_reference_update a a' r ks ks' :
  map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a') (proj_state a') →
  r ∈ proj_used_reference_set a' →
  reverse_index (proj_state a') r = ks' →
  (∀ r0, r0 ≠ r → r0 ∈ proj_used_reference_set a → r0 ∈ proj_used_reference_set a') →
  (∀ r0, r0 ≠ r → r0 ∈ proj_used_reference_set a → reverse_index (proj_state a') r0 = reverse_index (proj_state a) r0) →
  ●RR a ⋅ ◯RR (mk_frag r 1 ks) ~~>
    ●RR a' ⋅ ◯RR (mk_frag r 1 ks').
Proof.
  intros Hobj' Hused_r Hindex_r Hused_preserve Hindex_preserve.
  apply generic_reference_update_from_old_obj; done.
Qed.

Lemma generic_alloc_reference_from_old_obj a a' r ks :
  r ∉ proj_used_reference_set a →
  (map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a) (proj_state a) →
    map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a') (proj_state a')) →
  r ∈ proj_used_reference_set a' →
  reverse_index (proj_state a') r = ks →
  (∀ r0, r0 ∈ proj_used_reference_set a → r0 ∈ proj_used_reference_set a') →
  (∀ r0, r0 ∈ proj_used_reference_set a → reverse_index (proj_state a') r0 = reverse_index (proj_state a) r0) →
  ●RR a ~~> ●RR a' ⋅ ◯RR (mk_frag r 1 ks).
Proof.
  intros Hfresh Hobj_transform Hused_r Hindex_r Hused_preserve Hindex_preserve.
  apply view_update_alloc.
  intros n bf [Hobj [Hvalid [Hchildren Hreferences]]].
  assert (Hbf_none : bf !! r = None).
  { destruct (bf !! r) as [da|] eqn:Hbf; [|done].
    exfalso. apply Hfresh. eapply Hreferences; done.
  }
  repeat split.
  - exact (Hobj_transform Hobj).
  - intros r0 [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks. done.
    + assert (Hlookup_new : mk_frag r 1 ks !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      exact (Hvalid _ _ Hb).
  - intros r0 [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks.
      exists ks. split; [done|].
      symmetry. exact Hindex_r.
    + assert (Hlookup_new : mk_frag r 1 ks !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      destruct (Hchildren _ _ Hb) as (ks0 & Hagree & Hdom).
      exists ks0. split; [done|].
      pose proof (Hreferences _ _ Hb) as Hused_old.
      pose proof (Hindex_preserve r0 Hused_old) as Hindex.
      rewrite Hdom. symmetry. exact Hindex.
  - intros r0 da Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + done.
    + rewrite lookup_op in Hb.
      assert (Hlookup_new : mk_frag r 1 ks !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      apply Hused_preserve.
      eapply Hreferences; done.
Qed.

Lemma generic_alloc_reference a a' r ks :
  r ∉ proj_used_reference_set a →
  map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a') (proj_state a') →
  r ∈ proj_used_reference_set a' →
  reverse_index (proj_state a') r = ks →
  (∀ r0, r0 ∈ proj_used_reference_set a → r0 ∈ proj_used_reference_set a') →
  (∀ r0, r0 ∈ proj_used_reference_set a → reverse_index (proj_state a') r0 = reverse_index (proj_state a) r0) →
  ●RR a ~~> ●RR a' ⋅ ◯RR (mk_frag r 1 ks).
Proof.
  intros Hfresh Hobj' Hused_r Hindex_r Hused_preserve Hindex_preserve.
  apply generic_alloc_reference_from_old_obj; done.
Qed.

Lemma generic_reference_update_alloc_reference_from_old_obj a a' r ks ks' new_r new_ks :
  new_r ∉ proj_used_reference_set a →
  r ≠ new_r →
  (map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a) (proj_state a) →
    map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a') (proj_state a')) →
  r ∈ proj_used_reference_set a' →
  new_r ∈ proj_used_reference_set a' →
  reverse_index (proj_state a') r = ks' →
  reverse_index (proj_state a') new_r = new_ks →
  (∀ r0, r0 ≠ r → r0 ∈ proj_used_reference_set a → r0 ∈ proj_used_reference_set a') →
  (∀ r0, r0 ≠ r → r0 ∈ proj_used_reference_set a → reverse_index (proj_state a') r0 = reverse_index (proj_state a) r0) →
  ●RR a ⋅ ◯RR (mk_frag r 1 ks) ~~>
    ●RR a' ⋅ ◯RR (mk_frag r 1 ks') ⋅ ◯RR (mk_frag new_r 1 new_ks).
Proof.
  intros Hfresh Hneq_new Hobj_transform Hused_r Hused_new Hindex_r Hindex_new
    Hused_preserve Hindex_preserve.
  rewrite -assoc /rr_frag -view_frag_op.
  apply view_update.
  intros n bf [Hobj [Hvalid [Hchildren Hreferences]]].
  assert (Hbf_none_r : bf !! r = None).
  { destruct (bf !! r) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    assert (Hlookup :
      (mk_frag r 1 ks ⋅ bf) !! r = Some ((DfracOwn 1, to_agree ks) ⋅ (dqf, agf))).
    { rewrite lookup_op /mk_frag lookup_singleton_eq Hbf Some_op_opM //. }
    pose proof (Hvalid _ _ Hlookup) as Hvdq.
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dqf 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt.
    apply Hlt. reflexivity.
  }
  assert (Hbf_none_new : bf !! new_r = None).
  { destruct (bf !! new_r) as [da|] eqn:Hbf; [|done].
    exfalso. apply Hfresh.
    assert (Hlookup_old_new : (mk_frag r 1 ks ⋅ bf) !! new_r = Some da).
    { rewrite lookup_op.
      assert (Hnone_old_r : mk_frag r 1 ks !! new_r = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hnone_old_r Hbf left_id //. }
    eapply Hreferences; done.
  }
  repeat split.
  - exact (Hobj_transform Hobj).
  - intros r0 [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq_r].
    + assert (Hlookup_rg_r :
        (mk_frag r 1 ks' ⋅ mk_frag new_r 1 new_ks) !! r =
        Some (DfracOwn 1, to_agree ks')).
      { rewrite lookup_op /mk_frag lookup_singleton_eq.
        assert (Hnew_none_r : mk_frag new_r 1 new_ks !! r = None).
        { rewrite /mk_frag lookup_singleton_ne; congruence. }
        rewrite Hnew_none_r right_id //. }
      rewrite Hlookup_rg_r Hbf_none_r right_id in Hb.
      inversion Hb; subst dq agree_ks. done.
    + destruct (decide (r0 = new_r)) as [->|Hneq_new_r0].
      * assert (Hlookup_rg_new :
          (mk_frag r 1 ks' ⋅ mk_frag new_r 1 new_ks) !! new_r =
          Some (DfracOwn 1, to_agree new_ks)).
        { rewrite lookup_op.
          assert (Hr_none_new : mk_frag r 1 ks' !! new_r = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hr_none_new /mk_frag lookup_singleton_eq left_id //. }
        rewrite Hlookup_rg_new Hbf_none_new right_id in Hb.
        inversion Hb; subst dq agree_ks. done.
      * assert (Hlookup_rg_none :
          (mk_frag r 1 ks' ⋅ mk_frag new_r 1 new_ks) !! r0 = None).
        { rewrite lookup_op.
          assert (Hr_none : mk_frag r 1 ks' !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          assert (Hnew_none : mk_frag new_r 1 new_ks !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hr_none Hnew_none left_id //. }
        rewrite Hlookup_rg_none in Hb.
        rewrite left_id in Hb.
        assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some (dq, agree_ks)).
        { rewrite lookup_op.
          assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hnone_old Hb left_id //. }
        exact (map_Forall_lookup_1
          (λ _ '(dq0, _), ✓ dq0)
          (mk_frag r 1 ks ⋅ bf) r0 (dq, agree_ks)
          Hvalid Hlookup_old).
  - intros r0 [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq_r].
    + assert (Hlookup_rg_r :
        (mk_frag r 1 ks' ⋅ mk_frag new_r 1 new_ks) !! r =
        Some (DfracOwn 1, to_agree ks')).
      { rewrite lookup_op /mk_frag lookup_singleton_eq.
        assert (Hnew_none_r : mk_frag new_r 1 new_ks !! r = None).
        { rewrite /mk_frag lookup_singleton_ne; congruence. }
        rewrite Hnew_none_r right_id //. }
      rewrite Hlookup_rg_r Hbf_none_r right_id in Hb.
      inversion Hb; subst dq agree_ks.
      exists ks'. split; [done|].
      symmetry. exact Hindex_r.
    + destruct (decide (r0 = new_r)) as [->|Hneq_new_r0].
      * assert (Hlookup_rg_new :
          (mk_frag r 1 ks' ⋅ mk_frag new_r 1 new_ks) !! new_r =
          Some (DfracOwn 1, to_agree new_ks)).
        { rewrite lookup_op.
          assert (Hr_none_new : mk_frag r 1 ks' !! new_r = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hr_none_new /mk_frag lookup_singleton_eq left_id //. }
        rewrite Hlookup_rg_new Hbf_none_new right_id in Hb.
        inversion Hb; subst dq agree_ks.
        exists new_ks. split; [done|].
        symmetry. exact Hindex_new.
      * assert (Hlookup_rg_none :
          (mk_frag r 1 ks' ⋅ mk_frag new_r 1 new_ks) !! r0 = None).
        { rewrite lookup_op.
          assert (Hr_none : mk_frag r 1 ks' !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          assert (Hnew_none : mk_frag new_r 1 new_ks !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hr_none Hnew_none left_id //. }
        rewrite Hlookup_rg_none in Hb.
        rewrite left_id in Hb.
        assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some (dq, agree_ks)).
        { rewrite lookup_op.
          assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hnone_old Hb left_id //. }
        destruct (Hchildren _ _ Hlookup_old) as (ks0 & Hagree & Hdom).
        exists ks0. split; [done|].
        pose proof (Hreferences _ _ Hlookup_old) as Hused_old.
        pose proof (Hindex_preserve r0 Hneq_r Hused_old) as Hindex.
        rewrite Hdom. symmetry. exact Hindex.
  - intros r0 da Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq_r].
    + done.
    + destruct (decide (r0 = new_r)) as [->|Hneq_new_r0].
      * done.
      * assert (Hlookup_rg_none :
          (mk_frag r 1 ks' ⋅ mk_frag new_r 1 new_ks) !! r0 = None).
        { rewrite lookup_op.
          assert (Hr_none : mk_frag r 1 ks' !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          assert (Hnew_none : mk_frag new_r 1 new_ks !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hr_none Hnew_none left_id //. }
        rewrite Hlookup_rg_none in Hb.
        rewrite left_id in Hb.
        assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some da).
        { rewrite lookup_op.
          assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hnone_old Hb left_id //. }
        apply Hused_preserve; [done|].
        eapply Hreferences; done.
Qed.

Lemma generic_reference_update_alloc_reference a a' r ks ks' new_r new_ks :
  new_r ∉ proj_used_reference_set a →
  r ≠ new_r →
  map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a') (proj_state a') →
  r ∈ proj_used_reference_set a' →
  new_r ∈ proj_used_reference_set a' →
  reverse_index (proj_state a') r = ks' →
  reverse_index (proj_state a') new_r = new_ks →
  (∀ r0, r0 ≠ r → r0 ∈ proj_used_reference_set a → r0 ∈ proj_used_reference_set a') →
  (∀ r0, r0 ≠ r → r0 ∈ proj_used_reference_set a → reverse_index (proj_state a') r0 = reverse_index (proj_state a) r0) →
  ●RR a ⋅ ◯RR (mk_frag r 1 ks) ~~>
    ●RR a' ⋅ ◯RR (mk_frag r 1 ks') ⋅ ◯RR (mk_frag new_r 1 new_ks).
Proof.
  intros Hfresh Hneq_new Hobj' Hused_r Hused_new Hindex_r Hindex_new
    Hused_preserve Hindex_preserve.
  apply generic_reference_update_alloc_reference_from_old_obj; done.
Qed.

Class counted_reversed_referenceG Σ :=
  { #[global] counted_reversed_reference_inG :: inG Σ (viewR view_rel); }.

Definition counted_reversed_referenceΣ :=
  #[GFunctor (viewR view_rel)].

#[global]
Instance subG_counted_reversed_referenceG Σ :
  subG counted_reversed_referenceΣ Σ → counted_reversed_referenceG Σ.
Proof. solve_inG. Qed.

Context `{!counted_reversed_referenceG Σ}.

Global Instance own_auth_timeless γ a : Timeless (own γ (●RR a)).
Proof. apply _. Qed.

Global Instance own_frag_timeless γ b : Timeless (own γ (◯RR b)).
Proof. apply _. Qed.

Definition own_auth γ (a : auth) : iProp Σ :=
  own γ (●RR a).

Definition own_frag γ r dq ks : iProp Σ :=
  own γ (◯RR (mk_frag r dq ks)).

Lemma own_auth_frag_valid {γ a r dq ks} :
  own_auth γ a -∗
  own_frag γ r dq ks -∗
  ⌜ ks = reverse_index (proj_state a) r ⌝ ∗
  ⌜ r ∈ proj_used_reference_set a ⌝.
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_valid_2 with "Hauth Hfrag") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  rewrite /own_auth /own_frag in Hvalid0.
  pose proof (proj1 (view_both_validN view_rel 0%nat
    a (mk_frag r dq ks)) Hvalid0) as Hrel0.
  assert (Hvalid : ✓ (●RR a ⋅ ◯RR (mk_frag r dq ks))).
  { rewrite /rr_auth /rr_frag.
    apply (proj2 (view_both_valid view_rel a (mk_frag r dq ks))).
    intros n. exact Hrel0.
  }
  pose proof (auth_frag_valid a r dq ks Hvalid) as [Hks Hr].
  split; done.
Qed.

Lemma own_auth_frag_remove_zero_counts {γ a r dq ks} :
  own_auth γ a -∗
  own_frag γ r dq ks -∗
  ⌜ filter (λ '(_, n), (0 < n)%nat) ks = ks ⌝.
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_auth_frag_valid with "Hauth Hfrag") as "[%Hks _]".
  iPureIntro.
  rewrite Hks.
  apply map_eq. intros k.
  rewrite map_lookup_filter /reverse_index !map_lookup_imap.
  destruct (proj_state a !! k) as [v|] eqn:Hlookup; simpl; [|done].
  unfold reference_count.
  destruct (decide (0 < default 0 (extract_reference_count v !! r))%nat) as [Hpos|Hnpos]; simpl; [|done].
  rewrite option_guard_True; done.
Qed.

Lemma own_auth_frag_normalize {γ a r dq ks} :
  own_auth γ a -∗
  own_frag γ r dq ks -∗
    own_auth γ a ∗ own_frag γ r dq (filter (λ '(_, n), (0 < n)%nat) ks).
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_auth_frag_remove_zero_counts with "Hauth Hfrag") as %Hks.
  rewrite Hks. iFrame.
Qed.

Lemma generic_update_vs {γ a a'} :
  map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a') (proj_state a') →
  (∀ r, r ∈ proj_used_reference_set a → r ∈ proj_used_reference_set a') →
  (∀ r, r ∈ proj_used_reference_set a → reverse_index (proj_state a') r = reverse_index (proj_state a) r) →
  own_auth γ a ==∗ own_auth γ a'.
Proof.
  iIntros (Hobj Hused Hindex) "Hauth".
  iMod (own_update with "Hauth") as "Hauth".
  { eapply generic_update; done. }
  iModIntro. iExact "Hauth".
Qed.

Lemma generic_reference_update_vs {γ a a' r ks ks'} :
  map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a') (proj_state a') →
  r ∈ proj_used_reference_set a' →
  reverse_index (proj_state a') r = ks' →
  (∀ r0, r0 ≠ r → r0 ∈ proj_used_reference_set a → r0 ∈ proj_used_reference_set a') →
  (∀ r0, r0 ≠ r → r0 ∈ proj_used_reference_set a → reverse_index (proj_state a') r0 = reverse_index (proj_state a) r0) →
  own_auth γ a -∗
  own_frag γ r 1 ks ==∗
    own_auth γ a' ∗ own_frag γ r 1 ks'.
Proof.
  iIntros (Hobj Hused_r Hindex_r Hused Hindex) "Hauth Hfrag".
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { eapply generic_reference_update; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[Hauth Hfrag]".
  iFrame.
Qed.

Lemma generic_alloc_reference_vs {γ a a' r ks} :
  r ∉ proj_used_reference_set a →
  map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a') (proj_state a') →
  r ∈ proj_used_reference_set a' →
  reverse_index (proj_state a') r = ks →
  (∀ r0, r0 ∈ proj_used_reference_set a → r0 ∈ proj_used_reference_set a') →
  (∀ r0, r0 ∈ proj_used_reference_set a → reverse_index (proj_state a') r0 = reverse_index (proj_state a) r0) →
  own_auth γ a ==∗
    own_auth γ a' ∗ own_frag γ r 1 ks.
Proof.
  iIntros (Hfresh Hobj Hused_r Hindex_r Hused Hindex) "Hauth".
  iMod (own_update with "Hauth") as "H".
  { eapply generic_alloc_reference; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[Hauth Hfrag]".
  iFrame.
Qed.

Lemma generic_reference_update_alloc_reference_vs {γ a a' r ks ks' new_r new_ks} :
  new_r ∉ proj_used_reference_set a →
  r ≠ new_r →
  map_Forall (λ k v, to_reference k v ∈ proj_used_reference_set a') (proj_state a') →
  r ∈ proj_used_reference_set a' →
  new_r ∈ proj_used_reference_set a' →
  reverse_index (proj_state a') r = ks' →
  reverse_index (proj_state a') new_r = new_ks →
  (∀ r0, r0 ≠ r → r0 ∈ proj_used_reference_set a → r0 ∈ proj_used_reference_set a') →
  (∀ r0, r0 ≠ r → r0 ∈ proj_used_reference_set a → reverse_index (proj_state a') r0 = reverse_index (proj_state a) r0) →
  own_auth γ a -∗
  own_frag γ r 1 ks ==∗
    own_auth γ a' ∗ own_frag γ r 1 ks' ∗ own_frag γ new_r 1 new_ks.
Proof.
  iIntros (Hfresh Hneq_new Hobj Hused_r Hused_new Hindex_r Hindex_new Hused Hindex)
    "Hauth Hfrag".
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { eapply generic_reference_update_alloc_reference; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[H Hfrag_new]".
  iDestruct (own_op with "H") as "[Hauth Hfrag]".
  iFrame.
Qed.

End counted_reversed_reference.
