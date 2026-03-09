From New.proof Require Import prelude.
From iris.algebra Require Import cmra gset.

(*
  reversed_reference describes reversed reference using Iris' view resource algebra.
  
  The auth is a map from key (K) to value (V), where each value has at most one
  reference (R) pointing to another key in the map. We say the reference is from
  a child to its parent.

  The frag is a map from reference to set of keys. For each reference, the set of
  keys give us exactly the set of values in the auth that shares this reference.
  The frag gives us the reversed reference: from the parent to all its children.
  Note that entry (r, s) in the frag doesn't imply that the parent referred to as r
  currently exists in the auth.

  Function f abstracts how to retrieve the reference from the value. Function g
  abstracts how to convert the key and value into a reference that other values
  might point to. In some simple cases where R equals K, g just returns the key and
  ignores the value.

  One usage of this resource algebra is to describe the parent reference (or owner
  reference) mechanism in Kubernetes, where each object has at most one controller
  owner. We often need to reason about the state of all children objects of a given
  parent object, which is described by the frag. In this case, K is KKey.t, V is the
  KObjectV.t, R is the product of KKey.t and UID.t, f returns the (only) controller
  owner if it exists, and g returns the product of key and uid.
*)


Section reversed_reference.
Context {K : Type} `{Countable K} {R : Type} `{Countable R} {V : Type}.
Context {f : V → option R} {g : K → V → R}.

Definition authO : ofe := prodO (gmapO K (leibnizO V)) (gsetO (leibnizO R)).

Definition fragUR : ucmra := gmapUR R (prodR dfracR (agreeR (gset K))).

Implicit Types (a : authO) (b : fragUR).
Implicit Types (k : K) (r : R) (v : V) (n : nat).

Local Definition proj_state a : gmap K V := fst a.
Local Definition proj_used_reference a : gset R := snd a.

Local Definition view_rel_raw n a b :=
  (* each obj in a is a used reference *)
  (map_Forall (λ k v, (g k v) ∈ (proj_used_reference a)) (proj_state a)) ∧
  (* dfracs are valid *)
  (map_Forall (λ _ '(dq, _), ✓ dq) b) ∧
  (* for each (r, ks) in b, ks is the set of children of r in a *)
  (map_Forall (λ r '(_, agree_ks),
    ∃ ks, agree_ks ≡ to_agree ks ∧ ks = dom (filter (λ '(_, v), f v = Some r) (proj_state a))) b) ∧
  (* each r in b is a used reference *)
  (map_Forall (λ r _, r ∈ (proj_used_reference a)) b).

Local Lemma view_rel_raw_mono n1 n2 a1 a2 b1 b2 :
  view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  (n2 ≤ n1)%nat →
  view_rel_raw n2 a2 b2.
Proof.
  intros [Hobj [Hvalid [Hchildren Hreferences]]] Ha Hb _.
  destruct a1 as [state1 used1], a2 as [state2 used2].
  simpl in *.
  destruct Ha as [Hstate Hused].
  assert (Hstate_eqv : state1 ≡ state2).
  { apply (proj2 (discrete_iff n2 state1 state2)).
    exact Hstate.
  }
  assert (Hstate_eq : state1 = state2).
  { change ((state1 : gmap K (leibnizO V)) =
            (state2 : gmap K (leibnizO V))).
    apply map_eq. intros k.
    pose proof (proj1 (map_equiv_iff state1 state2) Hstate_eqv k) as Hlookup_eqv.
    apply leibniz_equiv in Hlookup_eqv. done.
  }
  subst state2.
  assert (Hused_eqv : used1 ≡ used2).
  { apply (proj2 (discrete_iff n2 used1 used2)).
    exact Hused.
  }
  assert (Hused_elem : ∀ r, r ∈ used1 ↔ r ∈ used2).
  { exact (proj1 (set_equiv used1 used2) Hused_eqv). }
  split.
  - rewrite map_Forall_lookup.
    intros k v Hlookup.
    pose proof (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup) as Hr_used1.
    apply (proj1 (Hused_elem _)).
    exact Hr_used1.
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
        ✓{n2} (Some (dq1, agree1) : option (dfrac * agree (gset K)))).
      { simpl. apply cmra_valid_validN.
        apply pair_valid. split; [done|].
        rewrite Hagree1. done.
      }
      assert (Hval2_n2 :
        ✓{n2} (Some (dq2, agree2) : option (dfrac * agree (gset K)))).
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
        pose proof (map_Forall_lookup_1 _ _ _ _ Hreferences Hlookup1) as Hr_used1.
        apply (proj1 (Hused_elem _)).
        exact Hr_used1.
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
  exists ((∅ : gmap K V), (∅ : gset R)).
  split_and!.
  all: rewrite map_Forall_lookup; intros i x Hlookup;
    rewrite lookup_empty in Hlookup; done.
Qed.

Local Canonical Structure view_rel :
    view_rel authO fragUR :=
  ViewRel view_rel_raw view_rel_raw_mono
          view_rel_raw_valid view_rel_raw_unit.

Definition cview_auth dq a : viewR view_rel := ●V{dq} a.
Definition cview_frag b : viewR view_rel := ◯V b.
Definition mk_frag (p: R) (dq: dfrac) (ks: gset K) : fragUR :=
  {[p := (dq, to_agree ks)]}.
Notation "●C a" := (cview_auth 1 a) (at level 20).
Notation "◯C b" := (cview_frag b) (at level 20).

Lemma auth_frag_valid a r dq ks:
✓ (●C a ⋅ ◯C (mk_frag r dq ks)) →
ks = dom (filter (λ '(_, v), f v = Some r) (proj_state a)) ∧
r ∈ (proj_used_reference a).
Proof.
  intros Hvalid.
  rewrite /cview_auth /cview_frag in Hvalid.
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

Lemma create_child a k v r ks cks:
(proj_state a) !! k = None →
f v = Some r →
g k v ≠ r → (* No self-parenting *)
dom (filter (λ '(_, v'), f v' = Some (g k v)) (proj_state a)) = cks →
g k v ∉ (proj_used_reference a) →
●C a ⋅
◯C (mk_frag r 1 ks) ~~>
  ●C ((<[k := v]> (proj_state a)), ((proj_used_reference a) ∪ {[g k v]})) ⋅
  ◯C (mk_frag r 1 (ks ∪ {[k]})) ⋅
  ◯C (mk_frag (g k v) 1 cks).
Proof.
  intros Hak Hfr Hnself Hcks Hfresh.
  rewrite -assoc /cview_frag -view_frag_op.
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
  assert (Hbf_none_g : bf !! (g k v) = None).
  { destruct (bf !! (g k v)) as [da|] eqn:Hbf; [|done].
    exfalso. apply Hfresh.
    assert (Hlookup_old_g : (mk_frag r 1 ks ⋅ bf) !! (g k v) = Some da).
    { rewrite lookup_op.
      assert (Hnone_old_r : mk_frag r 1 ks !! (g k v) = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hnone_old_r Hbf left_id //. }
    eapply Hreferences; done.
  }
  assert (Hlookup_r_old :
    (mk_frag r 1 ks ⋅ bf) !! r = Some (DfracOwn 1, to_agree ks)).
  { rewrite lookup_op /mk_frag lookup_singleton_eq Hbf_none_r right_id //. }
  assert (Hks_dom : ks = dom (filter (λ '(_, v0), f v0 = Some r) (proj_state a))).
  { destruct (Hchildren _ _ Hlookup_r_old) as (ks' & Hagree & Hdom).
    assert (Hks_eqv : ks ≡ ks').
    { apply (inj to_agree). by rewrite Hagree. }
    apply leibniz_equiv in Hks_eqv. subst ks'. done.
  }
  assert (Hr_used : r ∈ proj_used_reference a).
  { eapply Hreferences; done. }

  split_and!.
  - rewrite map_Forall_lookup.
    intros k0 v0 Hlookup0.
    simpl in Hlookup0.
    destruct (decide (k0 = k)) as [->|Hneq_k].
    + apply lookup_insert_Some in Hlookup0.
      destruct Hlookup0 as [[_ Hv0]|[Hneq _]].
      * symmetry in Hv0. subst v0.
        apply elem_of_union. right.
        apply elem_of_singleton. reflexivity.
      * exfalso. apply Hneq. reflexivity.
    + apply lookup_insert_Some in Hlookup0.
      destruct Hlookup0 as [[Heq _]|[_ Hlookup_old]].
      * exfalso. apply Hneq_k. symmetry. exact Heq.
      * pose proof (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old) as Hobj_used.
        apply elem_of_union. left. exact Hobj_used.
  - intros r0 [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq_r].
    + assert (Hlookup_rg_r :
        (mk_frag r 1 (ks ∪ {[k]}) ⋅ mk_frag (g k v) 1 cks) !! r =
        Some (DfracOwn 1, to_agree (ks ∪ {[k]}))).
      { rewrite lookup_op /mk_frag lookup_singleton_eq.
        assert (Hg_none_r : mk_frag (g k v) 1 cks !! r = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hg_none_r right_id //. }
      rewrite Hlookup_rg_r Hbf_none_r right_id in Hb.
      inversion Hb; subst dq agree_ks. done.
    + destruct (decide (r0 = g k v)) as [->|Hneq_g].
      * assert (Hlookup_rg_g :
          (mk_frag r 1 (ks ∪ {[k]}) ⋅ mk_frag (g k v) 1 cks) !! (g k v) =
          Some (DfracOwn 1, to_agree cks)).
        { rewrite lookup_op.
          assert (Hr_none_g : mk_frag r 1 (ks ∪ {[k]}) !! (g k v) = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hr_none_g /mk_frag lookup_singleton_eq left_id //. }
        rewrite Hlookup_rg_g Hbf_none_g right_id in Hb.
        inversion Hb; subst dq agree_ks. done.
      * assert (Hlookup_rg_none :
          (mk_frag r 1 (ks ∪ {[k]}) ⋅ mk_frag (g k v) 1 cks) !! r0 = None).
        { rewrite lookup_op.
          assert (Hr_none : mk_frag r 1 (ks ∪ {[k]}) !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          assert (Hg_none : mk_frag (g k v) 1 cks !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hr_none Hg_none left_id //. }
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
        (mk_frag r 1 (ks ∪ {[k]}) ⋅ mk_frag (g k v) 1 cks) !! r =
        Some (DfracOwn 1, to_agree (ks ∪ {[k]}))).
      { rewrite lookup_op /mk_frag lookup_singleton_eq.
        assert (Hg_none_r : mk_frag (g k v) 1 cks !! r = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hg_none_r right_id //. }
      rewrite Hlookup_rg_r Hbf_none_r right_id in Hb.
      inversion Hb; subst dq agree_ks.
      exists (ks ∪ {[k]}). split; [done|].
      assert (Hfins :
        filter (λ '(_, v0), f v0 = Some r) (<[k := v]> (proj_state a)) =
        <[k := v]> (filter (λ '(_, v0), f v0 = Some r) (proj_state a))).
      { apply map_filter_insert_True.
        rewrite Hfr. done.
      }
      rewrite Hfins dom_insert_L Hks_dom union_comm_L //.
    + destruct (decide (r0 = g k v)) as [->|Hneq_g].
      * assert (Hlookup_rg_g :
          (mk_frag r 1 (ks ∪ {[k]}) ⋅ mk_frag (g k v) 1 cks) !! (g k v) =
          Some (DfracOwn 1, to_agree cks)).
        { rewrite lookup_op.
          assert (Hr_none_g : mk_frag r 1 (ks ∪ {[k]}) !! (g k v) = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hr_none_g /mk_frag lookup_singleton_eq left_id //. }
        rewrite Hlookup_rg_g Hbf_none_g right_id in Hb.
        inversion Hb; subst dq agree_ks.
        exists cks. split; [done|].
        assert (Hfins :
          filter (λ '(_, v0), f v0 = Some (g k v)) (<[k := v]> (proj_state a)) =
          filter (λ '(_, v0), f v0 = Some (g k v)) (proj_state a)).
        { apply map_filter_insert_not'.
          - rewrite Hfr. intros Hcontra. inversion Hcontra. subst. done.
          - intros y Hy. rewrite Hak in Hy. done.
        }
        rewrite Hfins Hcks. done.
      * assert (Hlookup_rg_none :
          (mk_frag r 1 (ks ∪ {[k]}) ⋅ mk_frag (g k v) 1 cks) !! r0 = None).
        { rewrite lookup_op.
          assert (Hr_none : mk_frag r 1 (ks ∪ {[k]}) !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          assert (Hg_none : mk_frag (g k v) 1 cks !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hr_none Hg_none left_id //. }
        rewrite Hlookup_rg_none in Hb.
        rewrite left_id in Hb.
        assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some (dq, agree_ks)).
        { rewrite lookup_op.
          assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hnone_old Hb left_id //. }
        destruct (Hchildren _ _ Hlookup_old) as (ks0 & Hagree & Hdom).
        exists ks0. split; [done|].
        assert (Hfins :
          filter (λ '(_, v0), f v0 = Some r0) (<[k := v]> (proj_state a)) =
          filter (λ '(_, v0), f v0 = Some r0) (proj_state a)).
        { apply map_filter_insert_not'.
          - rewrite Hfr. intros Hcontra. inversion Hcontra. subst. done.
          - intros y Hy. rewrite Hak in Hy. done.
        }
        rewrite Hfins. done.
  - intros r0 da Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq_r].
    + set_solver.
    + destruct (decide (r0 = g k v)) as [->|Hneq_g].
      * set_solver.
      * assert (Hlookup_rg_none :
          (mk_frag r 1 (ks ∪ {[k]}) ⋅ mk_frag (g k v) 1 cks) !! r0 = None).
        { rewrite lookup_op.
          assert (Hr_none : mk_frag r 1 (ks ∪ {[k]}) !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          assert (Hg_none : mk_frag (g k v) 1 cks !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hr_none Hg_none left_id //. }
        rewrite Hlookup_rg_none in Hb.
        rewrite left_id in Hb.
        assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some da).
        { rewrite lookup_op.
          assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
          { rewrite /mk_frag lookup_singleton_ne; done. }
          rewrite Hnone_old Hb left_id //. }
        specialize (Hreferences _ _ Hlookup_old). set_solver.
Qed.

Lemma adopt_orphan a k v r ks v':
(proj_state a) !! k = Some v →
f v = None →
f v' = Some r →
g k v = g k v' →
●C a ⋅
◯C (mk_frag r 1 ks) ~~>
  ●C ((<[k := v']> (proj_state a)), (proj_used_reference a)) ⋅
  ◯C (mk_frag r 1 (ks ∪ {[k]})).
Proof.
  intros Hak Hnone Hfr Hg.
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
    apply Hlt. done.
  }
  assert (Hlookup_r_old :
    (mk_frag r 1 ks ⋅ bf) !! r = Some (DfracOwn 1, to_agree ks)).
  { rewrite lookup_op /mk_frag lookup_singleton_eq Hbf_none right_id //. }
  assert (Hks_dom : ks = dom (filter (λ '(_, v0), f v0 = Some r) (proj_state a))).
  { destruct (Hchildren _ _ Hlookup_r_old) as (ks' & Hagree & Hdom).
    assert (Hks_eqv : ks ≡ ks').
    { apply (inj to_agree). by rewrite Hagree. }
    apply leibniz_equiv in Hks_eqv. subst ks'. done.
  }
  assert (Hr_used : r ∈ proj_used_reference a).
  { eapply Hreferences; done. }
  assert (Hdom_transfer :
    ∀ x,
      x ∈ dom (mk_frag r 1 ks ⋅ bf) →
      x ∈ dom (mk_frag r 1 (ks ∪ {[k]}) ⋅ bf)).
  { intros x Hx.
    destruct (decide (x = r)) as [->|Hneq_x].
    - apply elem_of_dom_2 with (x := (DfracOwn 1, to_agree (ks ∪ {[k]}))).
      rewrite lookup_op /mk_frag lookup_singleton_eq Hbf_none right_id //.
    - rewrite elem_of_dom in Hx.
      destruct Hx as [da Hlookup_old].
      assert (Hbf_lookup : bf !! x = Some da).
      { rewrite lookup_op in Hlookup_old.
        assert (Hnone_old : mk_frag r 1 ks !! x = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hnone_old left_id in Hlookup_old. done.
      }
      apply elem_of_dom_2 with (x := da).
      rewrite lookup_op.
      assert (Hnone_new : mk_frag r 1 (ks ∪ {[k]}) !! x = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hnone_new Hbf_lookup left_id //.
  }

  split_and!.
  - rewrite map_Forall_lookup.
    intros k0 v0 Hlookup0.
    simpl in Hlookup0.
    destruct (decide (k0 = k)) as [->|Hneq_k].
    + apply lookup_insert_Some in Hlookup0.
      destruct Hlookup0 as [[_ Hv0]|[Hneq _]].
      * symmetry in Hv0. subst v0.
        rewrite <- Hg.
        exact (map_Forall_lookup_1 _ _ _ _ Hobj Hak).
      * exfalso. apply Hneq. reflexivity.
    + apply lookup_insert_Some in Hlookup0.
      destruct Hlookup0 as [[Heq _]|[_ Hlookup_old]].
      * exfalso. apply Hneq_k. symmetry. exact Heq.
      * exact (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old).
  - intros r0 [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks. done.
    + assert (Hlookup_new : mk_frag r 1 (ks ∪ {[k]}) !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
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
    destruct (decide (r0 = r)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks.
      exists (ks ∪ {[k]}). split; [done|].
      assert (Hfins :
        filter (λ '(_, v0), f v0 = Some r) (<[k := v']> (proj_state a)) =
        <[k := v']> (filter (λ '(_, v0), f v0 = Some r) (proj_state a))).
      { apply map_filter_insert_True.
        rewrite Hfr. done.
      }
      rewrite Hfins dom_insert_L Hks_dom union_comm_L //.
    + assert (Hlookup_new : mk_frag r 1 (ks ∪ {[k]}) !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some (dq, agree_ks)).
      { rewrite lookup_op.
        assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hnone_old Hb left_id //. }
      destruct (Hchildren _ _ Hlookup_old) as (ks0 & Hagree & Hdom).
      exists ks0. split; [done|].
      assert (Hfins :
        filter (λ '(_, v0), f v0 = Some r0) (<[k := v']> (proj_state a)) =
        filter (λ '(_, v0), f v0 = Some r0) (proj_state a)).
      { apply map_filter_insert_not'.
        - rewrite Hfr. intros Hcontra. inversion Hcontra. subst. done.
        - intros y Hy.
          rewrite Hak in Hy. inversion Hy; subst.
          rewrite Hnone. discriminate.
      }
      rewrite Hfins. done.
  - intros r0 da Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + done.
    + rewrite lookup_op in Hb.
      assert (Hlookup_new : mk_frag r 1 (ks ∪ {[k]}) !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some da).
      { rewrite lookup_op.
        assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hnone_old Hb left_id //. }
      eapply Hreferences; done.
Qed.

Lemma release_child a k v r ks v':
(proj_state a) !! k = Some v →
f v = Some r →
f v' = None →
g k v = g k v' →
●C a ⋅
◯C (mk_frag r 1 ks) ~~>
  ●C ((<[k := v']> (proj_state a)), (proj_used_reference a)) ⋅
  ◯C (mk_frag r 1 (ks ∖ {[k]})).
Proof.
  intros Hak Hfr Hnone Hg.
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
  assert (Hlookup_r_old :
    (mk_frag r 1 ks ⋅ bf) !! r = Some (DfracOwn 1, to_agree ks)).
  { rewrite lookup_op /mk_frag lookup_singleton_eq Hbf_none right_id //. }
  assert (Hks_dom : ks = dom (filter (λ '(_, v0), f v0 = Some r) (proj_state a))).
  { destruct (Hchildren _ _ Hlookup_r_old) as (ks' & Hagree & Hdom).
    assert (Hks_eqv : ks ≡ ks').
    { apply (inj to_agree). by rewrite Hagree. }
    apply leibniz_equiv in Hks_eqv. subst ks'. done.
  }
  assert (Hr_used : r ∈ proj_used_reference a).
  { eapply Hreferences; done. }
  assert (Hdom_transfer :
    ∀ x,
      x ∈ dom (mk_frag r 1 ks ⋅ bf) →
      x ∈ dom (mk_frag r 1 (ks ∖ {[k]}) ⋅ bf)).
  { intros x Hx.
    destruct (decide (x = r)) as [->|Hneq_x].
    - apply elem_of_dom_2 with (x := (DfracOwn 1, to_agree (ks ∖ {[k]}))).
      rewrite lookup_op /mk_frag lookup_singleton_eq Hbf_none right_id //.
    - rewrite elem_of_dom in Hx.
      destruct Hx as [da Hlookup_old].
      assert (Hbf_lookup : bf !! x = Some da).
      { rewrite lookup_op in Hlookup_old.
        assert (Hnone_old : mk_frag r 1 ks !! x = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hnone_old left_id in Hlookup_old. done.
      }
      apply elem_of_dom_2 with (x := da).
      rewrite lookup_op.
      assert (Hnone_new : mk_frag r 1 (ks ∖ {[k]}) !! x = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hnone_new Hbf_lookup left_id //.
  }

  repeat split.
  - rewrite map_Forall_lookup.
    intros k0 v0 Hlookup0.
    simpl in Hlookup0.
    destruct (decide (k0 = k)) as [->|Hneq_k].
    + apply lookup_insert_Some in Hlookup0.
      destruct Hlookup0 as [[_ Hv0]|[Hneq _]].
      * symmetry in Hv0. subst v0.
        rewrite <- Hg.
        exact (map_Forall_lookup_1 _ _ _ _ Hobj Hak).
      * exfalso. apply Hneq. reflexivity.
    + apply lookup_insert_Some in Hlookup0.
      destruct Hlookup0 as [[Heq _]|[_ Hlookup_old]].
      * exfalso. apply Hneq_k. symmetry. exact Heq.
      * exact (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old).
  - intros r0 [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks. done.
    + assert (Hlookup_new : mk_frag r 1 (ks ∖ {[k]}) !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
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
    destruct (decide (r0 = r)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks.
      exists (ks ∖ {[k]}). split; [done|].
      assert (Hfins :
        filter (λ '(_, v0), f v0 = Some r) (<[k := v']> (proj_state a)) =
        filter (λ '(_, v0), f v0 = Some r) (delete k (proj_state a))).
      { apply map_filter_insert_False.
        rewrite Hnone. discriminate.
      }
      assert (Hfdel :
        filter (λ '(_, v0), f v0 = Some r) (delete k (proj_state a)) =
        delete k (filter (λ '(_, v0), f v0 = Some r) (proj_state a))).
      { apply map_filter_delete. }
      rewrite Hfins Hfdel dom_delete_L Hks_dom. done.
    + assert (Hlookup_new : mk_frag r 1 (ks ∖ {[k]}) !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some (dq, agree_ks)).
      { rewrite lookup_op.
        assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hnone_old Hb left_id //. }
      destruct (Hchildren _ _ Hlookup_old) as (ks0 & Hagree & Hdom).
      exists ks0. split; [done|].
      assert (Hfins :
        filter (λ '(_, v0), f v0 = Some r0) (<[k := v']> (proj_state a)) =
        filter (λ '(_, v0), f v0 = Some r0) (proj_state a)).
      { apply map_filter_insert_not'.
        - rewrite Hnone. discriminate.
        - intros y Hy.
          rewrite Hak in Hy. inversion Hy; subst.
          rewrite Hfr. intros Hcontra.
          inversion Hcontra. subst. done.
      }
      rewrite Hfins. done.
  - intros r0 da Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + done.
    + rewrite lookup_op in Hb.
      assert (Hlookup_new : mk_frag r 1 (ks ∖ {[k]}) !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some da).
      { rewrite lookup_op.
        assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hnone_old Hb left_id //. }
      eapply Hreferences; done.
Qed.

Lemma delete_child a k v r ks:
(proj_state a) !! k = Some v →
f v = Some r →
●C a ⋅
◯C (mk_frag r 1 ks) ~~>
  ●C ((delete k (proj_state a)), (proj_used_reference a)) ⋅
  ◯C (mk_frag r 1 (ks ∖ {[k]})).
Proof.
  intros Hak Hfr.
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
  assert (Hlookup_r_old :
    (mk_frag r 1 ks ⋅ bf) !! r = Some (DfracOwn 1, to_agree ks)).
  { rewrite lookup_op /mk_frag lookup_singleton_eq Hbf_none right_id //. }
  assert (Hks_dom : ks = dom (filter (λ '(_, v0), f v0 = Some r) (proj_state a))).
  { destruct (Hchildren _ _ Hlookup_r_old) as (ks' & Hagree & Hdom).
    assert (Hks_eqv : ks ≡ ks').
    { apply (inj to_agree). by rewrite Hagree. }
    apply leibniz_equiv in Hks_eqv. subst ks'. done.
  }
  assert (Hr_used : r ∈ proj_used_reference a).
  { eapply Hreferences; done. }
  assert (Hdom_transfer :
    ∀ x,
      x ∈ dom (mk_frag r 1 ks ⋅ bf) →
      x ∈ dom (mk_frag r 1 (ks ∖ {[k]}) ⋅ bf)).
  { intros x Hx.
    destruct (decide (x = r)) as [->|Hneq_x].
    - apply elem_of_dom_2 with (x := (DfracOwn 1, to_agree (ks ∖ {[k]}))).
      rewrite lookup_op /mk_frag lookup_singleton_eq Hbf_none right_id //.
    - rewrite elem_of_dom in Hx.
      destruct Hx as [da Hlookup_old].
      assert (Hbf_lookup : bf !! x = Some da).
      { rewrite lookup_op in Hlookup_old.
        assert (Hnone_old : mk_frag r 1 ks !! x = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hnone_old left_id in Hlookup_old. done.
      }
      apply elem_of_dom_2 with (x := da).
      rewrite lookup_op.
      assert (Hnone_new : mk_frag r 1 (ks ∖ {[k]}) !! x = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hnone_new Hbf_lookup left_id //.
  }

  repeat split.
  - rewrite map_Forall_lookup.
    intros k0 v0 Hlookup0.
    simpl in Hlookup0.
    apply lookup_delete_Some in Hlookup0 as [_ Hlookup_old].
    exact (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old).
  - intros r0 [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks. done.
    + assert (Hlookup_new : mk_frag r 1 (ks ∖ {[k]}) !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
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
    destruct (decide (r0 = r)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks.
      exists (ks ∖ {[k]}). split; [done|].
      assert (Hfdel :
        filter (λ '(_, v0), f v0 = Some r) (delete k (proj_state a)) =
        delete k (filter (λ '(_, v0), f v0 = Some r) (proj_state a))).
      { apply map_filter_delete. }
      rewrite Hfdel dom_delete_L Hks_dom. done.
    + assert (Hlookup_new : mk_frag r 1 (ks ∖ {[k]}) !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some (dq, agree_ks)).
      { rewrite lookup_op.
        assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hnone_old Hb left_id //. }
      destruct (Hchildren _ _ Hlookup_old) as (ks0 & Hagree & Hdom).
      exists ks0. split; [done|].
      assert (Hfdel :
        filter (λ '(_, v0), f v0 = Some r0) (delete k (proj_state a)) =
        filter (λ '(_, v0), f v0 = Some r0) (proj_state a)).
      { change
          ((filter (λ '(_, v0), f v0 = Some r0) (delete k (proj_state a)) : gmap K (leibnizO V)) =
           (filter (λ '(_, v0), f v0 = Some r0) (proj_state a) : gmap K (leibnizO V))).
        refine (@map_filter_delete_not K (gmap K)
          _ _ _ _ _ _ _ _ _ (leibnizO V)
          (λ '(_, v0), f v0 = Some r0) _ (proj_state a) k _).
        intros y Hy.
        rewrite Hak in Hy. inversion Hy; subst.
        rewrite Hfr. intros Hcontra.
        inversion Hcontra. subst. done.
      }
      rewrite Hfdel. done.
  - intros r0 da Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + done.
    + rewrite lookup_op in Hb.
      assert (Hlookup_new : mk_frag r 1 (ks ∖ {[k]}) !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some da).
      { rewrite lookup_op.
        assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hnone_old Hb left_id //. }
      eapply Hreferences; done.
Qed.

Lemma delete_child2 a k r ks:
k ∈ ks →
●C a ⋅
◯C (mk_frag r 1 ks) ~~>
  ●C ((delete k (proj_state a)), (proj_used_reference a)) ⋅
  ◯C (mk_frag r 1 (ks ∖ {[k]})).
Proof.
  intros Hk.
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
  assert (Hlookup_r_old :
    (mk_frag r 1 ks ⋅ bf) !! r = Some (DfracOwn 1, to_agree ks)).
  { rewrite lookup_op /mk_frag lookup_singleton_eq Hbf_none right_id //. }
  assert (Hks_dom : ks = dom (filter (λ '(_, v0), f v0 = Some r) (proj_state a))).
  { destruct (Hchildren _ _ Hlookup_r_old) as (ks' & Hagree & Hdom).
    assert (Hks_eqv : ks ≡ ks').
    { apply (inj to_agree). by rewrite Hagree. }
    apply leibniz_equiv in Hks_eqv. subst ks'. done.
  }
  assert (Hr_used : r ∈ proj_used_reference a).
  { eapply Hreferences; done. }
  assert (Hk_in_dom : k ∈ dom (filter (λ '(_, v0), f v0 = Some r) (proj_state a))).
  { rewrite -Hks_dom. done. }
  apply elem_of_dom in Hk_in_dom as [vk Hk_lookup].
  apply map_lookup_filter_Some in Hk_lookup as [Hak Hfkr].
  assert (Hdom_transfer :
    ∀ x,
      x ∈ dom (mk_frag r 1 ks ⋅ bf) →
      x ∈ dom (mk_frag r 1 (ks ∖ {[k]}) ⋅ bf)).
  { intros x Hx.
    destruct (decide (x = r)) as [->|Hneq_x].
    - apply elem_of_dom_2 with (x := (DfracOwn 1, to_agree (ks ∖ {[k]}))).
      rewrite lookup_op /mk_frag lookup_singleton_eq Hbf_none right_id //.
    - rewrite elem_of_dom in Hx.
      destruct Hx as [da Hlookup_old].
      assert (Hbf_lookup : bf !! x = Some da).
      { rewrite lookup_op in Hlookup_old.
        assert (Hnone_old : mk_frag r 1 ks !! x = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hnone_old left_id in Hlookup_old. done.
      }
      apply elem_of_dom_2 with (x := da).
      rewrite lookup_op.
      assert (Hnone_new : mk_frag r 1 (ks ∖ {[k]}) !! x = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hnone_new Hbf_lookup left_id //.
  }

  repeat split.
  - rewrite map_Forall_lookup.
    intros k0 v0 Hlookup0.
    simpl in Hlookup0.
    apply lookup_delete_Some in Hlookup0 as [_ Hlookup_old].
    exact (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old).
  - intros r0 [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks. done.
    + assert (Hlookup_new : mk_frag r 1 (ks ∖ {[k]}) !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
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
    destruct (decide (r0 = r)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks.
      exists (ks ∖ {[k]}). split; [done|].
      assert (Hfdel :
        filter (λ '(_, v0), f v0 = Some r) (delete k (proj_state a)) =
        delete k (filter (λ '(_, v0), f v0 = Some r) (proj_state a))).
      { apply map_filter_delete. }
      rewrite Hfdel dom_delete_L Hks_dom. done.
    + assert (Hlookup_new : mk_frag r 1 (ks ∖ {[k]}) !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some (dq, agree_ks)).
      { rewrite lookup_op.
        assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hnone_old Hb left_id //. }
      destruct (Hchildren _ _ Hlookup_old) as (ks0 & Hagree & Hdom).
      exists ks0. split; [done|].
      assert (Hfdel :
        filter (λ '(_, v0), f v0 = Some r0) (delete k (proj_state a)) =
        filter (λ '(_, v0), f v0 = Some r0) (proj_state a)).
      { change
          ((filter (λ '(_, v0), f v0 = Some r0) (delete k (proj_state a)) : gmap K (leibnizO V)) =
           (filter (λ '(_, v0), f v0 = Some r0) (proj_state a) : gmap K (leibnizO V))).
        refine (@map_filter_delete_not K (gmap K)
          _ _ _ _ _ _ _ _ _ (leibnizO V)
          (λ '(_, v0), f v0 = Some r0) _ (proj_state a) k _).
        intros y Hy.
        rewrite Hak in Hy. inversion Hy; subst.
        rewrite Hfkr. intros Hcontra.
        inversion Hcontra. subst. done.
      }
      rewrite Hfdel. done.
  - intros r0 da Hb.
    destruct (decide (r0 = r)) as [->|Hneq].
    + done.
    + rewrite lookup_op in Hb.
      assert (Hlookup_new : mk_frag r 1 (ks ∖ {[k]}) !! r0 = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      assert (Hlookup_old : (mk_frag r 1 ks ⋅ bf) !! r0 = Some da).
      { rewrite lookup_op.
        assert (Hnone_old : mk_frag r 1 ks !! r0 = None).
        { rewrite /mk_frag lookup_singleton_ne; done. }
        rewrite Hnone_old Hb left_id //. }
      eapply Hreferences; done.
Qed.

Lemma simple_update a k v v':
(proj_state a) !! k = Some v →
f v = f v' →
g k v = g k v' →
●C a ~~> ●C ((<[k := v']> (proj_state a)), (proj_used_reference a)).
Proof.
  intros Hak Hfv Hg.
  apply view_update_auth.
  intros n bf [Hobj [Hvalid [Hchildren Hreferences]]].
  repeat split.
  - rewrite map_Forall_lookup.
    intros k0 v0 Hlookup0.
    simpl in Hlookup0.
    destruct (decide (k0 = k)) as [->|Hneq_k].
    + apply lookup_insert_Some in Hlookup0.
      destruct Hlookup0 as [[_ Hv0]|[Hneq _]].
      * symmetry in Hv0. subst v0.
        rewrite <- Hg.
        exact (map_Forall_lookup_1 _ _ _ _ Hobj Hak).
      * exfalso. apply Hneq. reflexivity.
    + apply lookup_insert_Some in Hlookup0.
      destruct Hlookup0 as [[Heq _]|[_ Hlookup_old]].
      * exfalso. apply Hneq_k. symmetry. exact Heq.
      * exact (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old).
  - done.
  - intros r [dq agree_ks] Hb.
    destruct (Hchildren _ _ Hb) as (ks & Hagree & Hks).
    exists ks. split; [exact Hagree|].
    set (P := λ kv : K * V, f kv.2 = Some r).
    assert (Hdom :
      dom (filter P (<[k := v']> (proj_state a))) =
      dom (filter P (proj_state a))).
    { destruct (decide (P (k, v'))) as [HPv'|HPv'].
      - assert (Hins :
          filter P (<[k := v']> (proj_state a)) =
          <[k := v']> (filter P (proj_state a))).
        { apply (map_filter_insert_True P (proj_state a) k v'). done. }
        rewrite Hins.
        assert (HPv : P (k, v)).
        { unfold P in *. rewrite Hfv. done. }
        apply dom_insert_lookup_L.
        eexists. apply map_lookup_filter_Some. split; [done|done].
      - assert (Hins :
          filter P (<[k := v']> (proj_state a)) =
          filter P (proj_state a)).
        { apply (map_filter_insert_not' P (proj_state a) k v').
          - done.
          - intros y Hy.
            rewrite Hak in Hy. inversion Hy; subst.
            unfold P in *. rewrite Hfv. done.
        }
        rewrite Hins. done.
    }
    rewrite /P in Hdom.
    rewrite Hdom. done.
  - intros r da Hb.
    eapply Hreferences; done.
Qed.

Lemma create_orphan a k v cks:
(proj_state a) !! k = None →
f v = None →
dom (filter (λ '(_, v'), f v' = Some (g k v)) (proj_state a)) = cks →
g k v ∉ (proj_used_reference a) →
●C a ~~>
  ●C ((<[k := v]> (proj_state a)), ((proj_used_reference a) ∪ {[g k v]})) ⋅
  ◯C (mk_frag (g k v) 1 cks).
Proof.
  intros Hak Hnone Hcks Hfresh.
  apply view_update_alloc.
  intros n bf [Hobj [Hvalid [Hchildren Hreferences]]].
  assert (Hbf_none : bf !! (g k v) = None).
  { destruct (bf !! (g k v)) as [da|] eqn:Hbf; [|done].
    exfalso. apply Hfresh. eapply Hreferences; done.
  }
  assert (Hfilter :
    ∀ r,
      filter (λ '(_, v'), f v' = Some r) (<[k := v]> (proj_state a)) =
      filter (λ '(_, v'), f v' = Some r) (proj_state a)).
  { intros r.
    change
      ((filter (λ '(_, v'), f v' = Some r) (<[k := v]> (proj_state a)) : gmap K (leibnizO V)) =
       (filter (λ '(_, v'), f v' = Some r) (proj_state a) : gmap K (leibnizO V))).
    refine (@map_filter_insert_not' K (gmap K)
      _ _ _ _ _ _ _ _ _ (leibnizO V)
      (λ '(_, v'), f v' = Some r) _ (proj_state a) k v _ _).
    - rewrite Hnone. discriminate.
    - intros y Hy. rewrite Hak in Hy. done.
  }
  assert (Hdom_transfer :
    ∀ x, x ∈ dom bf → x ∈ dom (mk_frag (g k v) 1 cks ⋅ bf)).
  { intros x Hx.
    destruct (decide (x = g k v)) as [->|Hneq_x].
    - apply elem_of_dom_2 with (x := (DfracOwn 1, to_agree cks)).
      rewrite lookup_op /mk_frag lookup_singleton_eq Hbf_none right_id //.
    - rewrite elem_of_dom in Hx.
      destruct Hx as [da Hlookup_bf].
      apply elem_of_dom_2 with (x := da).
      rewrite lookup_op.
      assert (Hnone_new : mk_frag (g k v) 1 cks !! x = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hnone_new Hlookup_bf left_id //.
  }
  repeat split.
  - rewrite map_Forall_lookup.
    intros k0 v0 Hlookup0.
    simpl in Hlookup0.
    destruct (decide (k0 = k)) as [->|Hneq_k].
    + apply lookup_insert_Some in Hlookup0.
      destruct Hlookup0 as [[_ Hv0]|[Hneq _]].
      * symmetry in Hv0. subst v0.
        apply elem_of_union. right.
        apply elem_of_singleton. reflexivity.
      * exfalso. apply Hneq. reflexivity.
    + apply lookup_insert_Some in Hlookup0.
      destruct Hlookup0 as [[Heq _]|[_ Hlookup_old]].
      * exfalso. apply Hneq_k. symmetry. exact Heq.
      * pose proof (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old) as Hobj_used.
        apply elem_of_union. left. exact Hobj_used.
  - intros r [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r = g k v)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks. done.
    + rewrite /mk_frag in Hb.
      assert (Hlookup_new : mk_frag (g k v) 1 cks !! r = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      specialize (Hvalid _ _ Hb). done.
  - intros r [dq agree_ks] Hb.
    rewrite lookup_op in Hb.
    destruct (decide (r = g k v)) as [->|Hneq].
    + rewrite /mk_frag lookup_singleton_eq Hbf_none right_id in Hb.
      inversion Hb; subst dq agree_ks.
      exists cks. split; [done|].
      rewrite (Hfilter (g k v)). done.
    + rewrite /mk_frag in Hb.
      assert (Hlookup_new : mk_frag (g k v) 1 cks !! r = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      destruct (Hchildren _ _ Hb) as (ks & Hagree & Hdom).
      exists ks. split; [done|].
      rewrite (Hfilter r). done.
  - intros r da Hb.
    destruct (decide (r = g k v)) as [->|Hneq].
    + set_solver.
    + rewrite lookup_op in Hb.
      assert (Hlookup_new : mk_frag (g k v) 1 cks !! r = None).
      { rewrite /mk_frag lookup_singleton_ne; done. }
      rewrite Hlookup_new in Hb.
      rewrite left_id in Hb.
      specialize (Hreferences _ _ Hb). set_solver.
Qed.

Lemma delete_orphan a k v:
(proj_state a) !! k = Some v →
f v = None →
●C a ~~> ●C ((delete k (proj_state a)), (proj_used_reference a)).
Proof.
  intros Hak Hnone.
  apply view_update_auth.
  intros n bf [Hobj [Hvalid [Hchildren Hreferences]]].
  repeat split.
  - rewrite map_Forall_lookup.
    intros k0 v0 Hlookup0.
    simpl in Hlookup0.
    apply lookup_delete_Some in Hlookup0 as [_ Hlookup_old].
    exact (map_Forall_lookup_1 _ _ _ _ Hobj Hlookup_old).
  - done.
  - intros r [dq agree_ks] Hb.
    destruct (Hchildren _ _ Hb) as (ks & Hagree & Hks).
    exists ks. split; [exact Hagree|].
    assert (Hfilter :
      filter (λ '(_, v'), f v' = Some r) (delete k (proj_state a)) =
      filter (λ '(_, v'), f v' = Some r) (proj_state a)).
    { change
        ((filter (λ '(_, v'), f v' = Some r) (delete k (proj_state a)) : gmap K (leibnizO V)) =
         (filter (λ '(_, v'), f v' = Some r) (proj_state a) : gmap K (leibnizO V))).
      refine (@map_filter_delete_not K (gmap K)
        _ _ _ _ _ _ _ _ _ (leibnizO V)
        (λ '(_, v'), f v' = Some r) _ (proj_state a) k _).
      intros y Hy.
      rewrite Hak in Hy. inversion Hy; subst.
      rewrite Hnone. discriminate.
    }
    rewrite Hfilter. done.
  - intros r da Hb.
    eapply Hreferences; done.
Qed.

Class reversed_referenceG Σ :=
  { #[global] reversed_reference_inG :: inG Σ (viewR view_rel); }.

Definition reversed_referenceΣ :=
  #[GFunctor (viewR view_rel)].

#[global]
Instance subG_reversed_referenceG Σ :
  subG reversed_referenceΣ Σ → reversed_referenceG Σ.
Proof. solve_inG. Qed.

Context `{!reversed_referenceG Σ}.

Global Instance own_auth_timeless γ a : Timeless (own γ (●C a)).
Proof. apply _. Qed.

Global Instance own_frag_timeless γ b : Timeless (own γ (◯C b)).
Proof. apply _. Qed.

Definition own_auth γ (state: gmap K V) (used_reference: gset R) : iProp Σ :=
  own γ (●C (state, used_reference)).

Definition own_frag γ r dq ks : iProp Σ :=
  own γ (◯C (mk_frag r dq ks)).

Lemma own_auth_frag_valid {γ state used_reference r dq ks}:
own_auth γ state used_reference -∗
own_frag γ r dq ks -∗
⌜ ks = dom (filter (λ '(_, v), f v = Some r) state) ⌝ ∗
⌜ r ∈ used_reference ⌝.
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_valid_2 with "Hauth Hfrag") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  rewrite /own_auth /own_frag in Hvalid0.
  pose proof (proj1 (view_both_validN view_rel 0%nat
    (state, used_reference) (mk_frag r dq ks)) Hvalid0) as Hrel0.
  assert (Hvalid : ✓ (●C (state, used_reference) ⋅ ◯C (mk_frag r dq ks))).
  { rewrite /cview_auth /cview_frag.
    apply (proj2 (view_both_valid view_rel (state, used_reference) (mk_frag r dq ks))).
    intros n. exact Hrel0.
  }
  pose proof (auth_frag_valid (state, used_reference) r dq ks Hvalid) as [Hks Hr].
  split; done.
Qed.

Lemma create_child_vs {γ state used_reference r ks} k v cks:
state !! k = None →
f v = Some r →
g k v ≠ r → (* No self-parenting *)
dom (filter (λ '(_, v'), f v' = Some (g k v)) state) = cks →
g k v ∉ used_reference →
own_auth γ state used_reference -∗
own_frag γ r 1 ks ==∗
  own_auth γ (<[k := v]> state) (used_reference ∪ {[g k v]}) ∗
  own_frag γ r 1 (ks ∪ {[k]}) ∗
  own_frag γ (g k v) 1 cks.
Proof.
  iIntros (Hak Hfr Hnself Hcks Hfresh) "Hauth Hfrag".
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { eapply create_child; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[H Hfrag2]".
  iDestruct (own_op with "H") as "[Hauth Hfrag1]".
  iFrame.
Qed.

Lemma adopt_orphan_vs {γ state used_reference r ks} k v v':
state !! k = Some v →
f v = None →
f v' = Some r →
g k v = g k v' →
own_auth γ state used_reference -∗ own_frag γ r 1 ks ==∗
  own_auth γ (<[k := v']> state) used_reference ∗ own_frag γ r 1 (ks ∪ {[k]}).
Proof.
  iIntros (Hak Hnone Hfr Hg) "Hauth Hfrag".
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { eapply adopt_orphan; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[Hauth Hfrag]".
  iFrame.
Qed.

Lemma release_child_vs {γ state used_reference r ks} k v v':
state !! k = Some v →
f v = Some r →
f v' = None →
g k v = g k v' →
own_auth γ state used_reference -∗ own_frag γ r 1 ks ==∗
  own_auth γ (<[k := v']> state) used_reference ∗ own_frag γ r 1 (ks ∖ {[k]}).
Proof.
  iIntros (Hak Hfr Hnone Hg) "Hauth Hfrag".
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { eapply release_child; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[Hauth Hfrag]".
  iFrame.
Qed.

Lemma delete_child_vs {γ state used_reference r ks} k v:
state !! k = Some v →
f v = Some r →
own_auth γ state used_reference -∗ own_frag γ r 1 ks ==∗
  own_auth γ (delete k state) used_reference ∗ own_frag γ r 1 (ks ∖ {[k]}).
Proof.
  iIntros (Hak Hfr) "Hauth Hfrag".
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { eapply delete_child; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[Hauth Hfrag]".
  iFrame.
Qed.

Lemma delete_child_vs2 {γ state used_reference r ks} k:
k ∈ ks →
own_auth γ state used_reference -∗ own_frag γ r 1 ks ==∗
  own_auth γ (delete k state) used_reference ∗ own_frag γ r 1 (ks ∖ {[k]}).
Proof.
  iIntros (Hk) "Hauth Hfrag".
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { eapply delete_child2; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[Hauth Hfrag]".
  iFrame.
Qed.

Lemma simple_update_vs {γ state used_reference} k v v':
state !! k = Some v →
f v = f v' →
g k v = g k v' →
own_auth γ state used_reference ==∗ own_auth γ (<[k := v']> state) used_reference.
Proof.
  iIntros (Hak Hf Hg) "Hauth".
  iMod (own_update with "Hauth") as "Hauth".
  { eapply simple_update; done. }
  iModIntro. iExact "Hauth".
Qed.

Lemma create_orphan_vs {γ state used_reference} k v cks:
state !! k = None →
f v = None →
dom (filter (λ '(_, v'), f v' = Some (g k v)) state) = cks →
g k v ∉ used_reference →
own_auth γ state used_reference ==∗
  own_auth γ (<[k := v]> state) (used_reference ∪ {[g k v]}) ∗
  own_frag γ (g k v) 1 cks.
Proof.
  iIntros (Hak Hnone Hcks Hfresh) "Hauth".
  iMod (own_update with "Hauth") as "H".
  { eapply create_orphan; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[Hauth Hfrag]".
  iFrame.
Qed.

Lemma delete_orphan_vs {γ state used_reference} k v:
state !! k = Some v →
f v = None →
own_auth γ state used_reference ==∗ own_auth γ (delete k state) used_reference.
Proof.
  iIntros (Hak Hnone) "Hauth".
  iMod (own_update with "Hauth") as "Hauth".
  { eapply delete_orphan; done. }
  iModIntro. iExact "Hauth".
Qed.

End reversed_reference.
