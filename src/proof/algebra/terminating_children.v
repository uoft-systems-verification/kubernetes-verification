From New.proof Require Import prelude.
From New.proof.kubernetes_types Require Export prelude.
From iris.algebra Require Import cmra gmap.
From iris.base_logic.lib Require Import own.

Section terminating_children.

Inductive phase :=
  | Quiescent
  | Mutable.

#[global] Instance phase_eq_decision : EqDecision phase.
Proof. solve_decision. Defined.

Lemma mutable_ne_quiescent : Mutable ≠ Quiescent.
Proof. intros H. inversion H. Qed.

Definition parent := (KKey.t * types.UID.t)%type.

Definition terminating_obj_parent_ref
    (obj : KObjectV.t) : option parent :=
  match (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') with
  | None => None
  | Some _ => obj_parent_ref obj
  end.

Lemma terminating_obj_parent_ref_eq_some obj p :
  terminating_obj_parent_ref obj = Some p ↔
    (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') ≠ None ∧
    obj_parent_ref obj = Some p.
Proof.
  unfold terminating_obj_parent_ref.
  destruct ((KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp'))
    as [timestamp|] eqn:Htimestamp.
  - split.
    + intros Hparent. split; [discriminate|exact Hparent].
    + intros [_ Hparent]. exact Hparent.
  - split.
    + discriminate.
    + intros [Htimestamp_ne _]. exfalso. apply Htimestamp_ne. reflexivity.
Qed.

Definition terminating_children
    (state : gmap KKey.t KObjectV.t) (p : parent) : gset KKey.t :=
  dom (filter (λ '(_, obj), terminating_obj_parent_ref obj = Some p) state).

Lemma terminating_children_insert_none state key obj p :
  state !! key = None →
  terminating_obj_parent_ref obj = None →
  terminating_children (<[key := obj]> state) p =
    terminating_children state p.
Proof.
  intros Habsent Hparent.
  apply leibniz_equiv.
  apply set_equiv. intros child_key.
  unfold terminating_children.
  rewrite !elem_of_dom.
  split.
  - intros [child_obj Hlookup].
    apply map_lookup_filter_Some in Hlookup as
      [Hlookup Hchild_parent].
    destruct (decide (child_key = key)) as [->|Hneq].
    + rewrite lookup_insert_eq in Hlookup.
      injection Hlookup as <-.
      rewrite Hparent in Hchild_parent. done.
    + rewrite lookup_insert_ne // in Hlookup.
      exists child_obj.
      apply map_lookup_filter_Some. split; done.
  - intros [child_obj Hlookup].
    apply map_lookup_filter_Some in Hlookup as
      [Hlookup Hchild_parent].
    assert (child_key ≠ key) as Hneq.
    { intros ->. rewrite Habsent in Hlookup. done. }
    exists child_obj.
    apply map_lookup_filter_Some. split; last done.
    rewrite lookup_insert_ne //.
Qed.

Lemma terminating_children_update_same state key old_obj new_obj p :
  state !! key = Some old_obj →
  terminating_obj_parent_ref old_obj =
    terminating_obj_parent_ref new_obj →
  terminating_children (<[key := new_obj]> state) p =
    terminating_children state p.
Proof.
  intros Hlookup Hparent.
  apply leibniz_equiv.
  apply set_equiv. intros child_key.
  unfold terminating_children.
  rewrite !elem_of_dom.
  split.
  - intros [child_obj Hchild].
    apply map_lookup_filter_Some in Hchild as
      [Hchild_lookup Hchild_parent].
    destruct (decide (child_key = key)) as [->|Hneq].
    + rewrite lookup_insert_eq in Hchild_lookup.
      injection Hchild_lookup as <-.
      exists old_obj.
      apply map_lookup_filter_Some. split; first done.
      rewrite Hparent. done.
    + exists child_obj.
      apply map_lookup_filter_Some. split; last done.
      rewrite lookup_insert_ne // in Hchild_lookup.
  - intros [child_obj Hchild].
    apply map_lookup_filter_Some in Hchild as
      [Hchild_lookup Hchild_parent].
    destruct (decide (child_key = key)) as [->|Hneq].
    + rewrite Hlookup in Hchild_lookup. injection Hchild_lookup as <-.
      exists new_obj.
      apply map_lookup_filter_Some. split.
      * rewrite lookup_insert_eq //.
      * rewrite -Hparent. done.
    + exists child_obj.
      apply map_lookup_filter_Some. split; last done.
      rewrite lookup_insert_ne //.
Qed.

Lemma terminating_children_update_remove_parent state key old_obj new_obj p :
  state !! key = Some old_obj →
  terminating_obj_parent_ref new_obj = None →
  terminating_children (<[key := new_obj]> state) p ⊆
    terminating_children state p.
Proof.
  intros Hlookup Hnew child_key Hchild.
  unfold terminating_children in Hchild |- *.
  apply elem_of_dom in Hchild as [child_obj Hchild].
  apply map_lookup_filter_Some in Hchild as
    [Hchild_lookup Hchild_parent].
  destruct (decide (child_key = key)) as [->|Hneq].
  - rewrite lookup_insert_eq in Hchild_lookup.
    injection Hchild_lookup as <-.
    rewrite Hnew in Hchild_parent. done.
  - apply elem_of_dom. exists child_obj.
    apply map_lookup_filter_Some. split; last done.
    rewrite lookup_insert_ne // in Hchild_lookup.
Qed.

Lemma terminating_children_delete_subset state key p :
  terminating_children (delete key state) p ⊆
    terminating_children state p.
Proof.
  intros child_key Hchild.
  unfold terminating_children in Hchild |- *.
  apply elem_of_dom in Hchild as [obj Hlookup].
  apply map_lookup_filter_Some in Hlookup as
    [Hlookup Hparent].
  apply lookup_delete_Some in Hlookup as [_ Hlookup].
  apply elem_of_dom. exists obj.
  apply map_lookup_filter_Some. split; done.
Qed.

Definition authO : ofe := leibnizO (gmap KKey.t KObjectV.t).
Definition fragUR : ucmra :=
  gmapUR parent (prodR dfracR (agreeR (leibnizO phase))).

Implicit Types (a : authO) (b : fragUR).

Lemma terminating_children_update_other_parent state key old_obj new_obj
    introduced_parent p :
  state !! key = Some old_obj →
  terminating_obj_parent_ref old_obj = None →
  terminating_obj_parent_ref new_obj = Some introduced_parent →
  p ≠ introduced_parent →
  terminating_children (<[key := new_obj]> state) p =
    terminating_children state p.
Proof.
  intros Hlookup Hold Hnew Hneq.
  apply leibniz_equiv.
  apply set_equiv. intros child_key.
  unfold terminating_children.
  rewrite !elem_of_dom.
  split.
  - intros [child_obj Hchild].
    apply map_lookup_filter_Some in Hchild as
      [Hchild_lookup Hchild_parent].
    destruct (decide (child_key = key)) as [->|Hchild_ne].
    + rewrite lookup_insert_eq in Hchild_lookup.
      injection Hchild_lookup as <-.
      rewrite Hnew in Hchild_parent.
      injection Hchild_parent as Heq.
      exfalso. apply Hneq. symmetry. exact Heq.
    + exists child_obj. apply map_lookup_filter_Some. split; last done.
      rewrite lookup_insert_ne // in Hchild_lookup.
  - intros [child_obj Hchild].
    apply map_lookup_filter_Some in Hchild as
      [Hchild_lookup Hchild_parent].
    assert (child_key ≠ key) as Hchild_ne.
    { intros ->. rewrite Hlookup in Hchild_lookup.
      injection Hchild_lookup as <-.
      rewrite Hold in Hchild_parent. done. }
    exists child_obj. apply map_lookup_filter_Some. split; last done.
    rewrite lookup_insert_ne //.
Qed.

Local Definition compatible
    (b : fragUR) (a : gmap KKey.t KObjectV.t) : Prop :=
  map_Forall (λ p '(dq, agree_phase),
    ∃ control_phase,
      agree_phase ≡ to_agree (A := leibnizO phase) control_phase ∧
      ✓ dq ∧
      (control_phase = Quiescent →
        terminating_children a p = ∅)) b.

Local Definition view_rel_raw (_ : nat) a b : Prop :=
  compatible b a.

Local Lemma view_rel_raw_mono n1 n2 a1 a2 b1 b2 :
  view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  (n2 ≤ n1)%nat →
  view_rel_raw n2 a2 b2.
Proof.
  intros Hcompatible Ha Hb _.
  assert (a1 = a2) as ->.
  { apply leibniz_equiv.
    apply (proj2 (discrete_iff n2 a1 a2)).
    exact Ha. }
  rewrite /view_rel_raw /compatible map_Forall_lookup in Hcompatible |- *.
  intros p [dq2 agree2] Hlookup2.
  destruct (lookup_includedN n2 b2 b1) as [Hlookup_incl _].
  specialize (Hlookup_incl Hb p).
  rewrite Hlookup2 in Hlookup_incl.
  destruct (Some_includedN_is_Some _ _ _ Hlookup_incl) as
    [[dq1 agree1] Hlookup1].
  destruct (Hcompatible _ _ Hlookup1) as
    (control_phase & Hagree1 & Hvdq1 & Hquiescent).
  rewrite Hlookup1 in Hlookup_incl.
  assert (Hvalid1 :
    ✓{n2} (Some (dq1, agree1) :
      option (dfrac * agree (leibnizO phase)))).
  { simpl. apply cmra_valid_validN.
    apply pair_valid. split.
    - apply cmra_valid_validN. done.
    - rewrite Hagree1. done. }
  assert (Hvalid2 :
    ✓{n2} (Some (dq2, agree2) :
      option (dfrac * agree (leibnizO phase)))).
  { eapply cmra_validN_includedN; done. }
  assert (Hvdq2 : ✓ dq2).
  { apply (proj2 (cmra_discrete_valid_iff n2 dq2)).
    apply (proj1 (pair_validN dq2 agree2 n2)).
    simpl in Hvalid2. done. }
  pose proof (Some_pair_includedN _ _ _ _ _ Hlookup_incl) as
    [_ Hagree_opt_incl].
  pose proof (proj1 (Some_includedN_total n2 agree2 agree1)
    Hagree_opt_incl) as Hagree_incl.
  assert (Hagree1_valid : ✓{n2} agree1).
  { rewrite Hagree1. done. }
  pose proof (agree_valid_includedN n2 agree2 agree1
    Hagree1_valid Hagree_incl) as Hagree2.
  exists control_phase. split_and!; try done.
  apply (proj2 (discrete_iff n2 agree2
    (to_agree (A := leibnizO phase) control_phase))).
  etrans; [exact Hagree2|exact (Hagree1 n2)].
Qed.

Local Lemma view_rel_raw_valid n a b :
  view_rel_raw n a b → ✓{n} b.
Proof.
  intros Hcompatible p.
  destruct (b !! p) as [[dq agree_phase]|] eqn:Hlookup.
  - destruct (Hcompatible _ _ Hlookup) as
      (control_phase & Hagree & Hvdq & _).
    rewrite Hlookup.
    apply pair_validN. split.
    + apply cmra_valid_validN. done.
    + rewrite Hagree. done.
  - rewrite Hlookup. done.
Qed.

Local Lemma view_rel_raw_unit n :
  ∃ a, view_rel_raw n a ε.
Proof.
  exists (∅ : gmap KKey.t KObjectV.t).
  rewrite /view_rel_raw /compatible map_Forall_lookup.
  intros p x Hlookup.
  rewrite lookup_empty in Hlookup. done.
Qed.

Local Canonical Structure control_view_rel : view_rel authO fragUR :=
  ViewRel view_rel_raw view_rel_raw_mono
    view_rel_raw_valid view_rel_raw_unit.

Definition control_auth dq a : viewR control_view_rel := ●V{dq} a.
Definition control_frag b : viewR control_view_rel := ◯V b.

Definition mk_frag (p : parent) (control_phase : phase) : fragUR :=
  {[p := (DfracOwn 1,
    to_agree (A := leibnizO phase) control_phase)]}.

Class terminatingChildrenG Σ := {
  #[global] terminating_children_inG ::
    inG Σ (viewR control_view_rel);
}.

Definition terminatingChildrenΣ := #[GFunctor (viewR control_view_rel)].

#[global]
Instance subG_terminatingChildrenG Σ :
  subG terminatingChildrenΣ Σ → terminatingChildrenG Σ.
Proof. solve_inG. Qed.

Context {Σ : gFunctors}.
Context {Hcontrol : terminatingChildrenG Σ}.
#[local] Existing Instance Hcontrol.

Definition own_auth γ state : iProp Σ :=
  own γ (control_auth 1 state).

Definition own_frag γ key uid control_phase : iProp Σ :=
  own γ (control_frag (mk_frag (key, uid) control_phase)).

Global Instance own_auth_timeless γ state :
  Timeless (own_auth γ state).
Proof. apply _. Qed.

Global Instance own_frag_timeless γ key uid control_phase :
  Timeless (own_frag γ key uid control_phase).
Proof. apply _. Qed.

Lemma init :
  ⊢ |==> ∃ γ,
    own_auth γ (∅ : gmap KKey.t KObjectV.t).
Proof.
  unfold own_auth.
  iMod (own_alloc (control_auth 1
    (∅ : gmap KKey.t KObjectV.t))) as (γ) "Hauth".
  { apply (proj2 (view_auth_dfrac_valid control_view_rel 1
      (∅ : gmap KKey.t KObjectV.t))).
    split; [done|].
    intros n.
    change (view_rel_raw n (∅ : gmap KKey.t KObjectV.t) ε).
    rewrite /view_rel_raw /compatible map_Forall_lookup.
    intros p x Hlookup. rewrite lookup_empty in Hlookup. done. }
  iModIntro. iExists γ. iExact "Hauth".
Qed.

Lemma own_auth_frag_valid {γ state key uid control_phase} :
  own_auth γ state -∗
  own_frag γ key uid control_phase -∗
  ⌜ control_phase = Quiescent →
    terminating_children state (key, uid) = ∅ ⌝.
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_valid_2 with "Hauth Hfrag") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid.
  iPureIntro.
  apply (proj1 (view_both_validN control_view_rel 0%nat
    state (mk_frag (key, uid) control_phase)))
    in Hvalid.
  change (view_rel_raw 0%nat state
    (mk_frag (key, uid) control_phase)) in Hvalid.
  assert (Hlookup :
    mk_frag (key, uid) control_phase !! (key, uid) =
      Some (DfracOwn 1,
        to_agree (A := leibnizO phase) control_phase)).
  { rewrite /mk_frag lookup_singleton_eq //. }
  destruct (Hvalid _ _ Hlookup) as
    (control_phase' & Hagree & _ & Hquiescent).
  assert (Hphase_eqv :
    (control_phase : leibnizO phase) ≡ control_phase').
  { apply (inj (to_agree :
      leibnizO phase → agree (leibnizO phase))).
    exact Hagree. }
  apply leibniz_equiv in Hphase_eqv.
  subst control_phase'.
  exact Hquiescent.
Qed.

Lemma create_living state key obj :
  state !! key = None →
  terminating_obj_parent_ref obj = None →
  control_auth 1 state ~~>
    control_auth 1 (<[key := obj]> state).
Proof.
  intros Habsent Hparent.
  apply view_update_auth.
  intros n b Hcompatible.
  change (compatible b state) in Hcompatible.
  change (compatible b (<[key := obj]> state)).
  rewrite /compatible map_Forall_lookup in Hcompatible |- *.
  intros p [dq agree_phase] Hlookup.
  destruct (Hcompatible _ _ Hlookup) as
    (control_phase & Hagree & Hvdq & Hquiescent).
  exists control_phase. split_and!; try done.
  intros ->. rewrite terminating_children_insert_none //.
  exact (Hquiescent eq_refl).
Qed.

Lemma update_same_parent state key old_obj new_obj :
  state !! key = Some old_obj →
  terminating_obj_parent_ref old_obj =
    terminating_obj_parent_ref new_obj →
  control_auth 1 state ~~>
    control_auth 1 (<[key := new_obj]> state).
Proof.
  intros Hlookup Hparent.
  apply view_update_auth.
  intros n b Hcompatible.
  change (compatible b state) in Hcompatible.
  change (compatible b (<[key := new_obj]> state)).
  rewrite /compatible map_Forall_lookup in Hcompatible |- *.
  intros p [dq agree_phase] Hfrag.
  destruct (Hcompatible _ _ Hfrag) as
    (control_phase & Hagree & Hvdq & Hquiescent).
  exists control_phase. split_and!; try done.
  intros ->.
  rewrite (terminating_children_update_same
    state key old_obj new_obj p Hlookup Hparent).
  exact (Hquiescent eq_refl).
Qed.

Lemma update_remove_parent state key old_obj new_obj :
  state !! key = Some old_obj →
  terminating_obj_parent_ref new_obj = None →
  control_auth 1 state ~~>
    control_auth 1 (<[key := new_obj]> state).
Proof.
  intros Hlookup Hnew.
  apply view_update_auth.
  intros n b Hcompatible.
  change (compatible b state) in Hcompatible.
  change (compatible b (<[key := new_obj]> state)).
  rewrite /compatible map_Forall_lookup in Hcompatible |- *.
  intros p [dq agree_phase] Hfrag.
  destruct (Hcompatible _ _ Hfrag) as
    (control_phase & Hagree & Hvdq & Hquiescent).
  exists control_phase. split_and!; try done.
  intros ->.
  apply leibniz_equiv. apply set_equiv. intros child_key.
  split.
  - intros Hchild.
    pose proof (terminating_children_update_remove_parent
      state key old_obj new_obj p Hlookup Hnew child_key Hchild) as Hold.
    rewrite (Hquiescent eq_refl) in Hold. exact Hold.
  - intros Hchild. rewrite elem_of_empty in Hchild. done.
Qed.

Lemma delete_state state key :
  control_auth 1 state ~~>
    control_auth 1 (delete key state).
Proof.
  apply view_update_auth.
  intros n b Hcompatible.
  change (compatible b state) in Hcompatible.
  change (compatible b (delete key state)).
  rewrite /compatible map_Forall_lookup in Hcompatible |- *.
  intros p [dq agree_phase] Hfrag.
  destruct (Hcompatible _ _ Hfrag) as
    (control_phase & Hagree & Hvdq & Hquiescent).
  exists control_phase. split_and!; try done.
  intros ->.
  apply leibniz_equiv. apply set_equiv. intros child_key.
  split.
  - intros Hchild.
    pose proof (terminating_children_delete_subset state key p
      child_key Hchild) as Hold.
    rewrite (Hquiescent eq_refl) in Hold. exact Hold.
  - intros Hchild. rewrite elem_of_empty in Hchild. done.
Qed.

Lemma update_introduce_mutable state key old_obj new_obj introduced_parent :
  state !! key = Some old_obj →
  terminating_obj_parent_ref old_obj = None →
  terminating_obj_parent_ref new_obj = Some introduced_parent →
  (control_auth 1 state ⋅
    control_frag (mk_frag introduced_parent Mutable)) ~~>
  (control_auth 1 (<[key := new_obj]> state) ⋅
    control_frag (mk_frag introduced_parent Mutable)).
Proof.
  intros Hlookup Hold Hnew.
  apply view_update.
  intros n bf Hcompatible.
  change (compatible
    (mk_frag introduced_parent Mutable ⋅ bf) state) in Hcompatible.
  change (compatible
    (mk_frag introduced_parent Mutable ⋅ bf)
    (<[key := new_obj]> state)).
  rewrite /compatible map_Forall_lookup in Hcompatible |- *.
  assert (Hbf_none : bf !! introduced_parent = None).
  { destruct (bf !! introduced_parent) as [[dq agree_phase]|]
      eqn:Hlookup_bf; last done.
    exfalso.
    assert (Hlookup_source :
      (mk_frag introduced_parent Mutable ⋅ bf) !! introduced_parent =
        Some ((DfracOwn 1,
          to_agree (A := leibnizO phase) Mutable) ⋅
          (dq, agree_phase))).
    { rewrite /mk_frag lookup_op lookup_singleton_eq Hlookup_bf
        Some_op_opM //. }
    destruct (Hcompatible _ _ Hlookup_source) as
      (source_phase & _ & Hvdq & _).
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dq 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt. apply Hlt. done. }
  intros p [dq agree_phase] Hfrag.
  destruct (decide (p = introduced_parent)) as [->|Hneq].
  - rewrite /mk_frag lookup_op lookup_singleton_eq Hbf_none
      right_id in Hfrag.
    inversion Hfrag. subst dq agree_phase.
    exists Mutable. split_and!; try done.
  - destruct (Hcompatible _ _ Hfrag) as
      (control_phase & Hagree & Hvdq & Hquiescent).
    exists control_phase. split_and!; try done.
    intros ->.
    rewrite (terminating_children_update_other_parent
      state key old_obj new_obj introduced_parent p
      Hlookup Hold Hnew Hneq).
    exact (Hquiescent eq_refl).
Qed.

Lemma set_phase state key uid old_phase new_phase :
  (new_phase = Quiescent →
    terminating_children state (key, uid) = ∅) →
  (control_auth 1 state ⋅
    control_frag (mk_frag (key, uid) old_phase)) ~~>
  (control_auth 1 state ⋅
    control_frag (mk_frag (key, uid) new_phase)).
Proof.
  intros Hquiescent.
  apply view_update.
  intros n bf Hrel.
  change (view_rel_raw n state
    (mk_frag (key, uid) old_phase ⋅ bf)) in Hrel.
  change (compatible
    (mk_frag (key, uid) old_phase ⋅ bf) state) in Hrel.
  rewrite /compatible map_Forall_lookup in Hrel |- *.
  assert (Hbf_none : bf !! (key, uid) = None).
  { destruct (bf !! (key, uid)) as [[dq agree_phase]|] eqn:Hlookup;
      last done.
    exfalso.
    assert (Hlookup_source :
      (mk_frag (key, uid) old_phase ⋅ bf) !! (key, uid) =
        Some ((DfracOwn 1,
          to_agree (A := leibnizO phase) old_phase) ⋅
          (dq, agree_phase))).
    { rewrite /mk_frag lookup_op lookup_singleton_eq Hlookup
        Some_op_opM //. }
    destruct (Hrel _ _ Hlookup_source) as
      (source_phase & _ & Hvdq & _).
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dq 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt.
    apply Hlt. done. }
  intros p [dq agree_phase] Hlookup.
  destruct (decide (p = (key, uid))) as [->|Hneq].
  - rewrite /mk_frag lookup_op lookup_singleton_eq Hbf_none
      right_id in Hlookup.
    inversion Hlookup. subst dq agree_phase.
    exists new_phase. split_and!; try done.
  - assert (Hlookup_bf : bf !! p = Some (dq, agree_phase)).
    { rewrite /mk_frag lookup_op lookup_singleton_ne // left_id
        in Hlookup.
      exact Hlookup. }
    assert (Hlookup_old :
      (mk_frag (key, uid) old_phase ⋅ bf) !! p =
        Some (dq, agree_phase)).
    { rewrite /mk_frag lookup_op lookup_singleton_ne // left_id.
      exact Hlookup_bf. }
    destruct (Hrel _ _ Hlookup_old) as
      (framed_phase & Hagree' & Hvdq & Hframed_phase).
    exists framed_phase. split_and!; done.
Qed.

Lemma create_living_vs γ state key obj :
  state !! key = None →
  terminating_obj_parent_ref obj = None →
  own_auth γ state ==∗
    own_auth γ (<[key := obj]> state).
Proof.
  iIntros (Habsent Hparent) "Hauth".
  iMod (own_update with "Hauth") as "Hauth".
  { eapply create_living; done. }
  iModIntro. iExact "Hauth".
Qed.

Lemma update_same_parent_vs γ state key old_obj new_obj :
  state !! key = Some old_obj →
  terminating_obj_parent_ref old_obj =
    terminating_obj_parent_ref new_obj →
  own_auth γ state ==∗
    own_auth γ (<[key := new_obj]> state).
Proof.
  iIntros (Hlookup Hparent) "Hauth".
  iMod (own_update with "Hauth") as "Hauth".
  { eapply update_same_parent; done. }
  iModIntro. iExact "Hauth".
Qed.

Lemma update_remove_parent_vs γ state key old_obj new_obj :
  state !! key = Some old_obj →
  terminating_obj_parent_ref new_obj = None →
  own_auth γ state ==∗
    own_auth γ (<[key := new_obj]> state).
Proof.
  iIntros (Hlookup Hnew) "Hauth".
  iMod (own_update with "Hauth") as "Hauth".
  { eapply update_remove_parent; done. }
  iModIntro. iExact "Hauth".
Qed.

Lemma delete_vs γ state key :
  own_auth γ state ==∗
    own_auth γ (delete key state).
Proof.
  iIntros "Hauth".
  iMod (own_update with "Hauth") as "Hauth".
  { apply delete_state. }
  iModIntro. iExact "Hauth".
Qed.

Lemma update_introduce_mutable_vs γ state key old_obj new_obj
    parent_key parent_uid :
  state !! key = Some old_obj →
  terminating_obj_parent_ref old_obj = None →
  terminating_obj_parent_ref new_obj = Some (parent_key, parent_uid) →
  own_auth γ state -∗
  own_frag γ parent_key parent_uid Mutable ==∗
    own_auth γ (<[key := new_obj]> state) ∗
    own_frag γ parent_key parent_uid Mutable.
Proof.
  iIntros (Hlookup Hold Hnew) "Hauth Hfrag".
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { eapply update_introduce_mutable; done. }
  iModIntro. iDestruct (own_op with "H") as "[$ $]".
Qed.

Lemma set_mutable_vs γ state key uid control_phase :
  own_auth γ state -∗
  own_frag γ key uid control_phase ==∗
    own_auth γ state ∗
    own_frag γ key uid Mutable.
Proof.
  iIntros "Hauth Hfrag".
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { apply set_phase. intros H.
    exfalso. exact (mutable_ne_quiescent H). }
  iModIntro.
  iDestruct (own_op with "H") as "[$ $]".
Qed.

Lemma reestablish_quiescent_vs γ state key uid :
  terminating_children state (key, uid) = ∅ →
  own_auth γ state -∗
  own_frag γ key uid Mutable ==∗
    own_auth γ state ∗
    own_frag γ key uid Quiescent.
Proof.
  iIntros (Hempty) "Hauth Hfrag".
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { apply set_phase. intros _. exact Hempty. }
  iModIntro.
  iDestruct (own_op with "H") as "[$ $]".
Qed.

End terminating_children.
