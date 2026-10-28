From New.proof Require Import prelude.
From New.object_specs Require Export prelude.
From iris.algebra Require Import cmra gmap gset view.
From iris.base_logic.lib Require Import own.

(** Exact knowledge of the living orphans in each bucket.

    A bucket is a (kind, namespace) pair. A living orphan belongs to the bucket
    of its key, so buckets are pairwise disjoint and a write to one key changes
    at most one bucket. A fragment [own_frag γ bk dq ks]
    says that the living orphans of [bk] are exactly [ks]. Any fraction reads the
    set; changing it needs the whole fragment, as for children in [cview].
    Fragments are created only together with the authority, by [init_frags]; no
    later update adds one. The fractions of a bucket's fragments add up to at
    most 1, so its whole fragment is unique. *)
Section orphan_view.

Definition bucket : Type := (go_string * go_string)%type.

Definition bucket_of (k : KKey.t) : bucket := (k.(KKey.Kind'), k.(KKey.Namespace')).

Definition is_living_orphan (obj : KObjectV.t) : Prop :=
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None ∧
  obj_parent_ref obj = None.

Definition in_bucket (bk : bucket) (k : KKey.t) (obj : KObjectV.t) : Prop :=
  bucket_of k = bk ∧ is_living_orphan obj.

#[global] Instance is_living_orphan_dec obj : Decision (is_living_orphan obj).
Proof. unfold is_living_orphan. apply _. Defined.

#[global] Instance in_bucket_dec bk k obj : Decision (in_bucket bk k obj).
Proof. unfold in_bucket. apply _. Defined.

Lemma not_living_orphan_of_parent obj p :
  obj_parent_ref obj = Some p → ¬ is_living_orphan obj.
Proof. intros Hparent (_ & Hnone). rewrite Hparent in Hnone. done. Qed.

Lemma not_living_orphan_of_terminating obj :
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
  ¬ is_living_orphan obj.
Proof. intros Hterminating (Hliving & _). done. Qed.

(** Orphan status depends only on the deletion timestamp and the controller
    reference. *)
Lemma is_living_orphan_iff old_obj new_obj :
  (KObjectV.objectmeta old_obj).(ObjectMetaV.DeletionTimestamp') =
    (KObjectV.objectmeta new_obj).(ObjectMetaV.DeletionTimestamp') →
  obj_parent_ref old_obj = obj_parent_ref new_obj →
  is_living_orphan old_obj ↔ is_living_orphan new_obj.
Proof.
  intros Hdeletion Hparent.
  rewrite /is_living_orphan Hdeletion Hparent //.
Qed.

Definition orphans (state : gmap KKey.t KObjectV.t) (bk : bucket) : gset KKey.t :=
  dom (filter (λ '(k, obj), in_bucket bk k obj) state).

Lemma elem_of_orphans state bk k :
  k ∈ orphans state bk ↔ ∃ obj, state !! k = Some obj ∧ in_bucket bk k obj.
Proof.
  rewrite /orphans elem_of_dom. split.
  - intros [obj Hobj]. apply map_lookup_filter_Some in Hobj as [Hlookup Hin].
    exists obj. done.
  - intros (obj & Hlookup & Hin). exists obj.
    apply map_lookup_filter_Some. done.
Qed.

Lemma orphans_empty bk : orphans ∅ bk = ∅.
Proof. rewrite /orphans map_filter_empty dom_empty_L //. Qed.

Lemma not_elem_of_orphans_other state bk k :
  bucket_of k ≠ bk → k ∉ orphans state bk.
Proof.
  intros Hne Hk. apply elem_of_orphans in Hk as (obj & _ & Hbk & _). done.
Qed.

Lemma orphans_insert state k obj bk :
  orphans (<[k := obj]> state) bk =
    if decide (in_bucket bk k obj) then orphans state bk ∪ {[k]}
    else orphans state bk ∖ {[k]}.
Proof.
  apply set_eq. intros k'.
  rewrite elem_of_orphans.
  destruct (decide (k' = k)) as [->|Hne].
  - rewrite lookup_insert_eq.
    case_decide as Hin.
    + split; [intros _; apply elem_of_union_r, elem_of_singleton; done|].
      intros _. exists obj. done.
    + split.
      * intros (obj' & Heq & Hin'). injection Heq as <-. done.
      * intros Hk. apply elem_of_difference in Hk as [_ Hk].
        exfalso. apply Hk. apply elem_of_singleton. done.
  - rewrite lookup_insert_ne //.
    rewrite -elem_of_orphans.
    case_decide.
    + rewrite elem_of_union elem_of_singleton. split; [by left|].
      intros [Hk|Hk]; done.
    + rewrite elem_of_difference elem_of_singleton. split; [done|].
      intros [Hk _]. done.
Qed.

Lemma orphans_delete state k bk :
  orphans (delete k state) bk = orphans state bk ∖ {[k]}.
Proof.
  apply set_eq. intros k'.
  rewrite elem_of_difference elem_of_singleton !elem_of_orphans.
  destruct (decide (k' = k)) as [->|Hne].
  - rewrite lookup_delete_eq. split.
    + intros (obj & Hlookup & _). done.
    + intros [_ Hk]. done.
  - rewrite lookup_delete_ne //. split.
    + intros Hk. split; done.
    + intros [Hk _]. done.
Qed.

Lemma orphans_insert_other state k obj bk :
  bucket_of k ≠ bk →
  orphans (<[k := obj]> state) bk = orphans state bk.
Proof.
  intros Hne.
  pose proof (not_elem_of_orphans_other state bk k Hne) as Hk.
  rewrite orphans_insert.
  case_decide as Hin.
  - destruct Hin as [Hbk _]. done.
  - apply set_eq. intros k'.
    rewrite elem_of_difference elem_of_singleton.
    split; [intros [Hk' _]; done|].
    intros Hk'. split; [done|]. intros ->. done.
Qed.

Lemma orphans_delete_other state k bk :
  bucket_of k ≠ bk →
  orphans (delete k state) bk = orphans state bk.
Proof.
  intros Hne.
  pose proof (not_elem_of_orphans_other state bk k Hne) as Hk.
  rewrite orphans_delete.
  apply set_eq. intros k'.
  rewrite elem_of_difference elem_of_singleton.
  split; [intros [Hk' _]; done|].
  intros Hk'. split; [done|]. intros ->. done.
Qed.

(** A write that keeps the key's orphan status leaves every bucket unchanged. *)
Lemma orphans_insert_same state k old_obj new_obj bk :
  state !! k = Some old_obj →
  (is_living_orphan old_obj ↔ is_living_orphan new_obj) →
  orphans (<[k := new_obj]> state) bk = orphans state bk.
Proof.
  intros Hlookup Hsame.
  destruct (decide (bucket_of k = bk)) as [<-|Hne];
    last (apply orphans_insert_other; done).
  rewrite orphans_insert.
  apply set_eq. intros k'.
  case_decide as Hin.
  - rewrite elem_of_union elem_of_singleton.
    split; [|intros Hk'; left; done].
    intros [Hk' | ->]; [done|].
    apply elem_of_orphans. exists old_obj.
    split; [done|]. split; [done|]. apply Hsame. destruct Hin as [_ Hin]. done.
  - rewrite elem_of_difference elem_of_singleton.
    split; [intros [Hk' _]; done|].
    intros Hk'. split; [done|]. intros ->.
    apply elem_of_orphans in Hk' as (obj & Hlookup' & _ & Hliving).
    rewrite Hlookup in Hlookup'. injection Hlookup' as <-.
    apply Hin. split; [done|]. apply Hsame. done.
Qed.

Lemma orphans_insert_fresh state k obj bk :
  state !! k = None →
  ¬ is_living_orphan obj →
  orphans (<[k := obj]> state) bk = orphans state bk.
Proof.
  intros Hlookup Hnot.
  rewrite orphans_insert.
  case_decide as Hin; first (destruct Hin as [_ Hin]; done).
  apply set_eq. intros k'.
  rewrite elem_of_difference elem_of_singleton.
  split; [intros [Hk' _]; done|].
  intros Hk'. split; [done|]. intros ->.
  apply elem_of_orphans in Hk' as (obj' & Hlookup' & _).
  rewrite Hlookup in Hlookup'. done.
Qed.

Lemma orphans_delete_not_orphan state k bk :
  (∀ obj, state !! k = Some obj → ¬ is_living_orphan obj) →
  orphans (delete k state) bk = orphans state bk.
Proof.
  intros Hnot.
  rewrite orphans_delete.
  apply set_eq. intros k'.
  rewrite elem_of_difference elem_of_singleton.
  split; [intros [Hk' _]; done|].
  intros Hk'. split; [done|]. intros ->.
  apply elem_of_orphans in Hk' as (obj & Hlookup & _ & Hliving).
  apply (Hnot obj Hlookup). done.
Qed.

Lemma orphans_insert_enter state k obj :
  is_living_orphan obj →
  orphans (<[k := obj]> state) (bucket_of k) = orphans state (bucket_of k) ∪ {[k]}.
Proof.
  intros Hliving. rewrite orphans_insert decide_True //.
Qed.

Lemma orphans_insert_leave state k obj :
  ¬ is_living_orphan obj →
  orphans (<[k := obj]> state) (bucket_of k) = orphans state (bucket_of k) ∖ {[k]}.
Proof.
  intros Hnot. rewrite orphans_insert decide_False //.
  intros [_ Hliving]. done.
Qed.

Lemma orphans_disjoint state bk1 bk2 :
  bk1 ≠ bk2 → orphans state bk1 ## orphans state bk2.
Proof.
  intros Hne k Hk1 Hk2.
  apply elem_of_orphans in Hk1 as (obj1 & _ & Hbk1 & _).
  apply elem_of_orphans in Hk2 as (obj2 & _ & Hbk2 & _).
  apply Hne. rewrite -Hbk1 -Hbk2 //.
Qed.

Definition authO : ofe := leibnizO (gmap KKey.t KObjectV.t).
Definition fragUR : ucmra :=
  gmapUR bucket (prodR dfracR (agreeR (leibnizO (gset KKey.t)))).

Implicit Types (a : authO) (b : fragUR).

Local Definition compatible b a : Prop :=
  map_Forall (λ bk '(dq, agree_ks),
    ∃ ks,
      agree_ks ≡ to_agree (A := leibnizO (gset KKey.t)) ks ∧
      ✓ dq ∧
      ks = orphans a bk) b.

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
  intros bk [dq2 agree2] Hlookup2.
  destruct (lookup_includedN n2 b2 b1) as [Hlookup_incl _].
  specialize (Hlookup_incl Hb bk).
  rewrite Hlookup2 in Hlookup_incl.
  destruct (Some_includedN_is_Some _ _ _ Hlookup_incl) as
    [[dq1 agree1] Hlookup1].
  destruct (Hcompatible _ _ Hlookup1) as
    (ks & Hagree1 & Hvdq1 & Hks).
  rewrite Hlookup1 in Hlookup_incl.
  assert (Hvalid1 :
    ✓{n2} (Some (dq1, agree1) :
      option (dfrac * agree (leibnizO (gset KKey.t))))).
  { simpl. apply cmra_valid_validN.
    apply pair_valid. split.
    - apply cmra_valid_validN. done.
    - rewrite Hagree1. done. }
  assert (Hvalid2 :
    ✓{n2} (Some (dq2, agree2) :
      option (dfrac * agree (leibnizO (gset KKey.t))))).
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
  exists ks. split_and!; try done.
  apply (proj2 (discrete_iff n2 agree2
    (to_agree (A := leibnizO (gset KKey.t)) ks))).
  etrans; [exact Hagree2|exact (Hagree1 n2)].
Qed.

Local Lemma view_rel_raw_valid n a b :
  view_rel_raw n a b → ✓{n} b.
Proof.
  intros Hcompatible bk.
  destruct (b !! bk) as [[dq agree_ks]|] eqn:Hlookup.
  - destruct (Hcompatible _ _ Hlookup) as
      (ks & Hagree & Hvdq & _).
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
  intros bk x Hlookup.
  rewrite lookup_empty in Hlookup. done.
Qed.

Local Canonical Structure orphan_view_rel : view_rel authO fragUR :=
  ViewRel view_rel_raw view_rel_raw_mono
    view_rel_raw_valid view_rel_raw_unit.

Definition orphan_auth dq a : viewR orphan_view_rel := ●V{dq} a.
Definition orphan_frag b : viewR orphan_view_rel := ◯V b.

Definition mk_frag (bk : bucket) (dq : dfrac) (ks : gset KKey.t) : fragUR :=
  {[bk := (dq, to_agree (A := leibnizO (gset KKey.t)) ks)]}.

(* A frame next to the whole fragment of [bk] has no fragment of [bk]. *)
Local Lemma frame_none_of_whole bk ks bf a :
  compatible (mk_frag bk (DfracOwn 1) ks ⋅ bf) a →
  bf !! bk = None.
Proof.
  intros Hcompatible.
  destruct (bf !! bk) as [[dq agree_ks]|] eqn:Hlookup_bf; last done.
  exfalso.
  assert (Hlookup_source :
    (mk_frag bk (DfracOwn 1) ks ⋅ bf) !! bk =
      Some ((DfracOwn 1, to_agree (A := leibnizO (gset KKey.t)) ks) ⋅
        (dq, agree_ks))).
  { rewrite /mk_frag lookup_op lookup_singleton_eq Hlookup_bf
      Some_op_opM //. }
  destruct (map_Forall_lookup_1 _ _ _ _ Hcompatible Hlookup_source) as
    (ks' & _ & Hvdq & _).
  simpl in Hvdq.
  pose proof (dfrac_valid_own_l dq 1 Hvdq) as Hlt.
  apply (Qp.lt_nge 1 1) in Hlt. apply Hlt. done.
Qed.

Lemma update_auth state state' :
  (∀ bk, orphans state' bk = orphans state bk) →
  orphan_auth 1 state ~~> orphan_auth 1 state'.
Proof.
  intros Hsame.
  apply view_update_auth.
  intros n bf Hcompatible.
  change (compatible bf state) in Hcompatible.
  change (compatible bf state').
  rewrite /compatible map_Forall_lookup in Hcompatible |- *.
  intros bk [dq agree_ks] Hlookup.
  destruct (Hcompatible _ _ Hlookup) as
    (ks & Hagree & Hvdq & Hks).
  exists ks. split_and!; try done.
  simpl in *. rewrite Hks Hsame //.
Qed.

Lemma update_bucket state state' bk ks :
  (∀ bk', bk' ≠ bk → orphans state' bk' = orphans state bk') →
  orphan_auth 1 state ⋅ orphan_frag (mk_frag bk (DfracOwn 1) ks) ~~>
    orphan_auth 1 state' ⋅
    orphan_frag (mk_frag bk (DfracOwn 1) (orphans state' bk)).
Proof.
  intros Hsame.
  apply view_update.
  intros n bf Hcompatible.
  change (compatible (mk_frag bk (DfracOwn 1) ks ⋅ bf) state)
    in Hcompatible.
  change (compatible (mk_frag bk (DfracOwn 1) (orphans state' bk) ⋅ bf)
    state').
  pose proof (frame_none_of_whole bk ks bf state Hcompatible)
    as Hbf_none.
  rewrite /compatible map_Forall_lookup in Hcompatible |- *.
  intros bk' [dq agree_ks] Hlookup.
  destruct (decide (bk' = bk)) as [->|Hne].
  - rewrite /mk_frag lookup_op lookup_singleton_eq Hbf_none right_id
      in Hlookup.
    inversion Hlookup. subst dq agree_ks.
    exists (orphans state' bk). split_and!; done.
  - assert (Hlookup_source :
      (mk_frag bk (DfracOwn 1) ks ⋅ bf) !! bk' = Some (dq, agree_ks)).
    { rewrite /mk_frag lookup_op lookup_singleton_ne // left_id.
      rewrite /mk_frag lookup_op lookup_singleton_ne // left_id in Hlookup.
      exact Hlookup. }
    destruct (Hcompatible _ _ Hlookup_source) as
      (ks' & Hagree & Hvdq & Hks).
    exists ks'. split_and!; try done.
    simpl in *. rewrite Hks Hsame //.
Qed.

Class orphanViewG Σ := {
  #[global] orphan_view_inG :: inG Σ (viewR orphan_view_rel);
}.

Definition orphanViewΣ := #[GFunctor (viewR orphan_view_rel)].

#[global]
Instance subG_orphanViewG Σ :
  subG orphanViewΣ Σ → orphanViewG Σ.
Proof. solve_inG. Qed.

Context {Σ : gFunctors}.
Context {Horphan : orphanViewG Σ}.
#[local] Existing Instance Horphan.

Definition own_auth γ (state : gmap KKey.t KObjectV.t) : iProp Σ :=
  own γ (orphan_auth 1 state).

Definition own_frag γ (bk : bucket) (dq : dfrac) (ks : gset KKey.t) : iProp Σ :=
  own γ (orphan_frag (mk_frag bk dq ks)).

Global Instance own_auth_timeless γ state :
  Timeless (own_auth γ state).
Proof. apply _. Qed.

Global Instance own_frag_timeless γ bk dq ks :
  Timeless (own_frag γ bk dq ks).
Proof. apply _. Qed.

Lemma init :
  ⊢ |==> ∃ γ,
    own_auth γ (∅ : gmap KKey.t KObjectV.t).
Proof.
  unfold own_auth.
  iMod (own_alloc (orphan_auth 1 (∅ : gmap KKey.t KObjectV.t))) as (γ) "Hauth".
  { apply (proj2 (view_auth_dfrac_valid orphan_view_rel 1
      (∅ : gmap KKey.t KObjectV.t))).
    split; [done|].
    intros n.
    change (view_rel_raw n (∅ : gmap KKey.t KObjectV.t) ε).
    rewrite /view_rel_raw /compatible map_Forall_lookup.
    intros bk x Hlookup. rewrite lookup_empty in Hlookup. done. }
  iModIntro. iExists γ. iExact "Hauth".
Qed.

(** The authority over the empty state, with the whole fragment of each bucket
    in [S]. This is the only way to create fragments. *)
Lemma init_frags (S : gset bucket) :
  ⊢ |==> ∃ γ,
    own_auth γ (∅ : gmap KKey.t KObjectV.t) ∗
    [∗ set] bk ∈ S, own_frag γ bk (DfracOwn 1) ∅.
Proof.
  iMod (own_alloc (orphan_auth 1 (∅ : gmap KKey.t KObjectV.t) ⋅
    orphan_frag (gset_to_gmap
      (DfracOwn 1, to_agree (A := leibnizO (gset KKey.t)) ∅) S)))
    as (γ) "[Hauth Hfrags]".
  { apply (proj2 (view_both_dfrac_valid orphan_view_rel 1
      (∅ : gmap KKey.t KObjectV.t) _)).
    split; [done|].
    intros n.
    change (compatible (gset_to_gmap
      (DfracOwn 1, to_agree (A := leibnizO (gset KKey.t)) ∅) S)
      (∅ : gmap KKey.t KObjectV.t)).
    rewrite /compatible map_Forall_lookup.
    intros bk [dq agree_ks] Hlookup.
    apply lookup_gset_to_gmap_Some in Hlookup as [_ Hx].
    inversion Hx. subst dq agree_ks.
    exists ∅. split_and!; done. }
  iModIntro. iExists γ. iFrame "Hauth".
  iEval (rewrite /orphan_frag -big_opS_gset_to_gmap big_opS_view_frag)
    in "Hfrags".
  iDestruct (big_opS_own_1 with "Hfrags") as "Hfrags".
  rewrite /own_frag /orphan_frag /mk_frag.
  iExact "Hfrags".
Qed.

Lemma own_auth_frag_valid {γ state bk dq ks} :
  own_auth γ state -∗
  own_frag γ bk dq ks -∗
  ⌜ ks = orphans state bk ⌝.
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_valid_2 with "Hauth Hfrag") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid.
  iPureIntro.
  apply (proj1 (view_both_validN orphan_view_rel 0%nat
    state (mk_frag bk dq ks))) in Hvalid.
  change (compatible (mk_frag bk dq ks) state) in Hvalid.
  assert (Hlookup :
    mk_frag bk dq ks !! bk =
      Some (dq, to_agree (A := leibnizO (gset KKey.t)) ks)).
  { rewrite /mk_frag lookup_singleton_eq //. }
  destruct (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup) as
    (ks' & Hagree & _ & Hks).
  assert (Hks_eqv : (ks : leibnizO (gset KKey.t)) ≡ ks').
  { apply (inj (to_agree : leibnizO (gset KKey.t) → agree (leibnizO (gset KKey.t)))).
    exact Hagree. }
  apply leibniz_equiv in Hks_eqv. subst ks'.
  done.
Qed.

Lemma own_auth_frag_lookup {γ state bk dq ks} k :
  k ∈ ks →
  own_auth γ state -∗
  own_frag γ bk dq ks -∗
  ⌜ ∃ obj, state !! k = Some obj ∧ in_bucket bk k obj ⌝.
Proof.
  iIntros (Hk) "Hauth Hfrag".
  iDestruct (own_auth_frag_valid with "Hauth Hfrag") as %->.
  iPureIntro. apply elem_of_orphans. done.
Qed.

Lemma own_frag_split γ bk dq1 dq2 ks :
  own_frag γ bk (dq1 ⋅ dq2) ks ⊣⊢ own_frag γ bk dq1 ks ∗ own_frag γ bk dq2 ks.
Proof.
  rewrite /own_frag -own_op /orphan_frag -view_frag_op /mk_frag singleton_op
    -pair_op agree_idemp //.
Qed.

Lemma own_frag_agree γ bk dq1 dq2 ks1 ks2 :
  own_frag γ bk dq1 ks1 -∗
  own_frag γ bk dq2 ks2 -∗
  ⌜ ks1 = ks2 ⌝.
Proof.
  iIntros "Hfrag1 Hfrag2".
  iDestruct (own_valid_2 with "Hfrag1 Hfrag2") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid.
  iPureIntro.
  rewrite /orphan_frag -view_frag_op in Hvalid.
  apply view_frag_validN in Hvalid as [a Hrel].
  apply view_rel_raw_valid in Hrel.
  rewrite /mk_frag singleton_op singleton_validN -pair_op pair_validN in Hrel.
  destruct Hrel as [_ Hagree].
  apply to_agree_op_validN in Hagree.
  apply (discrete_iff (A := leibnizO (gset KKey.t)) 0%nat ks1 ks2) in Hagree.
  exact Hagree.
Qed.

(** Any state change that leaves every bucket unchanged. *)
Lemma update_vs {γ state} state' :
  (∀ bk, orphans state' bk = orphans state bk) →
  own_auth γ state ==∗ own_auth γ state'.
Proof.
  iIntros (Hsame) "Hauth".
  iMod (own_update with "Hauth") as "Hauth".
  { apply update_auth. exact Hsame. }
  iModIntro. iExact "Hauth".
Qed.

Lemma update_bucket_vs {γ state bk ks} state' :
  (∀ bk', bk' ≠ bk → orphans state' bk' = orphans state bk') →
  own_auth γ state -∗
  own_frag γ bk (DfracOwn 1) ks ==∗
    own_auth γ state' ∗
    own_frag γ bk (DfracOwn 1) (orphans state' bk).
Proof.
  iIntros (Hsame) "Hauth Hfrag".
  iMod (own_update_2 with "Hauth Hfrag") as "H".
  { apply update_bucket. exact Hsame. }
  iModIntro. iDestruct (own_op with "H") as "[$ $]".
Qed.

Lemma insert_same_vs {γ state} k old_obj new_obj :
  state !! k = Some old_obj →
  (is_living_orphan old_obj ↔ is_living_orphan new_obj) →
  own_auth γ state ==∗ own_auth γ (<[k := new_obj]> state).
Proof.
  intros Hlookup Hsame.
  apply update_vs. intros bk.
  eapply orphans_insert_same; done.
Qed.

Lemma create_vs {γ state} k obj :
  state !! k = None →
  ¬ is_living_orphan obj →
  own_auth γ state ==∗ own_auth γ (<[k := obj]> state).
Proof.
  intros Hlookup Hnot.
  apply update_vs. intros bk.
  apply orphans_insert_fresh; done.
Qed.

Lemma delete_not_orphan_vs {γ state} k :
  (∀ obj, state !! k = Some obj → ¬ is_living_orphan obj) →
  own_auth γ state ==∗ own_auth γ (delete k state).
Proof.
  intros Hnot.
  apply update_vs. intros bk.
  apply orphans_delete_not_orphan. done.
Qed.

(** A key becomes a living orphan, as in a release or an orphan creation. *)
Lemma enter_vs {γ state ks} k obj :
  is_living_orphan obj →
  own_auth γ state -∗
  own_frag γ (bucket_of k) (DfracOwn 1) ks ==∗
    own_auth γ (<[k := obj]> state) ∗
    own_frag γ (bucket_of k) (DfracOwn 1) (ks ∪ {[k]}).
Proof.
  iIntros (Hliving) "Hauth Hfrag".
  iDestruct (own_auth_frag_valid with "Hauth Hfrag") as %->.
  iMod (update_bucket_vs (<[k := obj]> state) with "Hauth Hfrag")
    as "[$ Hfrag]".
  { intros bk Hne. apply orphans_insert_other. intros Heq. apply Hne. done. }
  rewrite orphans_insert_enter //.
Qed.

(** A key stops being a living orphan, as in an adoption. *)
Lemma leave_vs {γ state ks} k obj :
  ¬ is_living_orphan obj →
  own_auth γ state -∗
  own_frag γ (bucket_of k) (DfracOwn 1) ks ==∗
    own_auth γ (<[k := obj]> state) ∗
    own_frag γ (bucket_of k) (DfracOwn 1) (ks ∖ {[k]}).
Proof.
  iIntros (Hnot) "Hauth Hfrag".
  iDestruct (own_auth_frag_valid with "Hauth Hfrag") as %->.
  iMod (update_bucket_vs (<[k := obj]> state) with "Hauth Hfrag")
    as "[$ Hfrag]".
  { intros bk Hne. apply orphans_insert_other. intros Heq. apply Hne. done. }
  rewrite orphans_insert_leave //.
Qed.

Lemma delete_leave_vs {γ state ks} k :
  own_auth γ state -∗
  own_frag γ (bucket_of k) (DfracOwn 1) ks ==∗
    own_auth γ (delete k state) ∗
    own_frag γ (bucket_of k) (DfracOwn 1) (ks ∖ {[k]}).
Proof.
  iIntros "Hauth Hfrag".
  iDestruct (own_auth_frag_valid with "Hauth Hfrag") as %->.
  iMod (update_bucket_vs (delete k state) with "Hauth Hfrag")
    as "[$ Hfrag]".
  { intros bk Hne. apply orphans_delete_other. intros Heq. apply Hne. done. }
  rewrite orphans_delete //.
Qed.

End orphan_view.
