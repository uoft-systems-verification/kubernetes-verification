From New.proof Require Import prelude.
From New.proof.kubernetes_types Require Export prelude.
From iris.algebra Require Import cmra gset view.
From iris.base_logic.lib Require Import own.

(** Persistent evidence that deletion has been observed for one object
    identity.  The authority owns the current abstract state and used-UID set,
    so validity of every outstanding observation is enforced by the RA rather
    than carried separately in the Kubernetes invariant. *)
Section deletion_observation.

Definition observation := (KKey.t * types.UID.t)%type.
Definition authO : ofe :=
  leibnizO (gmap KKey.t KObjectV.t * gset types.UID.t).
Definition fragUR : ucmra := gsetUR observation.

Implicit Types (a : authO) (b : fragUR).

Local Definition compatible b a : Prop :=
  set_Forall (λ '(key, uid),
    uid ∈ a.2 ∧
    ∀ obj,
      a.1 !! key = Some obj →
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
      (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') ≠ None)
    b.

Local Definition view_rel_raw (_ : nat) a b : Prop := compatible b a.

Local Lemma view_rel_raw_mono n1 n2 a1 a2 b1 b2 :
  view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  (n2 ≤ n1)%nat →
  view_rel_raw n2 a2 b2.
Proof.
  intros Hcompatible Ha Hb _.
  apply (proj2 (discrete_iff n2 a1 a2)) in Ha.
  apply leibniz_equiv in Ha. subst a2.
  apply cmra_discrete_included_iff in Hb.
  apply gset_included in Hb.
  intros obs Hobs.
  apply Hcompatible, Hb, Hobs.
Qed.

Local Lemma view_rel_raw_valid n a b :
  view_rel_raw n a b → ✓{n} b.
Proof. done. Qed.

Local Lemma view_rel_raw_unit n :
  ∃ a, view_rel_raw n a ε.
Proof.
  exists (∅, ∅).
  intros obs Hobs. rewrite elem_of_empty in Hobs. done.
Qed.

Local Canonical Structure deletion_observation_view_rel : view_rel authO fragUR :=
  ViewRel view_rel_raw view_rel_raw_mono
          view_rel_raw_valid view_rel_raw_unit.

Definition observation_auth dq a : viewR deletion_observation_view_rel := ●V{dq} a.
Definition observation_frag b : viewR deletion_observation_view_rel := ◯V b.
Definition mk_frag (key : KKey.t) (uid : types.UID.t) : fragUR :=
  {[(key, uid)]}.

Class deletionObservationG Σ := {
  #[global] deletion_observation_inG ::
    inG Σ (viewR deletion_observation_view_rel);
}.

Definition deletionObservationΣ :=
  #[GFunctor (viewR deletion_observation_view_rel)].

#[global]
Instance subG_deletionObservationG Σ :
  subG deletionObservationΣ Σ → deletionObservationG Σ.
Proof. solve_inG. Qed.

Context {Σ : gFunctors}.
Context {Hobservation : deletionObservationG Σ}.
#[local] Existing Instance Hobservation.

Definition own_auth γ
    (state : gmap KKey.t KObjectV.t) (used_uid : gset types.UID.t) : iProp Σ :=
  own γ (observation_auth 1 (state, used_uid)).

Definition own_frag γ (key : KKey.t) (uid : types.UID.t) : iProp Σ :=
  own γ (observation_frag (mk_frag key uid)).

Global Instance own_auth_timeless γ state used_uid :
  Timeless (own_auth γ state used_uid).
Proof. unfold own_auth. apply _. Qed.

Global Instance own_frag_timeless γ key uid : Timeless (own_frag γ key uid).
Proof. unfold own_frag. apply _. Qed.

Global Instance own_frag_persistent γ key uid : Persistent (own_frag γ key uid).
Proof. unfold own_frag, observation_frag, mk_frag. apply _. Qed.

Lemma init :
  ⊢ |==> ∃ γ,
    own_auth γ (∅ : gmap KKey.t KObjectV.t)
      (∅ : gset types.UID.t).
Proof.
  unfold own_auth.
  iMod (own_alloc (observation_auth 1
    ((∅ : gmap KKey.t KObjectV.t),
      (∅ : gset types.UID.t)))) as (γ) "Hauth".
  { apply (proj2 (view_auth_dfrac_valid
      deletion_observation_view_rel 1
      ((∅ : gmap KKey.t KObjectV.t),
        (∅ : gset types.UID.t)))).
    split; [done|].
    intros n.
    change (view_rel_raw n
      ((∅ : gmap KKey.t KObjectV.t),
        (∅ : gset types.UID.t)) ε).
    intros obs Hobs. rewrite elem_of_empty in Hobs. done. }
  iModIntro. iExists γ. iExact "Hauth".
Qed.

Lemma auth_frag_valid {γ state used_uid key uid} :
  own_auth γ state used_uid -∗
  own_frag γ key uid -∗
  ⌜ uid ∈ used_uid ∧
    ∀ obj,
      state !! key = Some obj →
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
      (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝.
Proof.
  unfold own_auth, own_frag.
  iIntros "Hauth Hfrag".
  iDestruct (own_valid_2 with "Hauth Hfrag") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid.
  iPureIntro.
  apply (proj1 (view_both_validN deletion_observation_view_rel 0%nat
    (state, used_uid) (mk_frag key uid))) in Hvalid.
  change (view_rel_raw 0%nat (state, used_uid)
    (mk_frag key uid)) in Hvalid.
  unfold view_rel_raw, compatible in Hvalid.
  apply (Hvalid (key, uid)).
  apply elem_of_singleton. done.
Qed.

Lemma extend_used_uid state used_uid uid :
  observation_auth 1 (state, used_uid) ~~>
    observation_auth 1 (state, used_uid ∪ {[uid]}).
Proof.
  apply view_update_auth.
  intros n b Hcompatible.
  intros [key observed_uid] Hobserved.
  destruct (Hcompatible (key, observed_uid) Hobserved) as
    [Huid_used Hterminating].
  split; [apply elem_of_union_l; exact Huid_used|exact Hterminating].
Qed.

Lemma create state used_uid key uid obj :
  uid ∉ used_uid →
  (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
  observation_auth 1 (state, used_uid) ~~>
    observation_auth 1 (<[key := obj]> state, used_uid ∪ {[uid]}).
Proof.
  intros Hfresh Hobj_uid.
  apply view_update_auth.
  intros n b Hcompatible.
  intros [observed_key observed_uid] Hobserved.
  destruct (Hcompatible (observed_key, observed_uid) Hobserved) as
    [Huid_used Hterminating].
  split; [apply elem_of_union_l; exact Huid_used|].
  intros current_obj Hlookup Huid.
  destruct (decide (observed_key = key)) as [->|Hkey_ne].
  - rewrite lookup_insert_eq in Hlookup. injection Hlookup as <-.
    assert (uid = observed_uid) as -> by congruence.
    exfalso. apply Hfresh. done.
  - rewrite lookup_insert_ne // in Hlookup.
    eapply Hterminating; done.
Qed.

Lemma update state used_uid key old_obj new_obj :
  state !! key = Some old_obj →
  (KObjectV.objectmeta old_obj).(ObjectMetaV.UID') =
    (KObjectV.objectmeta new_obj).(ObjectMetaV.UID') →
  ((KObjectV.objectmeta old_obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
    (KObjectV.objectmeta new_obj).(ObjectMetaV.DeletionTimestamp') ≠ None) →
  observation_auth 1 (state, used_uid) ~~>
    observation_auth 1 (<[key := new_obj]> state, used_uid).
Proof.
  intros Hlookup_old Huid_eq Hdeletion_timestamp.
  apply view_update_auth.
  intros n b Hcompatible.
  intros [observed_key observed_uid] Hobserved.
  destruct (Hcompatible (observed_key, observed_uid) Hobserved) as
    [Huid_used Hterminating].
  split; [exact Huid_used|].
  intros current_obj Hlookup Huid.
  destruct (decide (observed_key = key)) as [->|Hkey_ne].
  - rewrite lookup_insert_eq in Hlookup. injection Hlookup as <-.
    apply Hdeletion_timestamp.
    eapply Hterminating; [exact Hlookup_old|].
    congruence.
  - rewrite lookup_insert_ne // in Hlookup.
    eapply Hterminating; done.
Qed.

Lemma delete_state state used_uid key :
  observation_auth 1 (state, used_uid) ~~>
    observation_auth 1 (delete key state, used_uid).
Proof.
  apply view_update_auth.
  intros n b Hcompatible.
  intros [observed_key observed_uid] Hobserved.
  destruct (Hcompatible (observed_key, observed_uid) Hobserved) as
    [Huid_used Hterminating].
  split; [exact Huid_used|].
  intros obj Hlookup Huid.
  change ((delete key state) !! observed_key = Some obj) in Hlookup.
  apply lookup_delete_Some in Hlookup as [_ Hlookup].
  eapply Hterminating; done.
Qed.

Lemma observe state used_uid key uid :
  uid ∈ used_uid →
  (∀ obj,
    state !! key = Some obj →
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
    (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') ≠ None) →
  observation_auth 1 (state, used_uid) ~~>
    observation_auth 1 (state, used_uid) ⋅
      observation_frag (mk_frag key uid).
Proof.
  intros Huid_used Hterminating.
  apply view_update_alloc.
  intros n b Hcompatible.
  rewrite /compatible /mk_frag gset_op.
  intros [observed_key observed_uid] Hobserved.
  apply elem_of_union in Hobserved as [Hnew|Hobserved].
  - apply elem_of_singleton in Hnew. injection Hnew as -> ->.
    split; done.
  - exact (Hcompatible (observed_key, observed_uid) Hobserved).
Qed.

Lemma extend_used_uid_vs {γ state used_uid} uid :
  own_auth γ state used_uid ==∗
    own_auth γ state (used_uid ∪ {[uid]}).
Proof.
  unfold own_auth.
  iApply own_update.
  apply extend_used_uid.
Qed.

Lemma create_vs {γ state used_uid} key uid obj :
  uid ∉ used_uid →
  (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
  own_auth γ state used_uid ==∗
    own_auth γ (<[key := obj]> state) (used_uid ∪ {[uid]}).
Proof.
  intros Hfresh Hobj_uid.
  unfold own_auth.
  iApply own_update.
  apply create; done.
Qed.

Lemma update_vs {γ state used_uid} key old_obj new_obj :
  state !! key = Some old_obj →
  (KObjectV.objectmeta old_obj).(ObjectMetaV.UID') =
    (KObjectV.objectmeta new_obj).(ObjectMetaV.UID') →
  ((KObjectV.objectmeta old_obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
    (KObjectV.objectmeta new_obj).(ObjectMetaV.DeletionTimestamp') ≠ None) →
  own_auth γ state used_uid ==∗
    own_auth γ (<[key := new_obj]> state) used_uid.
Proof.
  intros Hlookup Huid Hdeletion_timestamp.
  unfold own_auth.
  iApply own_update.
  eapply update; done.
Qed.

Lemma delete_vs {γ state used_uid} key :
  own_auth γ state used_uid ==∗
    own_auth γ (delete key state) used_uid.
Proof.
  unfold own_auth.
  iApply own_update.
  apply delete_state.
Qed.

Lemma observe_vs {γ state used_uid} key uid :
  uid ∈ used_uid →
  (∀ obj,
    state !! key = Some obj →
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
    (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') ≠ None) →
  own_auth γ state used_uid ==∗
    own_auth γ state used_uid ∗ own_frag γ key uid.
Proof.
  intros Huid_used Hterminating.
  unfold own_auth, own_frag.
  rewrite -own_op.
  iApply own_update.
  apply observe; done.
Qed.

Lemma observe_list_vs {A} {γ state used_uid}
    (key_of : A → KKey.t) (uid_of : A → types.UID.t) xs :
  Forall (λ x,
    uid_of x ∈ used_uid ∧
    ∀ obj,
      state !! key_of x = Some obj →
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid_of x →
      (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') ≠ None) xs →
  own_auth γ state used_uid ==∗
    own_auth γ state used_uid ∗
    ([∗ list] x ∈ xs, own_frag γ (key_of x) (uid_of x)).
Proof.
  intros Hobserved.
  induction Hobserved as [|x xs [Huid Hterminating] _ IH].
  - iIntros "Hauth". rewrite big_sepL_nil. iModIntro. iFrame.
  - iIntros "Hauth".
    iMod (observe_vs (key_of x) (uid_of x) Huid Hterminating
      with "Hauth") as "[Hauth #Hx]".
    iMod (IH with "Hauth") as "[Hauth Hxs]".
    iModIntro. rewrite big_sepL_cons. iFrame "Hauth Hx Hxs".
Qed.

End deletion_observation.
