From New.proof Require Import prelude.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From iris.algebra Require Import cmra csum excl gset gmap.
From iris.base_logic.lib Require Import own.

(* Reserved names are classified statically. In particular, API-server
   generated names never satisfy this predicate. *)
Axiom reserved_key_pred : KKey.t → Prop.

Inductive reservation_status :=
  | Available
  | Occupied (uid : types.UID.t)
  | Deleting (uid : types.UID.t).

#[global] Instance reservation_status_eq_decision : EqDecision reservation_status.
Proof. solve_decision. Defined.

Section kview.

Definition authO : ofe := prodO (gmapO KKey.t (leibnizO KObjectV.t)) (gsetO (leibnizO types.UID.t)).

Definition metaUR : ucmra := gmapUR (KKey.t * types.UID.t) (prodR dfracR (agreeR (leibnizO ObjectMetaV.t))).
Definition specUR : ucmra := gmapUR (KKey.t * types.UID.t) (prodR dfracR (agreeR (leibnizO ObjectSpecV.t))).
Definition statusUR : ucmra := gmapUR (KKey.t * types.UID.t) (prodR dfracR (agreeR (leibnizO ObjectStatusV.t))).
(* One map classifies keys. [Unreserved] uses an idempotent agreement token and
   is therefore persistent; [Reserved status] uses an exclusive token and
   tracks the reserved-name lifecycle. The sum makes the two classifications
   incompatible for the same key. *)
Canonical Structure key_classificationR : cmra :=
  csumR (agreeR (leibnizO unit)) (exclR (leibnizO reservation_status)).
Definition key_classificationUR : ucmra := gmapUR KKey.t key_classificationR.
Definition fragUR : ucmra :=
  prodUR metaUR (prodUR specUR (prodUR statusUR key_classificationUR)).

Implicit Types (a : authO) (b : fragUR).

Local Definition proj_state a : gmap KKey.t KObjectV.t := fst a.
Local Definition proj_used_uid a : gset types.UID.t := snd a.

Local Definition proj_meta b : metaUR := fst b.
Local Definition proj_spec b : specUR := fst (snd b).
Local Definition proj_status b : statusUR := fst (snd (snd b)).
Local Definition proj_key_classification b : key_classificationUR := snd (snd (snd b)).

Local Definition valid_kauth a : Prop :=
  map_Forall (λ k obj,
    k = KObjectV.key obj ∧
    KObjectV.valid obj ∧
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∈ proj_used_uid a ∧
    (* No object's parent reference can speculatively point to uid that has never existed *)
    no_speculative_parent_reference (KObjectV.objectmeta obj) (proj_used_uid a) ∧
    map_Forall (λ k' obj',
      (* Each obj has unique uid *)
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') = (KObjectV.objectmeta obj').(ObjectMetaV.UID') → k = k'
    ) (proj_state a)
  ) (proj_state a).

Local Definition compatible_kfrag b a : Prop :=
  map_Forall (λ '(k, uid) '(dq, agree_meta),
    ∃ meta, agree_meta ≡ to_agree (A := leibnizO ObjectMetaV.t) meta ∧
      ✓ dq ∧
      ∃ obj, proj_state a !! k = Some obj ∧
        (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid ∧
        (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None ∧
        ObjectMetaV.without_resource_version (KObjectV.objectmeta obj) = meta
  ) (proj_meta b) ∧
  map_Forall (λ '(k, uid) '(dq, agree_spec),
    ∃ spec, agree_spec ≡ to_agree (A := leibnizO ObjectSpecV.t) spec ∧
      uid ∈ proj_used_uid a ∧
      ✓ dq ∧
      ∀ obj, proj_state a !! k = Some obj →
        (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
        (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
        KObjectV.spec obj = spec
  ) (proj_spec b) ∧
  map_Forall (λ '(k, uid) '(dq, agree_status),
    ∃ status, agree_status ≡ to_agree (A := leibnizO ObjectStatusV.t) status ∧
      uid ∈ proj_used_uid a ∧
      ✓ dq ∧
      ∀ obj, proj_state a !! k = Some obj →
        (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
        (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
        KObjectV.status obj = status
  ) (proj_status b) ∧
  map_Forall (λ k (classification : key_classificationR),
    ✓ classification ∧
    match classification with
    | Cinl _ => ¬ reserved_key_pred k
    | Cinr (Excl status) =>
          reserved_key_pred k ∧
          match status with
          | Available => proj_state a !! k = None
          | Occupied uid =>
              ∃ obj,
                proj_state a !! k = Some obj ∧
                (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid ∧
                (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None
          | Deleting uid =>
              proj_state a !! k = None ∨
              ∃ obj,
                proj_state a !! k = Some obj ∧
                (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid ∧
                (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') ≠ None
          end
    | _ => False
    end
  ) (proj_key_classification b).

Local Definition view_rel_raw (n: nat) a b :=
  valid_kauth a ∧ compatible_kfrag b a.

Local Lemma view_rel_raw_mono n1 n2 a1 a2 b1 b2 :
  view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  (n2 ≤ n1)%nat →
  view_rel_raw n2 a2 b2.
Proof.
  intros [Hvalid [Hmeta [Hspec [Hstatus Hclassification]]]] Ha Hb _.
  destruct a1 as [state1 used1], a2 as [state2 used2].
  simpl in *.
  destruct Ha as [Hstate Hused].
  assert (Hstate_eqv : state1 ≡ state2).
  { apply (proj2 (discrete_iff n2 state1 state2)).
    exact Hstate.
  }
  assert (Hstate_eq : state1 = state2).
  { change ((state1 : gmap KKey.t (leibnizO KObjectV.t)) =
            (state2 : gmap KKey.t (leibnizO KObjectV.t))).
    apply map_eq. intros k.
    pose proof (proj1 (map_equiv_iff state1 state2) Hstate_eqv k) as Hlookup_eqv.
    apply leibniz_equiv in Hlookup_eqv. done.
  }
  subst state2.
  assert (Hused_eqv : used1 ≡ used2).
  { apply (proj2 (discrete_iff n2 used1 used2)).
    exact Hused.
  }
  assert (Hused_elem : ∀ uid, uid ∈ used1 ↔ uid ∈ used2).
  { exact (proj1 (set_equiv used1 used2) Hused_eqv). }
  apply pair_includedN in Hb as [Hmeta_incl Hrest].
  apply pair_includedN in Hrest as [Hspec_incl Hrest].
  apply pair_includedN in Hrest as [Hstatus_incl Hclassification_incl].
  split.
  { rewrite /valid_kauth.
    rewrite map_Forall_lookup.
    intros k obj Hlookup.
    pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup) as Hobj_valid.
    destruct Hobj_valid as (Hkey & Hwf & Huid_in & Hno_spec & Huniq).
    split_and!; [done|done| | |done].
    - apply (proj1 (Hused_elem _)). done.
    - intros kind name uid Hparent.
      apply (proj1 (Hused_elem uid)).
      eapply Hno_spec. done.
  }
  split.
  - rewrite map_Forall_lookup.
    intros [k uid] [dq2 agree2] Hlookup2.
    destruct (lookup_includedN n2 (proj_meta b2) (proj_meta b1)) as [Hlookup_incl _].
    specialize (Hlookup_incl Hmeta_incl (k, uid)).
    rewrite Hlookup2 in Hlookup_incl.
    destruct (Some_includedN_is_Some _ _ _ Hlookup_incl) as [da1 Hlookup1].
    destruct da1 as [dq1 agree1].
    destruct (Hmeta _ _ Hlookup1) as (meta & Hagree1 & Hvdq1 & Hobj).
    rewrite Hlookup1 in Hlookup_incl.
    assert (Hval1_n2 :
      ✓{n2} (Some (dq1, agree1) : option (dfrac * agree (leibnizO ObjectMetaV.t)))).
    { simpl. apply cmra_valid_validN.
      apply pair_valid. split; [done|].
      rewrite Hagree1. done.
    }
    assert (Hval2_n2 :
      ✓{n2} (Some (dq2, agree2) : option (dfrac * agree (leibnizO ObjectMetaV.t)))).
    { eapply cmra_validN_includedN.
      - exact Hval1_n2.
      - exact Hlookup_incl.
    }
    assert (Hvdq2_n2 : ✓{n2} dq2).
    { apply (proj1 (pair_validN dq2 agree2 n2)).
      simpl in Hval2_n2. done.
    }
    assert (Hvdq2 : ✓ dq2).
    { by apply (proj2 (cmra_discrete_valid_iff n2 dq2)). }
    pose proof (Some_pair_includedN _ _ _ _ _ Hlookup_incl) as [_ Hagree_opt_incl].
    pose proof (proj1 (Some_includedN_total n2 agree2 agree1) Hagree_opt_incl) as Hagree_incl.
    assert (Hagree1_n2 : ✓{n2} agree1).
    { rewrite Hagree1. done. }
    pose proof (agree_valid_includedN n2 agree2 agree1 Hagree1_n2 Hagree_incl)
      as Hagree2_n2.
    exists meta.
    split.
    + apply (proj2 (discrete_iff n2 agree2
        (to_agree (A := leibnizO ObjectMetaV.t) meta))).
      etrans; [exact Hagree2_n2|exact (Hagree1 n2)].
    + split; [exact Hvdq2|exact Hobj].
  - split.
    + rewrite map_Forall_lookup.
      intros [k uid] [dq2 agree2] Hlookup2.
      destruct (lookup_includedN n2 (proj_spec b2) (proj_spec b1)) as [Hlookup_incl _].
      specialize (Hlookup_incl Hspec_incl (k, uid)).
      rewrite Hlookup2 in Hlookup_incl.
      destruct (Some_includedN_is_Some _ _ _ Hlookup_incl) as [da1 Hlookup1].
      destruct da1 as [dq1 agree1].
      destruct (Hspec _ _ Hlookup1) as (spec & Hagree1 & Huid_in & Hvdq1 & Hspec_obj).
      rewrite Hlookup1 in Hlookup_incl.
      assert (Hval1_n2 :
        ✓{n2} (Some (dq1, agree1) : option (dfrac * agree (leibnizO ObjectSpecV.t)))).
      { simpl. apply cmra_valid_validN.
        apply pair_valid. split; [done|].
        rewrite Hagree1. done.
      }
      assert (Hval2_n2 :
        ✓{n2} (Some (dq2, agree2) : option (dfrac * agree (leibnizO ObjectSpecV.t)))).
      { eapply cmra_validN_includedN.
        - exact Hval1_n2.
        - exact Hlookup_incl.
      }
      assert (Hvdq2_n2 : ✓{n2} dq2).
      { apply (proj1 (pair_validN dq2 agree2 n2)).
        simpl in Hval2_n2. done.
      }
      assert (Hvdq2 : ✓ dq2).
      { by apply (proj2 (cmra_discrete_valid_iff n2 dq2)). }
      pose proof (Some_pair_includedN _ _ _ _ _ Hlookup_incl) as [_ Hagree_opt_incl].
      pose proof (proj1 (Some_includedN_total n2 agree2 agree1) Hagree_opt_incl) as Hagree_incl.
      assert (Hagree1_n2 : ✓{n2} agree1).
      { rewrite Hagree1. done. }
      pose proof (agree_valid_includedN n2 agree2 agree1 Hagree1_n2 Hagree_incl)
        as Hagree2_n2.
      exists spec.
      split.
      * apply (proj2 (discrete_iff n2 agree2
          (to_agree (A := leibnizO ObjectSpecV.t) spec))).
        etrans; [exact Hagree2_n2|exact (Hagree1 n2)].
      * split.
        { apply (proj1 (Hused_elem _)). exact Huid_in. }
        { split; [exact Hvdq2|exact Hspec_obj]. }
    + split.
      * rewrite map_Forall_lookup.
      intros [k uid] [dq2 agree2] Hlookup2.
      destruct (lookup_includedN n2 (proj_status b2) (proj_status b1)) as [Hlookup_incl _].
      specialize (Hlookup_incl Hstatus_incl (k, uid)).
      rewrite Hlookup2 in Hlookup_incl.
      destruct (Some_includedN_is_Some _ _ _ Hlookup_incl) as [da1 Hlookup1].
      destruct da1 as [dq1 agree1].
      destruct (Hstatus _ _ Hlookup1) as (status & Hagree1 & Huid_in & Hvdq1 & Hstatus_obj).
      rewrite Hlookup1 in Hlookup_incl.
      assert (Hval1_n2 :
        ✓{n2} (Some (dq1, agree1) : option (dfrac * agree (leibnizO ObjectStatusV.t)))).
      { simpl. apply cmra_valid_validN.
        apply pair_valid. split; [done|].
        rewrite Hagree1. done.
      }
      assert (Hval2_n2 :
        ✓{n2} (Some (dq2, agree2) : option (dfrac * agree (leibnizO ObjectStatusV.t)))).
      { eapply cmra_validN_includedN.
        - exact Hval1_n2.
        - exact Hlookup_incl.
      }
      assert (Hvdq2_n2 : ✓{n2} dq2).
      { apply (proj1 (pair_validN dq2 agree2 n2)).
        simpl in Hval2_n2. done.
      }
      assert (Hvdq2 : ✓ dq2).
      { by apply (proj2 (cmra_discrete_valid_iff n2 dq2)). }
      pose proof (Some_pair_includedN _ _ _ _ _ Hlookup_incl) as [_ Hagree_opt_incl].
      pose proof (proj1 (Some_includedN_total n2 agree2 agree1) Hagree_opt_incl) as Hagree_incl.
      assert (Hagree1_n2 : ✓{n2} agree1).
      { rewrite Hagree1. done. }
      pose proof (agree_valid_includedN n2 agree2 agree1 Hagree1_n2 Hagree_incl)
        as Hagree2_n2.
      exists status.
      split.
      { apply (proj2 (discrete_iff n2 agree2
          (to_agree (A := leibnizO ObjectStatusV.t) status))).
        etrans; [exact Hagree2_n2|exact (Hagree1 n2)]. }
      { split.
        { apply (proj1 (Hused_elem _)). exact Huid_in. }
        { split; [exact Hvdq2|exact Hstatus_obj]. } }
      * rewrite map_Forall_lookup.
        intros k classification2 Hlookup2.
        destruct (lookup_includedN n2 (proj_key_classification b2)
          (proj_key_classification b1)) as [Hlookup_incl _].
        specialize (Hlookup_incl Hclassification_incl k).
        rewrite Hlookup2 in Hlookup_incl.
        destruct (Some_includedN_is_Some _ _ _ Hlookup_incl) as
          [classification1 Hlookup1].
        destruct (Hclassification _ _ Hlookup1) as
          [Hvalid1 Hcompatible].
        rewrite Hlookup1 in Hlookup_incl.
        assert (Hvalid2 : ✓ classification2).
        { assert (Hoptvalid2 :
            ✓{n2} (Some classification2 : option key_classificationR)).
          { assert (Hoptvalid1 :
              ✓{n2} (Some classification1 : option key_classificationR)).
            { simpl. apply cmra_valid_validN. exact Hvalid1. }
            eapply cmra_validN_includedN.
            - exact Hoptvalid1.
            - exact Hlookup_incl. }
          simpl in Hoptvalid2.
          apply (proj2 (cmra_discrete_valid_iff n2 classification2)).
          exact Hoptvalid2. }
        split; [exact Hvalid2|].
        apply Some_csum_includedN in Hlookup_incl.
        destruct Hlookup_incl as
          [Hinvalid|[(agree2 & agree1 & Heq2 & Heq1 & Hincluded)|
            (excl2 & excl1 & Heq2 & Heq1 & Hincluded)]].
        { rewrite Hinvalid in Hvalid1. exact (False_rect _ Hvalid1). }
        { subst classification2 classification1. exact Hcompatible. }
        { subst classification2 classification1.
          destruct excl1 as [status1|]; [|done].
          destruct excl2 as [status2|]; [|done].
          apply Excl_includedN in Hincluded.
          apply leibniz_equiv in Hincluded. subst status2.
          exact Hcompatible. }
Qed.

Local Lemma view_rel_raw_valid n a b :
  view_rel_raw n a b → ✓{n} b.
Proof.
  intros [_ [Hmeta [Hspec [Hstatus Hclassification]]]].
  apply pair_validN. split.
  - intros [k uid].
    destruct (proj_meta b !! (k, uid)) as [[dq agree_meta]|] eqn:Hlookup.
    + pose proof (map_Forall_lookup_1 _ _ _ _ Hmeta Hlookup) as Hmeta_i.
      simpl in Hmeta_i.
      destruct Hmeta_i as (meta & Hagree & Hvdq & _).
      rewrite Hlookup.
      apply pair_validN. split.
      * apply cmra_valid_validN. done.
      * rewrite Hagree. done.
    + rewrite Hlookup. done.
  - apply pair_validN. split.
    + intros [k uid].
      destruct (proj_spec b !! (k, uid)) as [[dq agree_spec]|] eqn:Hlookup.
      * pose proof (map_Forall_lookup_1 _ _ _ _ Hspec Hlookup) as Hspec_i.
        simpl in Hspec_i.
        destruct Hspec_i as (spec & Hagree & _ & Hvdq & _).
        rewrite Hlookup.
        apply pair_validN. split.
        { apply cmra_valid_validN. done. }
        { rewrite Hagree. done. }
      * rewrite Hlookup. done.
    + apply pair_validN. split.
      * intros [k uid].
        destruct (proj_status b !! (k, uid)) as [[dq agree_status]|] eqn:Hlookup.
        { pose proof (map_Forall_lookup_1 _ _ _ _ Hstatus Hlookup) as Hstatus_i.
        simpl in Hstatus_i.
        destruct Hstatus_i as (status & Hagree & _ & Hvdq & _).
        rewrite Hlookup.
        apply pair_validN. split.
        { apply cmra_valid_validN. done. }
          { rewrite Hagree. done. } }
        { rewrite Hlookup. done. }
      * intros k.
        destruct (proj_key_classification b !! k) as
          [classification|] eqn:Hlookup.
        { pose proof (map_Forall_lookup_1 _ _ _ _ Hclassification Hlookup)
            as Hclassification_i.
          destruct Hclassification_i as [Hclassification_valid _].
          rewrite Hlookup.
          apply cmra_valid_validN. exact Hclassification_valid.
        }
        { rewrite Hlookup. done. }
Qed.

Local Lemma view_rel_raw_unit n :
  ∃ a, view_rel_raw n a ε.
Proof.
  exists ((∅ : gmap KKey.t KObjectV.t), (∅ : gset types.UID.t)).
  split.
  { rewrite /valid_kauth map_Forall_lookup /=.
    intros i x Hlookup. rewrite lookup_empty in Hlookup. done. }
  rewrite /compatible_kfrag.
  split.
  { rewrite map_Forall_lookup. intros i x Hlookup.
    rewrite lookup_empty in Hlookup. done. }
  split.
  { rewrite map_Forall_lookup. intros i x Hlookup.
    rewrite lookup_empty in Hlookup. done. }
  split.
  { rewrite map_Forall_lookup. intros i x Hlookup.
    rewrite lookup_empty in Hlookup. done. }
  { rewrite map_Forall_lookup. intros i x Hlookup.
    rewrite lookup_empty in Hlookup. done. }
Qed.

Local Canonical Structure view_rel : view_rel authO fragUR :=
  ViewRel view_rel_raw view_rel_raw_mono
          view_rel_raw_valid view_rel_raw_unit.

Definition kview_auth dq a : viewR view_rel := ●V{dq} a.
Definition kview_frag b : viewR view_rel := ◯V b.
Notation "●K a" := (kview_auth 1 a) (at level 20).
Notation "◯K b" := (kview_frag b) (at level 20).

Definition mk_meta_frag (k: KKey.t) (uid: types.UID.t) (dq: dfrac) (m: ObjectMetaV.t) : fragUR :=
  ({[(k, uid) := (dq, to_agree (ObjectMetaV.without_resource_version m))]}, (∅, (∅, ∅))).
Definition mk_spec_frag (k: KKey.t) (uid: types.UID.t) (dq: dfrac) (s: ObjectSpecV.t) : fragUR :=
  (∅, ({[(k, uid) := (dq, to_agree s)]}, (∅, ∅))).
Definition mk_status_frag (k: KKey.t) (uid: types.UID.t) (dq: dfrac) (s: ObjectStatusV.t) : fragUR :=
  (∅, (∅, ({[(k, uid) := (dq, to_agree s)]}, ∅))).
Definition mk_reservation_frag (k: KKey.t) (status: reservation_status) : fragUR :=
  (∅, (∅, (∅,
    ({[k := Cinr (Excl status)]} : key_classificationUR)))).
Definition mk_unreserved_frag (k : KKey.t) : fragUR :=
  (∅, (∅, (∅,
    ({[k := Cinl (to_agree (A := leibnizO unit) ())]} : key_classificationUR)))).

Global Instance unreserved_classification_core_id :
  CoreId (Cinl (to_agree (A := leibnizO unit) ()) : key_classificationR).
Proof. apply Cinl_core_id. apply _. Qed.

Global Instance mk_unreserved_frag_core_id k : CoreId (mk_unreserved_frag k).
Proof.
  apply pair_core_id; first apply _.
  apply pair_core_id; first apply _.
  apply pair_core_id; first apply _.
  apply gmap_singleton_core_id.
  exact unreserved_classification_core_id.
Qed.

Local Lemma valid_agree_unit_eq (x : agreeR (leibnizO unit)) :
  ✓ x → x ≡ to_agree (A := leibnizO unit) ().
Proof.
  intros Hvalid.
  destruct (to_agree_uninj x Hvalid) as [[] Heq].
  symmetry. exact Heq.
Qed.

Lemma auth_valid a k obj:
  ✓ (●K a) →
  (proj_state a) !! k = Some obj →
  k = KObjectV.key obj ∧
  KObjectV.valid obj ∧
  (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∈ proj_used_uid a ∧
  no_speculative_parent_reference (KObjectV.objectmeta obj) (proj_used_uid a) ∧
  map_Forall (λ k' obj',
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta obj').(ObjectMetaV.UID') → k = k'
  ) (proj_state a).
Proof.
  intros Hvalid Hlookup.
  rewrite /kview_auth in Hvalid.
  pose proof (proj1 (view_auth_dfrac_valid view_rel 1 a) Hvalid) as [_ Hrel].
  specialize (Hrel 0%nat).
  change (view_rel_raw 0%nat a ε) in Hrel.
  destruct Hrel as [Hvalid_a _].
  rewrite /valid_kauth in Hvalid_a.
  pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid_a Hlookup) as Hobj_valid.
  exact Hobj_valid.
Qed.

Lemma auth_valid_forall a:
  ✓ (●K a) →
  ∀ k obj,
  (proj_state a) !! k = Some obj →
  k = KObjectV.key obj ∧
  KObjectV.valid obj ∧
  (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∈ proj_used_uid a ∧
  no_speculative_parent_reference (KObjectV.objectmeta obj) (proj_used_uid a) ∧
  map_Forall (λ k' obj',
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta obj').(ObjectMetaV.UID') → k = k'
  ) (proj_state a).
Proof.
  intros Hvalid k obj Hlookup.
  eapply (auth_valid a k obj); done.
Qed.

Lemma auth_frag_valid (n: nat) a b:
  ✓ (●K a ⋅ ◯K b) →
  ∀ n, view_rel_raw n a b.
Proof.
  intros Hvalid m.
  rewrite /kview_auth /kview_frag in Hvalid.
  pose proof (proj1 (view_both_dfrac_valid view_rel 1 a b) Hvalid) as [_ Hrel].
  specialize (Hrel m).
  exact Hrel.
Qed.

Lemma meta_valid k uid dq meta:
  ✓ (◯K (mk_meta_frag k uid dq meta)) →
  k.(KKey.Name') = meta.(ObjectMetaV.Name') ∧
  k.(KKey.Namespace') = meta.(ObjectMetaV.Namespace') ∧
  uid = meta.(ObjectMetaV.UID') ∧
  ObjectMetaV.valid k.(KKey.Kind') meta ∧
  meta.(ObjectMetaV.DeletionTimestamp') = None.
Proof.
  intros Hvalid.
  rewrite /kview_frag in Hvalid.
  pose proof (proj1 (view_frag_valid view_rel (mk_meta_frag k uid dq meta)) Hvalid 0%nat)
    as [a Hrel].
  destruct Hrel as [Hvalid_a [Hmeta _]].
	  assert (Hlookup :
	    proj_meta (mk_meta_frag k uid dq meta) !! (k, uid) =
	    Some (dq, to_agree (A := leibnizO ObjectMetaV.t)
	      (ObjectMetaV.without_resource_version meta))).
	  { rewrite /proj_meta /mk_meta_frag /= lookup_singleton_eq //. }
	  destruct (Hmeta _ _ Hlookup) as (meta0 & Hagree & _ & Hobj).
	  destruct Hobj as (obj & Hlookup_obj & Huid_obj & Hliving & Hobj_meta).
	  pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid_a Hlookup_obj) as Hobj_valid.
	  destruct Hobj_valid as (Hkey_obj & Hwf_obj & _ & _ & _).
	  assert (Hmeta_eqv : (ObjectMetaV.without_resource_version meta : leibnizO ObjectMetaV.t) ≡ meta0).
	  { apply (inj (to_agree : leibnizO ObjectMetaV.t → agree (leibnizO ObjectMetaV.t))).
	    exact Hagree.
	  }
	  apply leibniz_equiv in Hmeta_eqv.
	  assert (Hobj_meta_eq : ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta obj) meta).
	  { rewrite <- Hmeta_eqv in Hobj_meta. exact Hobj_meta. }
	  subst k.
	  split.
	  - rewrite /KObjectV.key /=.
	    exact (ObjectMetaV.equiv_except_resource_version_name _ _ Hobj_meta_eq).
	  - split.
	    + rewrite /KObjectV.key /=.
	      exact (ObjectMetaV.equiv_except_resource_version_namespace _ _ Hobj_meta_eq).
	    + split.
	      * rewrite <- (ObjectMetaV.equiv_except_resource_version_uid _ _ Hobj_meta_eq). symmetry. exact Huid_obj.
	      * split.
	        -- destruct obj; unfold KObjectV.valid in Hwf_obj;
	             destruct Hwf_obj as (_ & _ & Hwf_meta & _ & _);
	             eapply ObjectMetaV.equiv_except_resource_version_valid; done.
	        -- rewrite <-(ObjectMetaV.equiv_except_resource_version_deletion_timestamp
	             _ _ Hobj_meta_eq).
	           exact Hliving.
Qed.

Lemma auth_meta_valid a k uid dq meta:
	  ✓ (●K a ⋅ ◯K (mk_meta_frag k uid dq meta)) →
	  ∃ obj, (proj_state a) !! k = Some obj ∧
	    (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid ∧
	    ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta obj) meta ∧
	    meta.(ObjectMetaV.UID') ∈ proj_used_uid a.
Proof.
  intros Hvalid.
  pose proof (auth_frag_valid 0%nat a (mk_meta_frag k uid dq meta) Hvalid 0%nat)
    as Hrel.
  destruct Hrel as [Hvalid_a [Hmeta _]].
	  assert (Hlookup :
	    proj_meta (mk_meta_frag k uid dq meta) !! (k, uid) =
	    Some (dq, to_agree (A := leibnizO ObjectMetaV.t)
	      (ObjectMetaV.without_resource_version meta))).
	  { rewrite /proj_meta /mk_meta_frag /= lookup_singleton_eq //. }
	  destruct (Hmeta _ _ Hlookup) as (meta0 & Hagree & _ & Hobj).
	  destruct Hobj as (obj & Hlookup_obj & Huid_obj & _ & Hobj_meta).
	  pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid_a Hlookup_obj) as Hobj_valid.
	  destruct Hobj_valid as (_ & _ & Huid_in & _ & _).
	  assert (Hmeta_eqv : (ObjectMetaV.without_resource_version meta : leibnizO ObjectMetaV.t) ≡ meta0).
	  { apply (inj (to_agree : leibnizO ObjectMetaV.t → agree (leibnizO ObjectMetaV.t))).
	    exact Hagree.
	  }
	  apply leibniz_equiv in Hmeta_eqv.
	  assert (Hobj_meta_eq : ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta obj) meta).
	  { rewrite <- Hmeta_eqv in Hobj_meta. exact Hobj_meta. }
	  exists obj. split_and!.
	  - exact Hlookup_obj.
	  - exact Huid_obj.
	  - exact Hobj_meta_eq.
	  - rewrite <- (ObjectMetaV.equiv_except_resource_version_uid _ _ Hobj_meta_eq). done.
Qed.

Lemma auth_meta_living a k uid dq meta :
  ✓ (●K a ⋅ ◯K (mk_meta_frag k uid dq meta)) →
  ∃ obj, proj_state a !! k = Some obj ∧
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid ∧
    (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None.
Proof.
  intros Hvalid.
  pose proof (auth_frag_valid 0%nat a (mk_meta_frag k uid dq meta)
    Hvalid 0%nat) as [_ [Hmeta _]].
  assert (Hlookup :
      proj_meta (mk_meta_frag k uid dq meta) !! (k, uid) =
        Some (dq, to_agree (A := leibnizO ObjectMetaV.t)
          (ObjectMetaV.without_resource_version meta))).
  { rewrite /proj_meta /mk_meta_frag /= lookup_singleton_eq //. }
  destruct (Hmeta _ _ Hlookup) as
    (meta' & Hagree & Hvdq & obj & Hobj & Huid & Hliving & Hmeta').
  exists obj. split_and!; done.
Qed.

Lemma meta_meta_valid k uid dq1 meta1 dq2 meta2:
	  ✓ (◯K (mk_meta_frag k uid dq1 meta1) ⋅
	     ◯K (mk_meta_frag k uid dq2 meta2)) →
	  ✓ (dq1 ⋅ dq2) ∧ ObjectMetaV.equiv_except_resource_version meta1 meta2.
Proof.
  intros Hvalid.
  rewrite /kview_frag -view_frag_op in Hvalid.
  pose proof (proj1
    (view_frag_valid view_rel
      (mk_meta_frag k uid dq1 meta1 ⋅ mk_meta_frag k uid dq2 meta2))
    Hvalid 0%nat) as [a Hrel].
  destruct Hrel as [_ [Hmeta _]].
	  assert (Hlookup :
	    proj_meta (mk_meta_frag k uid dq1 meta1 ⋅ mk_meta_frag k uid dq2 meta2) !! (k, uid) =
	    Some ((dq1, to_agree (A := leibnizO ObjectMetaV.t)
	            (ObjectMetaV.without_resource_version meta1)) ⋅
	          (dq2, to_agree (A := leibnizO ObjectMetaV.t)
	            (ObjectMetaV.without_resource_version meta2)))).
	  { rewrite /proj_meta /mk_meta_frag /= lookup_op.
	    rewrite lookup_singleton_eq lookup_singleton_eq Some_op_opM //. }
  destruct (Hmeta _ _ Hlookup) as (meta & Hagree & Hvdq & _).
  split.
  - exact Hvdq.
	  - change ((ObjectMetaV.without_resource_version meta1 : leibnizO ObjectMetaV.t) =
	      (ObjectMetaV.without_resource_version meta2 : leibnizO ObjectMetaV.t)).
	    apply to_agree_op_inv_L.
    rewrite Hagree. done.
Qed.

Lemma meta_meta_false k1 uid1 meta1 k2 uid2 meta2 :
  k1 = k2 →
  ✓ (◯K (mk_meta_frag k1 uid1 1 meta1) ⋅
     ◯K (mk_meta_frag k2 uid2 1 meta2)) →
  False.
Proof.
  intros -> Hvalid.
  destruct (decide (uid1 = uid2)) as [->|Huid_ne].
  - pose proof (meta_meta_valid k2 uid2 1 meta1 1 meta2 Hvalid) as [Hvdq _].
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l (DfracOwn 1) 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt.
    apply Hlt.
    done.
  - rewrite /kview_frag -view_frag_op in Hvalid.
    pose proof (proj1
      (view_frag_valid view_rel
        (mk_meta_frag k2 uid1 1 meta1 ⋅ mk_meta_frag k2 uid2 1 meta2))
      Hvalid 0%nat) as [a Hrel].
    destruct Hrel as [_ [Hmeta _]].
    assert (Hlookup1 :
	      proj_meta (mk_meta_frag k2 uid1 1 meta1 ⋅ mk_meta_frag k2 uid2 1 meta2) !! (k2, uid1) =
	      Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	        (ObjectMetaV.without_resource_version meta1))).
    { rewrite /proj_meta /mk_meta_frag /= lookup_op.
      assert (Hpair_ne : (k2, uid2) ≠ (k2, uid1)).
      { intros Hpair.
        apply Huid_ne.
        now inversion Hpair. }
      rewrite lookup_singleton_eq.
	      rewrite (lookup_singleton_ne (k2, uid2) (k2, uid1)
	        (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	          (ObjectMetaV.without_resource_version meta2)) Hpair_ne).
      rewrite right_id //.
    }
    assert (Hlookup2 :
	      proj_meta (mk_meta_frag k2 uid1 1 meta1 ⋅ mk_meta_frag k2 uid2 1 meta2) !! (k2, uid2) =
	      Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	        (ObjectMetaV.without_resource_version meta2))).
    { rewrite /proj_meta /mk_meta_frag /= lookup_op.
      assert (Hpair_ne : (k2, uid1) ≠ (k2, uid2)).
      { intros Hpair.
        apply Huid_ne.
        now inversion Hpair. }
	      rewrite (lookup_singleton_ne (k2, uid1) (k2, uid2)
	        (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	          (ObjectMetaV.without_resource_version meta1)) Hpair_ne).
      rewrite lookup_singleton_eq.
      rewrite left_id //.
    }
    destruct (Hmeta _ _ Hlookup1) as (meta1' & _ & _ & Hobj1).
    destruct (Hmeta _ _ Hlookup2) as (meta2' & _ & _ & Hobj2).
    destruct Hobj1 as (obj1 & Hlookup_obj1 & Huid_obj1 & _).
    destruct Hobj2 as (obj2 & Hlookup_obj2 & Huid_obj2 & _).
    rewrite Hlookup_obj1 in Hlookup_obj2.
    injection Hlookup_obj2 as <-.
    rewrite Huid_obj1 in Huid_obj2.
    contradiction.
Qed.

Lemma auth_spec_valid a k uid dq spec:
  ✓ (●K a ⋅ ◯K (mk_spec_frag k uid dq spec)) →
  ∀ obj, (proj_state a) !! k = Some obj →
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
    (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
    (KObjectV.spec obj) = spec.
Proof.
  intros Hvalid obj Hlookup_obj Huid_obj Hliving.
  pose proof (auth_frag_valid 0%nat a (mk_spec_frag k uid dq spec) Hvalid 0%nat)
    as Hrel.
  destruct Hrel as [_ [_ [Hspec _]]].
  assert (Hlookup :
    proj_spec (mk_spec_frag k uid dq spec) !! (k, uid) =
    Some (dq, to_agree (A := leibnizO ObjectSpecV.t) spec)).
  { rewrite /proj_spec /mk_spec_frag /= lookup_singleton_eq //. }
  destruct (Hspec _ _ Hlookup) as (spec0 & Hagree & _ & _ & Hspec_obj).
  assert (Hspec_eqv : (spec : leibnizO ObjectSpecV.t) ≡ spec0).
  { apply (inj (to_agree : leibnizO ObjectSpecV.t → agree (leibnizO ObjectSpecV.t))).
    exact Hagree.
  }
  apply leibniz_equiv in Hspec_eqv.
  subst spec0.
  eapply Hspec_obj; eauto.
Qed.

Lemma auth_reservation_valid a k status:
  ✓ (●K a ⋅ ◯K (mk_reservation_frag k status)) →
  reserved_key_pred k ∧
  match status with
  | Available => proj_state a !! k = None
  | Occupied uid =>
      ∃ obj,
        proj_state a !! k = Some obj ∧
        (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid ∧
        (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None
  | Deleting uid =>
      proj_state a !! k = None ∨
      ∃ obj,
        proj_state a !! k = Some obj ∧
        (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid ∧
        (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') ≠ None
  end.
Proof.
  intros Hvalid.
  pose proof (auth_frag_valid 0%nat a (mk_reservation_frag k status)
    Hvalid 0%nat) as Hrel.
  destruct Hrel as [_ [_ [_ [_ Hclassification]]]].
  assert (Hlookup :
    proj_key_classification (mk_reservation_frag k status) !! k =
      Some (Cinr (Excl status))).
  { rewrite /proj_key_classification /mk_reservation_frag /= lookup_singleton_eq //. }
  destruct (Hclassification _ _ Hlookup) as [_ Hcompatible].
  exact Hcompatible.
Qed.

Lemma meta_reservation_valid k uid dq meta status :
  ✓{0} (◯K (mk_meta_frag k uid dq meta) ⋅
    ◯K (mk_reservation_frag k status)) →
  status = Occupied uid.
Proof.
  intros Hvalid.
  rewrite /kview_frag -view_frag_op in Hvalid.
  pose proof (proj1 (view_frag_validN view_rel 0%nat
    (mk_meta_frag k uid dq meta ⋅ mk_reservation_frag k status))
    Hvalid) as [a Hrel].
  destruct Hrel as [_ [Hmeta [_ [_ Hreservation]]]].
  assert (Hmeta_lookup :
      proj_meta (mk_meta_frag k uid dq meta ⋅
        mk_reservation_frag k status) !! (k, uid) =
      Some (dq, to_agree (A := leibnizO ObjectMetaV.t)
        (ObjectMetaV.without_resource_version meta))).
  { rewrite /proj_meta /mk_meta_frag /mk_reservation_frag /=
      lookup_op lookup_singleton_eq lookup_empty right_id //. }
  destruct (Hmeta _ _ Hmeta_lookup) as
    (meta' & _ & _ & obj & Hobj & Hobj_uid & Hobj_living & _).
  assert (Hreservation_lookup :
      proj_key_classification (mk_meta_frag k uid dq meta ⋅
        mk_reservation_frag k status) !! k =
      Some (Cinr (Excl status))).
  { rewrite /proj_key_classification /mk_meta_frag /mk_reservation_frag /=.
    rewrite left_id lookup_singleton_eq //. }
  destruct (Hreservation _ _ Hreservation_lookup) as
    [_ [_ Hstatus]].
  destruct status as [|reserved_uid|reserved_uid].
  - rewrite Hobj in Hstatus. discriminate.
  - destruct Hstatus as (obj' & Hobj' & Hobj'_uid & _).
    rewrite Hobj in Hobj'. injection Hobj' as <-.
    f_equal. congruence.
  - destruct Hstatus as [Habsent|(obj' & Hobj' & _ & Hterminating)].
    + rewrite Hobj in Habsent. discriminate.
    + rewrite Hobj in Hobj'. injection Hobj' as <-.
      contradiction.
Qed.

Lemma unreserved_frag_valid n k :
  ✓{n} (◯K (mk_unreserved_frag k)) →
  ¬ reserved_key_pred k.
Proof.
  intros Hvalid.
  pose proof (proj1 (view_frag_validN view_rel n
    (mk_unreserved_frag k)) Hvalid) as [a Hrel].
  destruct Hrel as [_ [_ [_ [_ Hclassification]]]].
  assert (Hlookup :
    proj_key_classification (mk_unreserved_frag k) !! k =
      Some (Cinl (to_agree (A := leibnizO unit) ()))).
  { rewrite /proj_key_classification /mk_unreserved_frag /= lookup_singleton_eq //. }
  destruct (Hclassification _ _ Hlookup) as [_ Hcompatible].
  exact Hcompatible.
Qed.

Definition valid_k_uid_obj k uid obj: Prop :=
  k = KObjectV.key obj ∧
  uid = (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∧
  KObjectV.valid obj.

Lemma extend_used_uid a uid :
  ●K a ~~>
    ●K (proj_state a, proj_used_uid a ∪ {[uid]}).
Proof.
  apply view_update_auth.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  split.
  - rewrite /valid_kauth map_Forall_lookup in Hvalid |- *.
    intros key obj Hlookup.
    destruct (Hvalid key obj Hlookup) as
      (Hkey & Hobj_valid & Huid_used & Hno_spec & Huid_unique).
    split_and!; try done.
    + apply elem_of_union_l. exact Huid_used.
    + intros kind name parent_uid Hparent.
      apply elem_of_union_l.
      exact (Hno_spec kind name parent_uid Hparent).
  - split.
    + rewrite map_Forall_lookup in Hmeta |- *.
      intros [key frag_uid] [dq agree_meta] Hlookup.
      exact (Hmeta (key, frag_uid) (dq, agree_meta) Hlookup).
    + split.
      * rewrite map_Forall_lookup in Hspec |- *.
        intros [key frag_uid] [dq agree_spec] Hlookup.
        destruct (Hspec (key, frag_uid) (dq, agree_spec) Hlookup) as
          (spec & Hagree & Huid & Hdq & Hspec_obj).
        exists spec. split_and!; try done. apply elem_of_union_l. exact Huid.
      * split.
        -- rewrite map_Forall_lookup in Hstatus |- *.
           intros [key frag_uid] [dq agree_status] Hlookup.
           destruct (Hstatus (key, frag_uid) (dq, agree_status) Hlookup) as
             (status & Hagree & Huid & Hdq & Hstatus_obj).
           exists status. split_and!; try done. apply elem_of_union_l. exact Huid.
        -- rewrite map_Forall_lookup in Hreservation |- *.
           intros key classification Hlookup.
           exact (Hreservation key classification Hlookup).
Qed.

Lemma create_kobj a k uid obj:
  (proj_state a) !! k = None →
  ¬ reserved_key_pred k →
  uid ∉ (proj_used_uid a) →
  valid_k_uid_obj k uid obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
  no_speculative_parent_reference (KObjectV.objectmeta obj) (proj_used_uid a) →
  ●K a ~~>
    (●K ((<[k := obj]> (proj_state a)), ((proj_used_uid a) ∪ {[uid]})) ⋅
        ◯K (mk_meta_frag k uid 1 (KObjectV.objectmeta obj)) ⋅
        ◯K (mk_spec_frag k uid 1 (KObjectV.spec obj)) ⋅
        ◯K (mk_status_frag k uid 1 (KObjectV.status obj))).
Proof.
  intros Hak Hnot_reserved Huid_fresh Hkuid_obj Hdeletion_timestamp Hno_spec.
  destruct Hkuid_obj as (Hkey_obj & Huid_obj & Hwf_obj).
  rewrite -!assoc -!view_frag_op.
  apply view_update_alloc.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  assert (Hmeta_bf_none : proj_meta bf !! (k, uid) = None).
  { destruct (proj_meta bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    destruct (Hmeta _ _ Hbf) as (meta0 & _ & _ & Hobj0).
    destruct Hobj0 as (obj0 & Hlookup_obj0 & _ & _).
    rewrite Hak in Hlookup_obj0. done.
  }
  assert (Hspec_bf_none : proj_spec bf !! (k, uid) = None).
  { destruct (proj_spec bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    destruct (Hspec _ _ Hbf) as (_ & _ & Huid_in & _ & _).
    apply Huid_fresh. done.
  }
  assert (Hstatus_bf_none : proj_status bf !! (k, uid) = None).
  { destruct (proj_status bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    destruct (Hstatus _ _ Hbf) as (_ & _ & Huid_in & _ & _).
    apply Huid_fresh. done.
  }

  split.
  - eapply map_Forall_lookup_2.
    intros k' obj' Hlookup_new.
    destruct (decide (k' = k)) as [->|Hneq_k'].
    + rewrite lookup_insert in Hlookup_new.
      destruct (decide (k = k)) as [_|Hneq_k]; [|done].
      inversion Hlookup_new. subst obj'.
      split_and!. all: try done.
      * rewrite Huid_obj. apply elem_of_union_r, elem_of_singleton_2. done.
      * intros kind name uid0 Hparent.
        apply elem_of_union_l.
        eapply Hno_spec. done.
      * eapply map_Forall_lookup_2.
        intros k'' obj'' Hlookup_new2 Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq_k''].
        { done. }
        simpl in Hlookup_new2.
        apply lookup_insert_Some in Hlookup_new2.
        destruct Hlookup_new2 as [[Hk_eq _]|[Hk_neq Hlookup_old2]].
        { congruence. }
        pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup_old2) as Hkobj_old2.
        destruct Hkobj_old2 as (_ & _ & Huid_in_old2 & _ & _).
        exfalso.
        apply Huid_fresh.
        rewrite Huid_obj.
        rewrite <- Huid_eq in Huid_in_old2.
        done.
    + simpl in Hlookup_new.
      apply lookup_insert_Some in Hlookup_new.
      destruct Hlookup_new as [[Hk_eq _]|[Hk_neq Hlookup_old]].
      { congruence. }
      pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup_old) as Hkobj_old.
      destruct Hkobj_old as (Hkey_old & Hwf_old & Huid_old_in & Hno_spec_old & Huniq_old).
      split_and!. all: try done.
      * apply elem_of_union_l. exact Huid_old_in.
      * intros kind name uid0 Hparent.
        apply elem_of_union_l.
        eapply Hno_spec_old. done.
      * eapply map_Forall_lookup_2.
        intros k'' obj'' Hlookup_new2 Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq_k''].
        { rewrite lookup_insert in Hlookup_new2.
          destruct (decide (k = k)) as [_|Hneq_k]; [|done].
          inversion Hlookup_new2. subst obj''.
          exfalso.
          apply Huid_fresh.
          rewrite <- Huid_obj in Huid_eq.
          rewrite Huid_eq in Huid_old_in.
          done.
        }
        simpl in Hlookup_new2.
        apply lookup_insert_Some in Hlookup_new2.
        destruct Hlookup_new2 as [[Hk_eq2 _]|[Hk_neq2 Hlookup_old2]].
        { congruence. }
        eapply Huniq_old; done.
  - split_and!.
    + intros [k' uid'] [dq' agree_meta'] Hlookup_new.
      destruct (decide ((k', uid') = (k, uid))) as [Heq_pair|Hneq_pair].
      * inversion Heq_pair. subst k' uid'.
        rewrite /proj_meta /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
        rewrite (right_id (A := metaUR) (∅ : metaUR)) in Hlookup_new.
	        rewrite (lookup_op
	          (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	             (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]} : metaUR) ⋅ ∅)
	          bf.1 (k, uid)) in Hlookup_new.
	        rewrite (lookup_op
	          ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	             (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]} : metaUR)
	          (∅ : metaUR) (k, uid)) in Hlookup_new.
        rewrite lookup_singleton_eq lookup_empty right_id Hmeta_bf_none right_id in Hlookup_new.
        inversion Hlookup_new. subst dq' agree_meta'.
	        exists (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)).
	        split_and!. all: try done.
        exists obj. split_and!;
          [rewrite lookup_insert_eq; done
          |symmetry; done
          |exact Hdeletion_timestamp
          |done].
      * assert (Hlookup_old : proj_meta bf !! (k', uid') = Some (dq', agree_meta')).
        { rewrite /proj_meta /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
          rewrite (right_id (A := metaUR) (∅ : metaUR)) in Hlookup_new.
	          assert (Hsingle_none :
	            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	              (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]}
	              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectMetaV.t))) !!
	            (k', uid') = None).
          { apply lookup_singleton_ne. done. }
	          rewrite (lookup_op
	            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	               (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]} : metaUR) ⋅ ∅)
	            bf.1 (k', uid')) in Hlookup_new.
	          rewrite (lookup_op
	            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	               (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]} : metaUR)
	            (∅ : metaUR) (k', uid')) in Hlookup_new.
          rewrite Hsingle_none lookup_empty in Hlookup_new.
          simpl in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectMetaV.t))) None) in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectMetaV.t))) None) in Hlookup_new.
          done.
        }
        destruct (Hmeta _ _ Hlookup_old) as (meta' & Hagree' & Hvdq' & Hobj').
        destruct Hobj' as
          (obj0 & Hlookup_obj0 & Huid_obj0 & Hliving_obj0 & Hmeta_obj0).
        assert (Hneq_k : k' ≠ k).
        { intros Hk'. subst k'.
          rewrite Hak in Hlookup_obj0. done.
        }
        exists meta'. split_and!. all: try done.
        exists obj0. split_and!. all: try done.
        rewrite lookup_insert_ne; done.
    + intros [k' uid'] [dq' agree_spec'] Hlookup_new.
      destruct (decide ((k', uid') = (k, uid))) as [Heq_pair|Hneq_pair].
      * inversion Heq_pair. subst k' uid'.
        rewrite /proj_spec /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
        rewrite (lookup_op
          ((∅ : specUR) ⋅
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
               (KObjectV.spec obj))]} : specUR) ⋅ ∅))
          bf.2.1 (k, uid)) in Hlookup_new.
        rewrite (lookup_op
          (∅ : specUR)
          (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
              (KObjectV.spec obj))]} : specUR) ⋅ ∅) (k, uid)) in Hlookup_new.
        rewrite lookup_empty in Hlookup_new.
        rewrite (left_id
          (A := option (dfrac * agree (leibnizO ObjectSpecV.t))) None) in Hlookup_new.
        rewrite (lookup_op
          ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
             (KObjectV.spec obj))]} : specUR)
          (∅ : specUR) (k, uid)) in Hlookup_new.
        rewrite lookup_singleton_eq lookup_empty right_id Hspec_bf_none right_id in Hlookup_new.
        inversion Hlookup_new. subst dq' agree_spec'.
        exists (KObjectV.spec obj). split_and!. all: try done.
        { rewrite Huid_obj. apply elem_of_union_r.
          apply elem_of_singleton_2. done. }
        intros obj0 Hlookup_obj0 Huid_obj0 Hliving_obj0.
        rewrite lookup_insert in Hlookup_obj0.
        destruct (decide (k = k)) as [_|Hneq_k]; [|done].
        inversion Hlookup_obj0. subst obj0. done.
      * assert (Hlookup_old : proj_spec bf !! (k', uid') = Some (dq', agree_spec')).
        { rewrite /proj_spec /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
          assert (Hsingle_none :
            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
              (KObjectV.spec obj))]}
              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectSpecV.t))) !!
            (k', uid') = None).
          { apply lookup_singleton_ne. done. }
          rewrite (lookup_op
            ((∅ : specUR) ⋅
              (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
                 (KObjectV.spec obj))]} : specUR) ⋅ ∅))
            bf.2.1 (k', uid')) in Hlookup_new.
          rewrite (lookup_op
            (∅ : specUR)
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
                (KObjectV.spec obj))]} : specUR) ⋅ ∅) (k', uid')) in Hlookup_new.
          rewrite lookup_empty in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectSpecV.t))) None) in Hlookup_new.
          rewrite (lookup_op
            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
               (KObjectV.spec obj))]} : specUR)
            (∅ : specUR) (k', uid')) in Hlookup_new.
          rewrite Hsingle_none lookup_empty in Hlookup_new.
          simpl in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectSpecV.t))) None) in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectSpecV.t))) None) in Hlookup_new.
          done.
        }
        destruct (Hspec _ _ Hlookup_old) as (spec' & Hagree' & Huid_in' & Hvdq' & Hspec').
        exists spec'. split_and!. all: try done.
        { apply elem_of_union_l. done. }
        intros obj0 Hlookup_obj0 Huid_obj0.
        destruct (decide (k' = k)) as [->|Hneq_k'].
        { rewrite lookup_insert in Hlookup_obj0.
          destruct (decide (k = k)) as [_|Hneq_k]; [|done].
          inversion Hlookup_obj0. subst obj0.
          exfalso.
          apply Hneq_pair.
          rewrite <- Huid_obj in Huid_obj0.
          congruence.
        }
        simpl in Hlookup_obj0.
        apply lookup_insert_Some in Hlookup_obj0.
        destruct Hlookup_obj0 as [[Hk_eq _]|[Hk_neq Hlookup_old_obj0]].
        { congruence. }
        eapply Hspec'; done.
    + intros [k' uid'] [dq' agree_status'] Hlookup_new.
      destruct (decide ((k', uid') = (k, uid))) as [Heq_pair|Hneq_pair].
      * inversion Heq_pair. subst k' uid'.
        rewrite /proj_status /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
        rewrite (lookup_op
          ((∅ : statusUR) ⋅
            ((∅ : statusUR) ⋅
              ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
                 (KObjectV.status obj))]} : statusUR)))
          bf.2.2.1 (k, uid)) in Hlookup_new.
        rewrite (lookup_op
          (∅ : statusUR)
          ((∅ : statusUR) ⋅
            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
               (KObjectV.status obj))]} : statusUR)) (k, uid)) in Hlookup_new.
        rewrite lookup_empty in Hlookup_new.
        rewrite (left_id
          (A := option (dfrac * agree (leibnizO ObjectStatusV.t))) None) in Hlookup_new.
        rewrite (lookup_op
          (∅ : statusUR)
          ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
             (KObjectV.status obj))]} : statusUR) (k, uid)) in Hlookup_new.
        rewrite lookup_empty in Hlookup_new.
        rewrite (left_id
          (A := option (dfrac * agree (leibnizO ObjectStatusV.t))) None) in Hlookup_new.
        rewrite lookup_singleton_eq Hstatus_bf_none right_id in Hlookup_new.
        inversion Hlookup_new. subst dq' agree_status'.
        exists (KObjectV.status obj). split_and!. all: try done.
        { rewrite Huid_obj. apply elem_of_union_r.
          apply elem_of_singleton_2. reflexivity. }
        intros obj0 Hlookup_obj0 Huid_obj0.
        rewrite lookup_insert in Hlookup_obj0.
        destruct (decide (k = k)) as [_|Hneq_k]; [|done].
        inversion Hlookup_obj0. subst obj0. done.
      * assert (Hlookup_old : proj_status bf !! (k', uid') = Some (dq', agree_status')).
        { rewrite /proj_status /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
          assert (Hsingle_none :
            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
              (KObjectV.status obj))]}
              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectStatusV.t))) !!
            (k', uid') = None).
          { apply lookup_singleton_ne. done. }
          rewrite (lookup_op
            ((∅ : statusUR) ⋅
              ((∅ : statusUR) ⋅
                ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
                   (KObjectV.status obj))]} : statusUR)))
            bf.2.2.1 (k', uid')) in Hlookup_new.
          rewrite (lookup_op
            (∅ : statusUR)
            ((∅ : statusUR) ⋅
              ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
                 (KObjectV.status obj))]} : statusUR)) (k', uid')) in Hlookup_new.
          rewrite lookup_empty in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectStatusV.t))) None) in Hlookup_new.
          rewrite (lookup_op
            (∅ : statusUR)
            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
               (KObjectV.status obj))]} : statusUR) (k', uid')) in Hlookup_new.
          rewrite lookup_empty in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectStatusV.t))) None) in Hlookup_new.
          rewrite Hsingle_none in Hlookup_new.
          simpl in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectStatusV.t))) None) in Hlookup_new.
          done.
        }
        destruct (Hstatus _ _ Hlookup_old) as
          (status' & Hagree' & Huid_in' & Hvdq' & Hstatus').
        exists status'. split_and!. all: try done.
        { apply elem_of_union_l. exact Huid_in'. }
        intros obj0 Hlookup_obj0 Huid_obj0.
        destruct (decide (k' = k)) as [->|Hneq_k'].
        { rewrite lookup_insert in Hlookup_obj0.
          destruct (decide (k = k)) as [_|Hneq_k]; [|done].
          inversion Hlookup_obj0. subst obj0.
          exfalso.
          apply Hneq_pair.
          rewrite <- Huid_obj in Huid_obj0.
          congruence.
        }
        simpl in Hlookup_obj0.
        apply lookup_insert_Some in Hlookup_obj0.
        destruct Hlookup_obj0 as [[Hk_eq _]|[Hk_neq Hlookup_old_obj0]].
        { congruence. }
        eapply Hstatus'; done.
    + intros k' classification Hlookup_new.
      assert (Hlookup_old :
        proj_key_classification bf !! k' = Some classification).
      { move: Hlookup_new.
        rewrite /proj_key_classification /mk_meta_frag /mk_spec_frag
          /mk_status_frag /kview_frag /= !left_id. done. }
      destruct (Hreservation _ _ Hlookup_old) as
        [Hclassification_valid Hcompatible].
      split; [exact Hclassification_valid|].
      destruct classification as [agree|excl|]; [exact Hcompatible| |done].
      destruct excl as [reservation|]; [|done].
      destruct Hcompatible as [Hreserved Hreservation_state].
      split; [exact Hreserved|].
      assert (Hneq : k' ≠ k) by (intros ->; contradiction).
      destruct reservation as [|reserved_uid|reserved_uid].
      * simpl. rewrite lookup_insert_ne //.
      * destruct Hreservation_state as [obj' Hobj'].
        exists obj'. simpl. rewrite lookup_insert_ne //.
      * destruct Hreservation_state as [Habsent|Hpresent].
        { left. simpl. rewrite lookup_insert_ne //. }
        { right. destruct Hpresent as [obj' Hobj'].
          exists obj'. simpl. rewrite lookup_insert_ne //. }
Qed.

Lemma alloc_unreserved a k :
  ¬ reserved_key_pred k →
  ●K a ~~> ●K a ⋅ ◯K (mk_unreserved_frag k).
Proof.
  intros Hnot_reserved.
  apply view_update_alloc.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  split; [exact Hvalid|].
  split.
  { move: Hmeta. rewrite /proj_meta /mk_unreserved_frag /= !left_id //. }
  split.
  { move: Hspec. rewrite /proj_spec /mk_unreserved_frag /= !left_id //. }
  split.
  { move: Hstatus. rewrite /proj_status /mk_unreserved_frag /= !left_id //. }
  rewrite map_Forall_lookup.
  intros k' classification Hlookup.
  move: Hlookup.
  rewrite /proj_key_classification /mk_unreserved_frag /kview_frag /= lookup_op.
  destruct (decide (k' = k)) as [->|Hneq].
  - rewrite lookup_singleton_eq.
    destruct (proj_key_classification bf !! k) as [classification_f|]
      eqn:Hlookup_f; rewrite Hlookup_f /=.
    + intros Hclassification.
      destruct (Hreservation _ _ Hlookup_f) as [Hvalid_f Hcompatible_f].
      destruct classification_f as [agree_f|excl_f|].
      * assert (Hagree_f : agree_f ≡ to_agree (A := leibnizO unit) ()) by
          (apply valid_agree_unit_eq; exact Hvalid_f).
        rewrite /op /cmra_op /key_classificationR /= in Hclassification.
        inversion Hclassification. subst classification.
        split.
        { rewrite /valid /cmra_valid /op /cmra_op /key_classificationR /=.
          rewrite Hagree_f.
          rewrite to_agree_op_valid. done. }
        { exact Hnot_reserved. }
      * destruct excl_f as [status_f|].
        { destruct Hcompatible_f as [Hreserved _]. contradiction. }
        { done. }
      * done.
    + intros Hclassification. inversion Hclassification. subst classification.
      split; [done|exact Hnot_reserved].
  - rewrite lookup_singleton_ne // left_id.
    intros Hlookup_f. exact (Hreservation _ _ Hlookup_f).
Qed.

Lemma create_reserved_kobj a k uid obj:
  (proj_state a) !! k = None →
  uid ∉ (proj_used_uid a) →
  valid_k_uid_obj k uid obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
  no_speculative_parent_reference (KObjectV.objectmeta obj) (proj_used_uid a) →
  (●K a ⋅ ◯K (mk_reservation_frag k Available)) ~~>
    (●K ((<[k := obj]> (proj_state a)), ((proj_used_uid a) ∪ {[uid]})) ⋅
        ◯K (mk_meta_frag k uid 1 (KObjectV.objectmeta obj)) ⋅
        ◯K (mk_spec_frag k uid 1 (KObjectV.spec obj)) ⋅
        ◯K (mk_status_frag k uid 1 (KObjectV.status obj)) ⋅
        ◯K (mk_reservation_frag k (Occupied uid))).
Proof.
  intros Hak Huid_fresh Hkuid_obj Hdeletion_timestamp Hno_spec.
  destruct Hkuid_obj as (Hkey_obj & Huid_obj & Hwf_obj).
  rewrite -!assoc -!view_frag_op.
  apply view_update.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  rewrite /proj_meta /mk_reservation_frag /= left_id in Hmeta.
  rewrite /proj_spec /mk_reservation_frag /= left_id in Hspec.
  rewrite /proj_status /mk_reservation_frag /= left_id in Hstatus.
  assert (Hreservation_bf_none :
    proj_key_classification bf !! k = None).
  { destruct (proj_key_classification bf !! k) as [classification_f|] eqn:Hbf;
      last done.
    exfalso.
    assert (Hlookup :
      proj_key_classification (mk_reservation_frag k Available ⋅ bf) !! k =
        Some ((Cinr (Excl Available) : key_classificationR) ⋅
          classification_f)).
    { rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
        lookup_singleton_eq Hbf Some_op_opM //. }
    destruct (Hreservation _ _ Hlookup) as [Hclassification_valid _].
    exact (exclusive_l (Cinr (Excl Available) : key_classificationR)
      classification_f Hclassification_valid).
  }
  assert (Hreservation_pred : reserved_key_pred k).
  { assert (Hlookup :
      proj_key_classification (mk_reservation_frag k Available ⋅ bf) !! k =
        (Some (Cinr (Excl Available)) : option key_classificationR)).
    { rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
        lookup_singleton_eq Hreservation_bf_none right_id //. }
    destruct (Hreservation _ _ Hlookup) as [_ [Hpred _]].
    exact Hpred.
  }
  assert (Htarget_meta :
    proj_meta (mk_meta_frag k uid 1 (KObjectV.objectmeta obj) ⋅
      (mk_spec_frag k uid 1 (KObjectV.spec obj) ⋅
       (mk_status_frag k uid 1 (KObjectV.status obj) ⋅
        mk_reservation_frag k (Occupied uid))) ⋅ bf) =
    proj_meta (mk_meta_frag k uid 1 (KObjectV.objectmeta obj) ⋅
      (mk_spec_frag k uid 1 (KObjectV.spec obj) ⋅
       mk_status_frag k uid 1 (KObjectV.status obj)) ⋅ bf)).
  { rewrite /proj_meta /mk_meta_frag /mk_spec_frag /mk_status_frag
      /mk_reservation_frag /= !right_id. done. }
  assert (Htarget_spec :
    proj_spec (mk_meta_frag k uid 1 (KObjectV.objectmeta obj) ⋅
      (mk_spec_frag k uid 1 (KObjectV.spec obj) ⋅
       (mk_status_frag k uid 1 (KObjectV.status obj) ⋅
        mk_reservation_frag k (Occupied uid))) ⋅ bf) =
    proj_spec (mk_meta_frag k uid 1 (KObjectV.objectmeta obj) ⋅
      (mk_spec_frag k uid 1 (KObjectV.spec obj) ⋅
       mk_status_frag k uid 1 (KObjectV.status obj)) ⋅ bf)).
  { rewrite /proj_spec /mk_meta_frag /mk_spec_frag /mk_status_frag
      /mk_reservation_frag /= !left_id !right_id. done. }
  assert (Htarget_status :
    proj_status (mk_meta_frag k uid 1 (KObjectV.objectmeta obj) ⋅
      (mk_spec_frag k uid 1 (KObjectV.spec obj) ⋅
       (mk_status_frag k uid 1 (KObjectV.status obj) ⋅
        mk_reservation_frag k (Occupied uid))) ⋅ bf) =
    proj_status (mk_meta_frag k uid 1 (KObjectV.objectmeta obj) ⋅
      (mk_spec_frag k uid 1 (KObjectV.spec obj) ⋅
       mk_status_frag k uid 1 (KObjectV.status obj)) ⋅ bf)).
  { rewrite /proj_status /mk_meta_frag /mk_spec_frag /mk_status_frag
      /mk_reservation_frag /= !left_id !right_id. done. }
  assert (Htarget_reservation :
    proj_key_classification
      (mk_meta_frag k uid 1 (KObjectV.objectmeta obj) ⋅
       (mk_spec_frag k uid 1 (KObjectV.spec obj) ⋅
        (mk_status_frag k uid 1 (KObjectV.status obj) ⋅
         mk_reservation_frag k (Occupied uid))) ⋅ bf) =
    proj_key_classification (mk_reservation_frag k (Occupied uid) ⋅ bf)).
  { rewrite /proj_key_classification /mk_meta_frag /mk_spec_frag /mk_status_frag
      /mk_reservation_frag /= !left_id. done. }
  assert (Hmeta_bf_none : proj_meta bf !! (k, uid) = None).
  { destruct (proj_meta bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    destruct (Hmeta _ _ Hbf) as (meta0 & _ & _ & Hobj0).
    destruct Hobj0 as (obj0 & Hlookup_obj0 & _ & _).
    rewrite Hak in Hlookup_obj0. done.
  }
  assert (Hspec_bf_none : proj_spec bf !! (k, uid) = None).
  { destruct (proj_spec bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    destruct (Hspec _ _ Hbf) as (_ & _ & Huid_in & _ & _).
    apply Huid_fresh. done.
  }
  assert (Hstatus_bf_none : proj_status bf !! (k, uid) = None).
  { destruct (proj_status bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    destruct (Hstatus _ _ Hbf) as (_ & _ & Huid_in & _ & _).
    apply Huid_fresh. done.
  }

  split.
  - eapply map_Forall_lookup_2.
    intros k' obj' Hlookup_new.
    destruct (decide (k' = k)) as [->|Hneq_k'].
    + rewrite lookup_insert in Hlookup_new.
      destruct (decide (k = k)) as [_|Hneq_k]; [|done].
      inversion Hlookup_new. subst obj'.
      split_and!. all: try done.
      * rewrite Huid_obj. apply elem_of_union_r, elem_of_singleton_2. done.
      * intros kind name uid0 Hparent.
        apply elem_of_union_l.
        eapply Hno_spec. done.
      * eapply map_Forall_lookup_2.
        intros k'' obj'' Hlookup_new2 Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq_k''].
        { done. }
        simpl in Hlookup_new2.
        apply lookup_insert_Some in Hlookup_new2.
        destruct Hlookup_new2 as [[Hk_eq _]|[Hk_neq Hlookup_old2]].
        { congruence. }
        pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup_old2) as Hkobj_old2.
        destruct Hkobj_old2 as (_ & _ & Huid_in_old2 & _ & _).
        exfalso.
        apply Huid_fresh.
        rewrite Huid_obj.
        rewrite <- Huid_eq in Huid_in_old2.
        done.
    + simpl in Hlookup_new.
      apply lookup_insert_Some in Hlookup_new.
      destruct Hlookup_new as [[Hk_eq _]|[Hk_neq Hlookup_old]].
      { congruence. }
      pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup_old) as Hkobj_old.
      destruct Hkobj_old as (Hkey_old & Hwf_old & Huid_old_in & Hno_spec_old & Huniq_old).
      split_and!. all: try done.
      * apply elem_of_union_l. exact Huid_old_in.
      * intros kind name uid0 Hparent.
        apply elem_of_union_l.
        eapply Hno_spec_old. done.
      * eapply map_Forall_lookup_2.
        intros k'' obj'' Hlookup_new2 Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq_k''].
        { rewrite lookup_insert in Hlookup_new2.
          destruct (decide (k = k)) as [_|Hneq_k]; [|done].
          inversion Hlookup_new2. subst obj''.
          exfalso.
          apply Huid_fresh.
          rewrite <- Huid_obj in Huid_eq.
          rewrite Huid_eq in Huid_old_in.
          done.
        }
        simpl in Hlookup_new2.
        apply lookup_insert_Some in Hlookup_new2.
        destruct Hlookup_new2 as [[Hk_eq2 _]|[Hk_neq2 Hlookup_old2]].
        { congruence. }
        eapply Huniq_old; done.
  - split_and!.
    + rewrite Htarget_meta.
      intros [k' uid'] [dq' agree_meta'] Hlookup_new.
      destruct (decide ((k', uid') = (k, uid))) as [Heq_pair|Hneq_pair].
      * inversion Heq_pair. subst k' uid'.
        rewrite /proj_meta /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
        rewrite (right_id (A := metaUR) (∅ : metaUR)) in Hlookup_new.
	        rewrite (lookup_op
	          (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	             (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]} : metaUR) ⋅ ∅)
	          bf.1 (k, uid)) in Hlookup_new.
	        rewrite (lookup_op
	          ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	             (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]} : metaUR)
	          (∅ : metaUR) (k, uid)) in Hlookup_new.
        rewrite lookup_singleton_eq lookup_empty right_id Hmeta_bf_none right_id in Hlookup_new.
        inversion Hlookup_new. subst dq' agree_meta'.
	        exists (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)).
	        split_and!. all: try done.
        exists obj. split_and!;
          [rewrite lookup_insert_eq; done
          |symmetry; done
          |exact Hdeletion_timestamp
          |done].
      * assert (Hlookup_old : proj_meta bf !! (k', uid') = Some (dq', agree_meta')).
        { rewrite /proj_meta /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
          rewrite (right_id (A := metaUR) (∅ : metaUR)) in Hlookup_new.
	          assert (Hsingle_none :
	            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	              (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]}
	              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectMetaV.t))) !!
	            (k', uid') = None).
          { apply lookup_singleton_ne. done. }
	          rewrite (lookup_op
	            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	               (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]} : metaUR) ⋅ ∅)
	            bf.1 (k', uid')) in Hlookup_new.
	          rewrite (lookup_op
	            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	               (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]} : metaUR)
	            (∅ : metaUR) (k', uid')) in Hlookup_new.
          rewrite Hsingle_none lookup_empty in Hlookup_new.
          simpl in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectMetaV.t))) None) in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectMetaV.t))) None) in Hlookup_new.
          done.
        }
        destruct (Hmeta _ _ Hlookup_old) as (meta' & Hagree' & Hvdq' & Hobj').
        destruct Hobj' as
          (obj0 & Hlookup_obj0 & Huid_obj0 & Hliving_obj0 & Hmeta_obj0).
        assert (Hneq_k : k' ≠ k).
        { intros Hk'. subst k'.
          rewrite Hak in Hlookup_obj0. done.
        }
        exists meta'. split_and!. all: try done.
        exists obj0. split_and!. all: try done.
        rewrite lookup_insert_ne; done.
    + rewrite Htarget_spec.
      intros [k' uid'] [dq' agree_spec'] Hlookup_new.
      destruct (decide ((k', uid') = (k, uid))) as [Heq_pair|Hneq_pair].
      * inversion Heq_pair. subst k' uid'.
        rewrite /proj_spec /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
        rewrite (lookup_op
          ((∅ : specUR) ⋅
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
               (KObjectV.spec obj))]} : specUR) ⋅ ∅))
          bf.2.1 (k, uid)) in Hlookup_new.
        rewrite (lookup_op
          (∅ : specUR)
          (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
              (KObjectV.spec obj))]} : specUR) ⋅ ∅) (k, uid)) in Hlookup_new.
        rewrite lookup_empty in Hlookup_new.
        rewrite (left_id
          (A := option (dfrac * agree (leibnizO ObjectSpecV.t))) None) in Hlookup_new.
        rewrite (lookup_op
          ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
             (KObjectV.spec obj))]} : specUR)
          (∅ : specUR) (k, uid)) in Hlookup_new.
        rewrite lookup_singleton_eq lookup_empty right_id Hspec_bf_none right_id in Hlookup_new.
        inversion Hlookup_new. subst dq' agree_spec'.
        exists (KObjectV.spec obj). split_and!. all: try done.
        { rewrite Huid_obj. apply elem_of_union_r.
          apply elem_of_singleton_2. done. }
        intros obj0 Hlookup_obj0 Huid_obj0.
        rewrite lookup_insert in Hlookup_obj0.
        destruct (decide (k = k)) as [_|Hneq_k]; [|done].
        inversion Hlookup_obj0. subst obj0. done.
      * assert (Hlookup_old : proj_spec bf !! (k', uid') = Some (dq', agree_spec')).
        { rewrite /proj_spec /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
          assert (Hsingle_none :
            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
              (KObjectV.spec obj))]}
              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectSpecV.t))) !!
            (k', uid') = None).
          { apply lookup_singleton_ne. done. }
          rewrite (lookup_op
            ((∅ : specUR) ⋅
              (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
                 (KObjectV.spec obj))]} : specUR) ⋅ ∅))
            bf.2.1 (k', uid')) in Hlookup_new.
          rewrite (lookup_op
            (∅ : specUR)
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
                (KObjectV.spec obj))]} : specUR) ⋅ ∅) (k', uid')) in Hlookup_new.
          rewrite lookup_empty in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectSpecV.t))) None) in Hlookup_new.
          rewrite (lookup_op
            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t)
               (KObjectV.spec obj))]} : specUR)
            (∅ : specUR) (k', uid')) in Hlookup_new.
          rewrite Hsingle_none lookup_empty in Hlookup_new.
          simpl in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectSpecV.t))) None) in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectSpecV.t))) None) in Hlookup_new.
          done.
        }
        destruct (Hspec _ _ Hlookup_old) as (spec' & Hagree' & Huid_in' & Hvdq' & Hspec').
        exists spec'. split_and!. all: try done.
        { apply elem_of_union_l. done. }
        intros obj0 Hlookup_obj0 Huid_obj0.
        destruct (decide (k' = k)) as [->|Hneq_k'].
        { rewrite lookup_insert in Hlookup_obj0.
          destruct (decide (k = k)) as [_|Hneq_k]; [|done].
          inversion Hlookup_obj0. subst obj0.
          exfalso.
          apply Hneq_pair.
          rewrite <- Huid_obj in Huid_obj0.
          congruence.
        }
        simpl in Hlookup_obj0.
        apply lookup_insert_Some in Hlookup_obj0.
        destruct Hlookup_obj0 as [[Hk_eq _]|[Hk_neq Hlookup_old_obj0]].
        { congruence. }
        eapply Hspec'; done.
    + rewrite Htarget_status.
      intros [k' uid'] [dq' agree_status'] Hlookup_new.
      destruct (decide ((k', uid') = (k, uid))) as [Heq_pair|Hneq_pair].
      * inversion Heq_pair. subst k' uid'.
        rewrite /proj_status /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
        rewrite (lookup_op
          ((∅ : statusUR) ⋅
            ((∅ : statusUR) ⋅
              ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
                 (KObjectV.status obj))]} : statusUR)))
          bf.2.2.1 (k, uid)) in Hlookup_new.
        rewrite (lookup_op
          (∅ : statusUR)
          ((∅ : statusUR) ⋅
            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
               (KObjectV.status obj))]} : statusUR)) (k, uid)) in Hlookup_new.
        rewrite lookup_empty in Hlookup_new.
        rewrite (left_id
          (A := option (dfrac * agree (leibnizO ObjectStatusV.t))) None) in Hlookup_new.
        rewrite (lookup_op
          (∅ : statusUR)
          ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
             (KObjectV.status obj))]} : statusUR) (k, uid)) in Hlookup_new.
        rewrite lookup_empty in Hlookup_new.
        rewrite (left_id
          (A := option (dfrac * agree (leibnizO ObjectStatusV.t))) None) in Hlookup_new.
        rewrite lookup_singleton_eq Hstatus_bf_none right_id in Hlookup_new.
        inversion Hlookup_new. subst dq' agree_status'.
        exists (KObjectV.status obj). split_and!. all: try done.
        { rewrite Huid_obj. apply elem_of_union_r.
          apply elem_of_singleton_2. reflexivity. }
        intros obj0 Hlookup_obj0 Huid_obj0.
        rewrite lookup_insert in Hlookup_obj0.
        destruct (decide (k = k)) as [_|Hneq_k]; [|done].
        inversion Hlookup_obj0. subst obj0. done.
      * assert (Hlookup_old : proj_status bf !! (k', uid') = Some (dq', agree_status')).
        { rewrite /proj_status /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
          assert (Hsingle_none :
            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
              (KObjectV.status obj))]}
              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectStatusV.t))) !!
            (k', uid') = None).
          { apply lookup_singleton_ne. done. }
          rewrite (lookup_op
            ((∅ : statusUR) ⋅
              ((∅ : statusUR) ⋅
                ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
                   (KObjectV.status obj))]} : statusUR)))
            bf.2.2.1 (k', uid')) in Hlookup_new.
          rewrite (lookup_op
            (∅ : statusUR)
            ((∅ : statusUR) ⋅
              ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
                 (KObjectV.status obj))]} : statusUR)) (k', uid')) in Hlookup_new.
          rewrite lookup_empty in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectStatusV.t))) None) in Hlookup_new.
          rewrite (lookup_op
            (∅ : statusUR)
            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
               (KObjectV.status obj))]} : statusUR) (k', uid')) in Hlookup_new.
          rewrite lookup_empty in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectStatusV.t))) None) in Hlookup_new.
          rewrite Hsingle_none in Hlookup_new.
          simpl in Hlookup_new.
          rewrite (left_id
            (A := option (dfrac * agree (leibnizO ObjectStatusV.t))) None) in Hlookup_new.
          done.
        }
        destruct (Hstatus _ _ Hlookup_old) as
          (status' & Hagree' & Huid_in' & Hvdq' & Hstatus').
        exists status'. split_and!. all: try done.
        { apply elem_of_union_l. exact Huid_in'. }
        intros obj0 Hlookup_obj0 Huid_obj0.
        destruct (decide (k' = k)) as [->|Hneq_k'].
        { rewrite lookup_insert in Hlookup_obj0.
          destruct (decide (k = k)) as [_|Hneq_k]; [|done].
          inversion Hlookup_obj0. subst obj0.
          exfalso.
          apply Hneq_pair.
          rewrite <- Huid_obj in Huid_obj0.
          congruence.
        }
        simpl in Hlookup_obj0.
        apply lookup_insert_Some in Hlookup_obj0.
        destruct Hlookup_obj0 as [[Hk_eq _]|[Hk_neq Hlookup_old_obj0]].
        { congruence. }
        eapply Hstatus'; done.
    + intros k' classification Hlookup_new.
      destruct (decide (k' = k)) as [->|Hneq].
      * assert (Hlookup_target :
          proj_key_classification (mk_reservation_frag k (Occupied uid) ⋅ bf) !! k =
          (Some (Cinr (Excl (Occupied uid))) : option key_classificationR)).
        { rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
            lookup_singleton_eq Hreservation_bf_none right_id //. }
        rewrite Htarget_reservation Hlookup_target in Hlookup_new.
        inversion Hlookup_new. subst classification.
        split; [done|]. split; [exact Hreservation_pred|].
        exists obj. split_and!;
          [rewrite lookup_insert_eq; done
          |symmetry; done
          |exact Hdeletion_timestamp].
      * assert (Hlookup_bf :
          proj_key_classification bf !! k' = Some classification).
        { assert (Hneq' : k ≠ k') by (intros ->; apply Hneq; done).
          rewrite Htarget_reservation in Hlookup_new.
          rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
            lookup_singleton_ne // left_id in Hlookup_new.
          exact Hlookup_new. }
        assert (Hlookup_old :
          proj_key_classification (mk_reservation_frag k Available ⋅ bf) !! k' =
            Some classification).
        { assert (Hneq' : k ≠ k') by (intros ->; apply Hneq; done).
          rewrite /proj_key_classification /mk_reservation_frag /= lookup_op.
          rewrite lookup_singleton_ne // Hlookup_bf left_id //. }
        destruct (Hreservation _ _ Hlookup_old) as
          [Hclassification_valid Hcompatible].
        split; [exact Hclassification_valid|].
        destruct classification as [agree|excl|]; [exact Hcompatible| |done].
        destruct excl as [reservation|]; [|done].
        destruct Hcompatible as [Hreserved Hreservation_state].
        split; [exact Hreserved|].
        destruct reservation as [|reserved_uid|reserved_uid].
        { simpl. rewrite lookup_insert_ne //. }
        { destruct Hreservation_state as [obj' Hobj'].
          exists obj'. simpl. rewrite lookup_insert_ne //. }
        { destruct Hreservation_state as [Habsent|Hpresent].
          - left. simpl. rewrite lookup_insert_ne //.
          - right. destruct Hpresent as [obj' Hobj'].
            exists obj'. simpl. rewrite lookup_insert_ne //. }
Qed.

Lemma delete_kobj_raw a k uid meta:
  ¬ reserved_key_pred k →
  ●K a ⋅ ◯K (mk_meta_frag k uid 1 meta) ~~>
    ●K (delete k (proj_state a), proj_used_uid a).
Proof.
  intros Hnot_reserved.
  apply view_update_dealloc.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  assert (Hbf_none : proj_meta bf !! (k, uid) = None).
  { destruct (proj_meta bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
	    assert (Hlookup :
	      (proj_meta (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k, uid) =
	      Some ((DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	        (ObjectMetaV.without_resource_version meta)) ⋅ (dqf, agf))).
    { rewrite /proj_meta /mk_meta_frag /= lookup_op.
      rewrite lookup_singleton_eq Hbf Some_op_opM //. }
    destruct (Hmeta _ _ Hlookup) as (meta0 & _ & Hvdq & _).
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dqf 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt.
    apply Hlt. done.
  }
	  assert (Hlookup_k :
	    (proj_meta (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k, uid) =
	    Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	      (ObjectMetaV.without_resource_version meta))).
  { rewrite /proj_meta /mk_meta_frag /= lookup_op.
    rewrite lookup_singleton_eq Hbf_none right_id //. }
  destruct (Hmeta _ _ Hlookup_k) as (meta0 & Hagree0 & _ & Hobj0).
  destruct Hobj0 as (obj0 & Hobj0_lookup & Hobj0_uid & Hobj0_meta).
	  assert (Hmeta_eqv : (ObjectMetaV.without_resource_version meta : leibnizO ObjectMetaV.t) ≡ meta0).
  { apply (inj (to_agree : leibnizO ObjectMetaV.t → agree (leibnizO ObjectMetaV.t))).
    by rewrite Hagree0.
  }
  apply leibniz_equiv in Hmeta_eqv. subst meta0.
  assert (Hbf_none_obj0 :
    proj_meta bf !! (k, ObjectMetaV.UID' (KObjectV.objectmeta obj0)) = None).
  { rewrite Hobj0_uid. done. }

  split.
  - intros k' obj' Hlookup.
    simpl in Hlookup.
    apply lookup_delete_Some in Hlookup as [_ Hlookup].
    pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup) as Hkobj.
    destruct Hkobj as (Hkey & Hwf & Huid_in & Hno_spec & Huniq).
    split_and!. all: try done.
    apply map_Forall_delete. done.
  - split_and!.
    + intros [k' uid'] [dq' agree_meta'] Hlookup_bf.
      assert (Hneq_pair : (k', uid') ≠ (k, uid)).
      { intros Heq. inversion Heq. subst.
        rewrite Hbf_none_obj0 in Hlookup_bf. done.
      }
      assert (Hlookup_old :
        (proj_meta (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k', uid') =
        Some (dq', agree_meta')).
      { rewrite /proj_meta /mk_meta_frag /=.
	        rewrite (lookup_op
	          ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	            (ObjectMetaV.without_resource_version meta))]})
	          (proj_meta bf) (k', uid')).
	        assert (Hsingle_none :
	          (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	            (ObjectMetaV.without_resource_version meta))]}
	            : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectMetaV.t))) !!
            (k', uid')) = None).
        { apply lookup_singleton_ne. done. }
        rewrite Hsingle_none.
        rewrite Hlookup_bf left_id //. }
      destruct (Hmeta _ _ Hlookup_old) as (meta' & Hagree' & Hvdq' & Hobj').
      destruct Hobj' as
        (obj' & Hobj'_lookup & Hobj'_uid & Hobj'_living & Hobj'_meta).
      assert (Hneq_k : k' ≠ k).
      { intros Hk'. subst k'.
        rewrite Hobj0_lookup in Hobj'_lookup. inversion Hobj'_lookup. subst obj'.
        assert (Huid' : uid' = uid) by congruence.
        subst uid'. exfalso. apply Hneq_pair.
        apply (f_equal (λ u, (k, u))). done.
      }
      exists meta'.
      split_and!. all: try done.
      exists obj'. split_and!. all: try done.
      apply lookup_delete_Some. split; [done|done].
    + intros [k' uid'] [dq' agree_spec'] Hlookup_bf.
      assert (Hlookup_old :
        (proj_spec (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k', uid') =
        Some (dq', agree_spec')).
      { rewrite /proj_spec /mk_meta_frag /=.
        rewrite (lookup_op ∅ (proj_spec bf) (k', uid')).
        rewrite lookup_empty left_id. done. }
      destruct (Hspec _ _ Hlookup_old) as (spec' & Hagree' & Huid' & Hvdq' & Hspec').
      exists spec'. split_and!. all: try done.
      intros obj Hlookup Huid_obj.
      simpl in Hlookup.
      apply lookup_delete_Some in Hlookup as [_ Hlookup].
      eapply Hspec'; done.
    + intros [k' uid'] [dq' agree_status'] Hlookup_bf.
      assert (Hlookup_old :
        (proj_status (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k', uid') =
        Some (dq', agree_status')).
      { rewrite /proj_status /mk_meta_frag /=.
        rewrite (lookup_op ∅ (proj_status bf) (k', uid')).
        rewrite lookup_empty left_id. done. }
      destruct (Hstatus _ _ Hlookup_old) as
        (status' & Hagree' & Huid' & Hvdq' & Hstatus').
      exists status'. split_and!. all: try done.
      intros obj Hlookup Huid_obj.
      simpl in Hlookup.
      apply lookup_delete_Some in Hlookup as [_ Hlookup].
      eapply Hstatus'; done.
    + intros k' classification Hlookup_bf.
      assert (Hlookup_old :
        (proj_key_classification (mk_meta_frag k uid 1 meta ⋅ bf)) !! k' =
          Some classification).
      { rewrite /proj_key_classification /mk_meta_frag /= lookup_op lookup_empty
          left_id. done. }
      destruct (Hreservation _ _ Hlookup_old) as
        [Hclassification_valid Hcompatible].
      split; [exact Hclassification_valid|].
      destruct classification as [agree|excl|]; [exact Hcompatible| |done].
      destruct excl as [reservation|]; [|done].
      destruct Hcompatible as [Hreserved Hreservation_state].
      split; [exact Hreserved|].
      assert (Hneq : k' ≠ k) by (intros ->; contradiction).
      destruct reservation as [|reserved_uid|reserved_uid].
      * simpl. rewrite lookup_delete_ne //.
      * destruct Hreservation_state as [obj' Hobj'].
        exists obj'. simpl. rewrite lookup_delete_ne //.
      * destruct Hreservation_state as [Habsent|Hpresent].
        { left. simpl. rewrite lookup_delete_ne //. }
        { right. destruct Hpresent as [obj' Hobj'].
          exists obj'. simpl. rewrite lookup_delete_ne //. }
Qed.

Lemma delete_reserved_kobj a k uid meta:
  (●K a ⋅ ◯K (mk_meta_frag k uid 1 meta) ⋅
    ◯K (mk_reservation_frag k (Occupied uid))) ~~>
    (●K (delete k (proj_state a), proj_used_uid a) ⋅
      ◯K (mk_reservation_frag k (Deleting uid))).
Proof.
  rewrite -!assoc -!view_frag_op.
  apply view_update.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  assert (Hsource_meta :
    proj_meta ((mk_meta_frag k uid 1 meta ⋅
      mk_reservation_frag k (Occupied uid)) ⋅ bf) =
    proj_meta (mk_meta_frag k uid 1 meta ⋅ bf)).
  { rewrite /proj_meta /mk_meta_frag /mk_reservation_frag /= !right_id.
    done. }
  assert (Hsource_spec :
    proj_spec ((mk_meta_frag k uid 1 meta ⋅
      mk_reservation_frag k (Occupied uid)) ⋅ bf) =
    proj_spec (mk_meta_frag k uid 1 meta ⋅ bf)).
  { rewrite /proj_spec /mk_meta_frag /mk_reservation_frag /= !left_id.
    done. }
  assert (Hsource_status :
    proj_status ((mk_meta_frag k uid 1 meta ⋅
      mk_reservation_frag k (Occupied uid)) ⋅ bf) =
    proj_status (mk_meta_frag k uid 1 meta ⋅ bf)).
  { rewrite /proj_status /mk_meta_frag /mk_reservation_frag /= !left_id.
    done. }
  rewrite Hsource_meta in Hmeta.
  rewrite Hsource_spec in Hspec.
  rewrite Hsource_status in Hstatus.
  assert (Hreservation_bf_none :
    proj_key_classification bf !! k = None).
  { destruct (proj_key_classification bf !! k) as [classification_f|] eqn:Hbf;
      last done.
    exfalso.
    assert (Hlookup :
      proj_key_classification ((mk_meta_frag k uid 1 meta ⋅
        mk_reservation_frag k (Occupied uid)) ⋅ bf) !! k =
        Some ((Cinr (Excl (Occupied uid)) : key_classificationR) ⋅
          classification_f)).
    { rewrite /proj_key_classification /mk_meta_frag /mk_reservation_frag /=
        !lookup_op !lookup_empty !left_id lookup_singleton_eq Hbf
        Some_op_opM //. }
    destruct (Hreservation _ _ Hlookup) as [Hclassification_valid _].
    exact (exclusive_l (Cinr (Excl (Occupied uid)) : key_classificationR)
      classification_f Hclassification_valid).
  }
  assert (Hreservation_pred : reserved_key_pred k).
  { assert (Hlookup :
      proj_key_classification ((mk_meta_frag k uid 1 meta ⋅
        mk_reservation_frag k (Occupied uid)) ⋅ bf) !! k =
        (Some (Cinr (Excl (Occupied uid))) : option key_classificationR)).
    { rewrite /proj_key_classification /mk_meta_frag /mk_reservation_frag /=
        !lookup_op !lookup_empty !left_id lookup_singleton_eq
        Hreservation_bf_none right_id //. }
    destruct (Hreservation _ _ Hlookup) as [_ [Hpred _]].
    exact Hpred.
  }
  assert (Htarget_meta :
    proj_meta (mk_reservation_frag k (Deleting uid) ⋅ bf) = proj_meta bf).
  { rewrite /proj_meta /mk_reservation_frag /= left_id //. }
  assert (Htarget_spec :
    proj_spec (mk_reservation_frag k (Deleting uid) ⋅ bf) = proj_spec bf).
  { rewrite /proj_spec /mk_reservation_frag /= left_id //. }
  assert (Htarget_status :
    proj_status (mk_reservation_frag k (Deleting uid) ⋅ bf) = proj_status bf).
  { rewrite /proj_status /mk_reservation_frag /= left_id //. }
  assert (Hbf_none : proj_meta bf !! (k, uid) = None).
  { destruct (proj_meta bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
	    assert (Hlookup :
	      (proj_meta (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k, uid) =
	      Some ((DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	        (ObjectMetaV.without_resource_version meta)) ⋅ (dqf, agf))).
    { rewrite /proj_meta /mk_meta_frag /= lookup_op.
      rewrite lookup_singleton_eq Hbf Some_op_opM //. }
    destruct (Hmeta _ _ Hlookup) as (meta0 & _ & Hvdq & _).
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dqf 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt.
    apply Hlt. done.
  }
	  assert (Hlookup_k :
	    (proj_meta (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k, uid) =
	    Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	      (ObjectMetaV.without_resource_version meta))).
  { rewrite /proj_meta /mk_meta_frag /= lookup_op.
    rewrite lookup_singleton_eq Hbf_none right_id //. }
  destruct (Hmeta _ _ Hlookup_k) as (meta0 & Hagree0 & _ & Hobj0).
  destruct Hobj0 as (obj0 & Hobj0_lookup & Hobj0_uid & Hobj0_meta).
	  assert (Hmeta_eqv : (ObjectMetaV.without_resource_version meta : leibnizO ObjectMetaV.t) ≡ meta0).
  { apply (inj (to_agree : leibnizO ObjectMetaV.t → agree (leibnizO ObjectMetaV.t))).
    by rewrite Hagree0.
  }
  apply leibniz_equiv in Hmeta_eqv. subst meta0.
  assert (Hbf_none_obj0 :
    proj_meta bf !! (k, ObjectMetaV.UID' (KObjectV.objectmeta obj0)) = None).
  { rewrite Hobj0_uid. done. }

  split.
  - intros k' obj' Hlookup.
    simpl in Hlookup.
    apply lookup_delete_Some in Hlookup as [_ Hlookup].
    pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup) as Hkobj.
    destruct Hkobj as (Hkey & Hwf & Huid_in & Hno_spec & Huniq).
    split_and!. all: try done.
    apply map_Forall_delete. done.
  - split_and!.
    + rewrite Htarget_meta.
      intros [k' uid'] [dq' agree_meta'] Hlookup_bf.
      assert (Hneq_pair : (k', uid') ≠ (k, uid)).
      { intros Heq. inversion Heq. subst.
        rewrite Hbf_none_obj0 in Hlookup_bf. done.
      }
      assert (Hlookup_old :
        (proj_meta (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k', uid') =
        Some (dq', agree_meta')).
      { rewrite /proj_meta /mk_meta_frag /=.
	        rewrite (lookup_op
	          ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	            (ObjectMetaV.without_resource_version meta))]})
	          (proj_meta bf) (k', uid')).
	        assert (Hsingle_none :
	          (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	            (ObjectMetaV.without_resource_version meta))]}
	            : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectMetaV.t))) !!
            (k', uid')) = None).
        { apply lookup_singleton_ne. done. }
        rewrite Hsingle_none.
        rewrite Hlookup_bf left_id //. }
      destruct (Hmeta _ _ Hlookup_old) as (meta' & Hagree' & Hvdq' & Hobj').
      destruct Hobj' as
        (obj' & Hobj'_lookup & Hobj'_uid & Hobj'_living & Hobj'_meta).
      assert (Hneq_k : k' ≠ k).
      { intros Hk'. subst k'.
        rewrite Hobj0_lookup in Hobj'_lookup. inversion Hobj'_lookup. subst obj'.
        assert (Huid' : uid' = uid) by congruence.
        subst uid'. exfalso. apply Hneq_pair.
        apply (f_equal (λ u, (k, u))). done.
      }
      exists meta'.
      split_and!. all: try done.
      exists obj'. split_and!. all: try done.
      apply lookup_delete_Some. split; [done|done].
    + rewrite Htarget_spec.
      intros [k' uid'] [dq' agree_spec'] Hlookup_bf.
      assert (Hlookup_old :
        (proj_spec (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k', uid') =
        Some (dq', agree_spec')).
      { rewrite /proj_spec /mk_meta_frag /=.
        rewrite (lookup_op ∅ (proj_spec bf) (k', uid')).
        rewrite lookup_empty left_id. done. }
      destruct (Hspec _ _ Hlookup_old) as (spec' & Hagree' & Huid' & Hvdq' & Hspec').
      exists spec'. split_and!. all: try done.
      intros obj Hlookup Huid_obj.
      simpl in Hlookup.
      apply lookup_delete_Some in Hlookup as [_ Hlookup].
      eapply Hspec'; done.
    + rewrite Htarget_status.
      intros [k' uid'] [dq' agree_status'] Hlookup_bf.
      assert (Hlookup_old :
        (proj_status (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k', uid') =
        Some (dq', agree_status')).
      { rewrite /proj_status /mk_meta_frag /=.
        rewrite (lookup_op ∅ (proj_status bf) (k', uid')).
        rewrite lookup_empty left_id. done. }
      destruct (Hstatus _ _ Hlookup_old) as
        (status' & Hagree' & Huid' & Hvdq' & Hstatus').
      exists status'. split_and!. all: try done.
      intros obj Hlookup Huid_obj.
      simpl in Hlookup.
      apply lookup_delete_Some in Hlookup as [_ Hlookup].
      eapply Hstatus'; done.
    + intros k' classification Hlookup_new.
      destruct (decide (k' = k)) as [->|Hneq].
      * assert (Hlookup_target :
          proj_key_classification (mk_reservation_frag k (Deleting uid) ⋅ bf) !! k =
          (Some (Cinr (Excl (Deleting uid))) : option key_classificationR)).
        { rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
            lookup_singleton_eq Hreservation_bf_none right_id //. }
        rewrite Hlookup_target in Hlookup_new.
        inversion Hlookup_new. subst classification.
        split; [done|]. split; [exact Hreservation_pred|].
        left. simpl. apply lookup_delete_eq.
      * assert (Hneq' : k ≠ k') by (intros ->; apply Hneq; done).
        assert (Hlookup_bf :
          proj_key_classification bf !! k' = Some classification).
        { rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
            lookup_singleton_ne // left_id in Hlookup_new.
          exact Hlookup_new. }
        assert (Hlookup_old :
          proj_key_classification ((mk_meta_frag k uid 1 meta ⋅
            mk_reservation_frag k (Occupied uid)) ⋅ bf) !! k' =
            Some classification).
        { rewrite /proj_key_classification /mk_meta_frag /mk_reservation_frag /=
            !lookup_op !lookup_empty !left_id lookup_singleton_ne //
            Hlookup_bf left_id //. }
        destruct (Hreservation _ _ Hlookup_old) as
          [Hclassification_valid Hcompatible].
        split; [exact Hclassification_valid|].
        destruct classification as [agree|excl|]; [exact Hcompatible| |done].
        destruct excl as [reservation|]; [|done].
        destruct Hcompatible as [Hreserved Hreservation_state].
        split; [exact Hreserved|].
        destruct reservation as [|reserved_uid|reserved_uid].
        { simpl. rewrite lookup_delete_ne //. }
        { destruct Hreservation_state as [obj' Hobj'].
          exists obj'. simpl. rewrite lookup_delete_ne //. }
        { destruct Hreservation_state as [Habsent|Hpresent].
          - left. simpl. rewrite lookup_delete_ne //.
          - right. destruct Hpresent as [obj' Hobj'].
            exists obj'. simpl. rewrite lookup_delete_ne //.
        }
Qed.

Lemma recover_available a k uid :
  proj_state a !! k = None →
  (●K a ⋅ ◯K (mk_reservation_frag k (Deleting uid))) ~~>
    (●K a ⋅ ◯K (mk_reservation_frag k Available)).
Proof.
  intros Habsent.
  apply view_update.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  assert (Hbf_none : proj_key_classification bf !! k = None).
  { destruct (proj_key_classification bf !! k) as [classification_f|] eqn:Hlookup;
      last done.
    exfalso.
    assert (Hsource_lookup :
        proj_key_classification (mk_reservation_frag k (Deleting uid) ⋅ bf) !! k =
          Some ((Cinr (Excl (Deleting uid)) : key_classificationR) ⋅
            classification_f)).
    { rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
        lookup_singleton_eq Hlookup Some_op_opM //. }
    destruct (Hreservation _ _ Hsource_lookup) as [Hclassification_valid _].
    exact (exclusive_l (Cinr (Excl (Deleting uid)) : key_classificationR)
      classification_f Hclassification_valid). }
  assert (Hreserved : reserved_key_pred k).
  { assert (Hsource_lookup :
        proj_key_classification (mk_reservation_frag k (Deleting uid) ⋅ bf) !! k =
          (Some (Cinr (Excl (Deleting uid))) : option key_classificationR)).
    { rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
        lookup_singleton_eq Hbf_none right_id //. }
    destruct (Hreservation _ _ Hsource_lookup) as [_ [Hreserved _]].
    exact Hreserved. }
  split; first exact Hvalid.
  split_and!.
  - rewrite /proj_meta /mk_reservation_frag /= !left_id in Hmeta |- *.
    exact Hmeta.
  - rewrite /proj_spec /mk_reservation_frag /= !left_id in Hspec |- *.
    exact Hspec.
  - rewrite /proj_status /mk_reservation_frag /= !left_id in Hstatus |- *.
    exact Hstatus.
  - intros k' classification Hlookup_target.
    destruct (decide (k' = k)) as [->|Hneq].
    + rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
        lookup_singleton_eq Hbf_none right_id in Hlookup_target.
      inversion Hlookup_target. subst classification.
      split; [done|]. split; [exact Hreserved|exact Habsent].
    + assert (Hlookup_bf : proj_key_classification bf !! k' =
          Some classification).
      { rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
          lookup_singleton_ne // left_id in Hlookup_target.
        exact Hlookup_target. }
      assert (Hlookup_source :
          proj_key_classification (mk_reservation_frag k (Deleting uid) ⋅ bf) !! k' =
            Some classification).
      { rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
          lookup_singleton_ne // Hlookup_bf left_id //. }
      destruct (Hreservation _ _ Hlookup_source) as
        [Hclassification_valid Hcompatible].
      split; done.
Qed.

Lemma delete_terminating_kobj a k obj :
  proj_state a !! k = Some obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
  ●K a ~~> ●K (delete k (proj_state a), proj_used_uid a).
Proof.
  intros Hlookup Hterminating.
  apply view_update_auth.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  split.
  - rewrite /valid_kauth map_Forall_lookup.
    intros k' obj' Hlookup'.
    simpl in Hlookup'.
    apply lookup_delete_Some in Hlookup' as [_ Hlookup'].
    pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup') as
      (Hkey & Hwf & Huid & Hparent & Hunique).
    split_and!; try done.
    simpl. apply map_Forall_delete. done.
  - split_and!.
    + rewrite map_Forall_lookup.
      intros [k' uid'] [dq agree_meta] Hfrag.
      destruct (Hmeta _ _ Hfrag) as
        (meta & Hagree & Hvdq & obj' & Hobj' & Huid' & Hliving & Hmeta').
      assert (k' ≠ k) as Hneq.
      { intros ->. rewrite Hlookup in Hobj'. injection Hobj' as <-.
        exact (Hterminating Hliving). }
      exists meta. split_and!; try done.
      exists obj'. split_and!; try done.
      simpl.
      apply lookup_delete_Some. split; done.
    + rewrite map_Forall_lookup.
      intros [k' uid'] [dq agree_spec] Hfrag.
      destruct (Hspec _ _ Hfrag) as
        (spec & Hagree & Huid & Hvdq & Hspec_obj).
      exists spec. split_and!; try done.
      intros obj' Hobj' Huid'.
      simpl in Hobj'.
      apply lookup_delete_Some in Hobj' as [_ Hobj'].
      eapply Hspec_obj; done.
    + rewrite map_Forall_lookup.
      intros [k' uid'] [dq agree_status] Hfrag.
      destruct (Hstatus _ _ Hfrag) as
        (status & Hagree & Huid & Hvdq & Hstatus_obj).
      exists status. split_and!; try done.
      intros obj' Hobj' Huid'.
      simpl in Hobj'.
      apply lookup_delete_Some in Hobj' as [_ Hobj'].
      eapply Hstatus_obj; done.
    + rewrite map_Forall_lookup.
      intros k' classification Hfrag.
      destruct (Hreservation _ _ Hfrag) as
        [Hclassification_valid Hcompatible].
      split; [exact Hclassification_valid|].
      destruct classification as [agree|excl|]; [exact Hcompatible| |done].
      destruct excl as [reservation|]; [|done].
      destruct Hcompatible as [Hreserved Hstate].
      split; [exact Hreserved|].
      destruct reservation as [|reserved_uid|reserved_uid].
      * assert (k' ≠ k) as Hneq.
        { intros ->. rewrite Hlookup in Hstate. done. }
        rewrite lookup_delete_ne //.
      * destruct Hstate as (obj' & Hobj' & Huid' & Hliving).
        assert (k' ≠ k) as Hneq.
        { intros ->. rewrite Hlookup in Hobj'. injection Hobj' as <-.
          exact (Hterminating Hliving). }
        exists obj'. rewrite lookup_delete_ne //.
      * destruct (decide (k' = k)) as [->|Hneq].
        { left. rewrite lookup_delete_eq //. }
        destruct Hstate as [Habsent|Hpresent].
        { left. rewrite lookup_delete_ne //. }
        { right. destruct Hpresent as (obj' & Hobj' & Huid' & Hterm').
          exists obj'. rewrite lookup_delete_ne //. }
Qed.

Lemma update_terminating_kobj a k uid old_obj new_obj :
  valid_k_uid_obj k uid new_obj →
  (KObjectV.objectmeta new_obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
  no_speculative_parent_reference (KObjectV.objectmeta new_obj)
    (proj_used_uid a) →
  proj_state a !! k = Some old_obj →
  (KObjectV.objectmeta old_obj).(ObjectMetaV.UID') = uid →
  (KObjectV.objectmeta old_obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
  ●K a ~~> ●K (<[k := new_obj]> (proj_state a), proj_used_uid a).
Proof.
  intros (Hkey_new & Huid_new & Hvalid_new) Hnew_terminating Hno_spec
    Hlookup Hold_uid Hold_terminating.
  apply view_update_auth.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup) as
    (Hkey_old & Hvalid_old & Huid_in & Hno_spec_old & Hunique_old).
  assert (Huid_old_new :
      (KObjectV.objectmeta old_obj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta new_obj).(ObjectMetaV.UID')).
  { rewrite Hold_uid Huid_new //. }
  split.
  - rewrite /valid_kauth map_Forall_lookup.
    intros k' obj' Hlookup_new.
    simpl in Hlookup_new.
    destruct (decide (k' = k)) as [->|Hneq].
    + rewrite lookup_insert_eq in Hlookup_new. injection Hlookup_new as <-.
      split_and!; try done.
      * rewrite -Huid_new. rewrite -Hold_uid. exact Huid_in.
      * rewrite map_Forall_lookup. intros k'' obj'' Hlookup'' Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq'']; first done.
        rewrite lookup_insert_ne // in Hlookup''.
        eapply Hunique_old; [exact Hlookup''|].
        rewrite Huid_old_new. exact Huid_eq.
    + rewrite lookup_insert_ne // in Hlookup_new.
      pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup_new) as
        (Hkey & Hwf & Huid & Hparent & Hunique).
      split_and!; try done.
      rewrite map_Forall_lookup. intros k'' obj'' Hlookup'' Huid_eq.
      destruct (decide (k'' = k)) as [->|Hneq''].
      * rewrite lookup_insert_eq in Hlookup''. injection Hlookup'' as <-.
        eapply Hunique; [exact Hlookup|].
        rewrite Huid_old_new. exact Huid_eq.
      * rewrite lookup_insert_ne // in Hlookup''.
        eapply Hunique; done.
  - split_and!.
    + rewrite map_Forall_lookup. intros [k' uid'] [dq agree_meta] Hfrag.
      destruct (Hmeta _ _ Hfrag) as
        (meta & Hagree & Hvdq & obj' & Hobj' & Huid' & Hliving & Hmeta').
      assert (k' ≠ k) as Hneq.
      { intros ->. rewrite Hlookup in Hobj'. injection Hobj' as <-.
        exact (Hold_terminating Hliving). }
      exists meta. split_and!; try done.
      exists obj'. split_and!; try done.
      simpl. rewrite lookup_insert_ne //.
    + rewrite map_Forall_lookup. intros [k' uid'] [dq agree_spec] Hfrag.
      destruct (Hspec _ _ Hfrag) as
        (spec & Hagree & Huid & Hvdq & Hspec_obj).
      exists spec. split_and!; try done.
      intros obj' Hobj' Huid' Hliving'. simpl in Hobj'.
      destruct (decide (k' = k)) as [->|Hneq].
      * rewrite lookup_insert_eq in Hobj'. injection Hobj' as <-.
        exfalso. exact (Hnew_terminating Hliving').
      * rewrite lookup_insert_ne // in Hobj'. eapply Hspec_obj; done.
    + rewrite map_Forall_lookup. intros [k' uid'] [dq agree_status] Hfrag.
      destruct (Hstatus _ _ Hfrag) as
        (status & Hagree & Huid & Hvdq & Hstatus_obj).
      exists status. split_and!; try done.
      intros obj' Hobj' Huid' Hliving'. simpl in Hobj'.
      destruct (decide (k' = k)) as [->|Hneq].
      * rewrite lookup_insert_eq in Hobj'. injection Hobj' as <-.
        exfalso. exact (Hnew_terminating Hliving').
      * rewrite lookup_insert_ne // in Hobj'. eapply Hstatus_obj; done.
    + rewrite map_Forall_lookup.
      intros k' classification Hfrag.
      destruct (Hreservation _ _ Hfrag) as
        [Hclassification_valid Hcompatible].
      split; [exact Hclassification_valid|].
      destruct classification as [agree|excl|]; [exact Hcompatible| |done].
      destruct excl as [reservation|]; [|done].
      destruct Hcompatible as [Hreserved Hstate].
      split; [exact Hreserved|].
      destruct reservation as [|reserved_uid|reserved_uid].
      * assert (k' ≠ k) as Hneq.
        { intros ->. rewrite Hlookup in Hstate. done. }
        rewrite lookup_insert_ne //.
      * destruct Hstate as (obj' & Hobj' & Huid' & Hliving).
        assert (k' ≠ k) as Hneq.
        { intros ->. rewrite Hlookup in Hobj'. injection Hobj' as <-.
          exact (Hold_terminating Hliving). }
        exists obj'. rewrite lookup_insert_ne //.
      * destruct (decide (k' = k)) as [->|Hneq].
        { right. destruct Hstate as [Habsent|Hpresent].
          - rewrite Hlookup in Habsent. done.
          - destruct Hpresent as (obj' & Hobj' & Huid' & Hterm').
            rewrite Hlookup in Hobj'. injection Hobj' as <-.
            exists new_obj. split_and!.
            + rewrite lookup_insert_eq //.
            + rewrite -Huid_new -Hold_uid. exact Huid'.
            + exact Hnew_terminating. }
        destruct Hstate as [Habsent|Hpresent].
        { left. rewrite lookup_insert_ne //. }
        { right. destruct Hpresent as (obj' & Hobj' & Huid' & Hterm').
          exists obj'. rewrite lookup_insert_ne //. }
Qed.

Lemma mark_terminating_kobj_raw a k uid meta old_obj new_obj :
  ¬ reserved_key_pred k →
  valid_k_uid_obj k uid new_obj →
  (KObjectV.objectmeta new_obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
  no_speculative_parent_reference (KObjectV.objectmeta new_obj)
    (proj_used_uid a) →
  proj_state a !! k = Some old_obj →
  (●K a ⋅ ◯K (mk_meta_frag k uid 1 meta)) ~~>
    ●K (<[k := new_obj]> (proj_state a), proj_used_uid a).
Proof.
  intros Hnot_reserved (Hkey_new & Huid_new & Hvalid_new)
    Hnew_terminating Hno_spec Hlookup.
  apply view_update_dealloc.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  assert (Hmeta_bf_none : proj_meta bf !! (k, uid) = None).
  { destruct (proj_meta bf !! (k, uid)) as [[dqf agreef]|] eqn:Hbf;
      last done.
    exfalso.
    assert (Hsource :
        proj_meta (mk_meta_frag k uid 1 meta ⋅ bf) !! (k, uid) =
          Some ((DfracOwn 1,
            to_agree (A := leibnizO ObjectMetaV.t)
              (ObjectMetaV.without_resource_version meta)) ⋅
            (dqf, agreef))).
    { rewrite /proj_meta /mk_meta_frag /= lookup_op lookup_singleton_eq
        Hbf Some_op_opM //. }
    destruct (Hmeta _ _ Hsource) as (meta' & _ & Hvdq & _).
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dqf 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt. apply Hlt. done. }
  assert (Hsource_meta :
      proj_meta (mk_meta_frag k uid 1 meta ⋅ bf) !! (k, uid) =
        Some (DfracOwn 1,
          to_agree (A := leibnizO ObjectMetaV.t)
            (ObjectMetaV.without_resource_version meta))).
  { rewrite /proj_meta /mk_meta_frag /= lookup_op lookup_singleton_eq
      Hmeta_bf_none right_id //. }
  destruct (Hmeta _ _ Hsource_meta) as
    (meta' & Hagree & Hvdq & old_obj' & Hold_lookup & Hold_uid &
      Hold_living & Hold_meta).
  rewrite Hlookup in Hold_lookup. injection Hold_lookup as <-.
  assert (Huid_old_new :
      (KObjectV.objectmeta old_obj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta new_obj).(ObjectMetaV.UID')).
  { rewrite Hold_uid -Huid_new //. }
  pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup) as
    (Hkey_old & Hvalid_old & Huid_in & Hno_spec_old & Hunique_old).
  split.
  - rewrite /valid_kauth map_Forall_lookup.
    intros k' obj' Hlookup_new. simpl in Hlookup_new.
    destruct (decide (k' = k)) as [->|Hneq].
    + rewrite lookup_insert_eq in Hlookup_new. injection Hlookup_new as <-.
      split_and!; try done.
      * rewrite -Huid_new -Hold_uid. exact Huid_in.
      * rewrite map_Forall_lookup. intros k'' obj'' Hlookup'' Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq'']; first done.
        rewrite lookup_insert_ne // in Hlookup''.
        eapply Hunique_old; [exact Hlookup''|].
        rewrite Huid_old_new. exact Huid_eq.
    + rewrite lookup_insert_ne // in Hlookup_new.
      pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup_new) as
        (Hkey & Hwf & Huid_in' & Hparent & Hunique).
      split_and!; try done.
      rewrite map_Forall_lookup. intros k'' obj'' Hlookup'' Huid_eq.
      destruct (decide (k'' = k)) as [->|Hneq''].
      * rewrite lookup_insert_eq in Hlookup''. injection Hlookup'' as <-.
        eapply Hunique; [exact Hlookup|].
        rewrite Huid_old_new. exact Huid_eq.
      * rewrite lookup_insert_ne // in Hlookup''.
        eapply Hunique; done.
  - split_and!.
    + rewrite map_Forall_lookup.
      intros [k' uid'] [dq agree_meta] Hfrag.
      assert ((k', uid') ≠ (k, uid)) as Hpair_ne.
      { intros Heq. inversion Heq; subst. rewrite Hmeta_bf_none in Hfrag. done. }
      assert (Hsource :
          proj_meta (mk_meta_frag k uid 1 meta ⋅ bf) !! (k', uid') =
            Some (dq, agree_meta)).
      { rewrite /proj_meta /mk_meta_frag /= lookup_op
          lookup_singleton_ne // Hfrag left_id //. }
      destruct (Hmeta _ _ Hsource) as
        (meta'0 & Hagree0 & Hvdq0 & obj' & Hobj' & Huid' & Hliving & Hmeta').
      assert (k' ≠ k) as Hkey_ne.
      { intros ->. rewrite Hlookup in Hobj'. injection Hobj' as <-.
        apply Hpair_ne. f_equal. congruence. }
      exists meta'0. split_and!; try done.
      exists obj'. split_and!; try done.
      simpl. rewrite lookup_insert_ne //.
    + rewrite map_Forall_lookup.
      intros [k' uid'] [dq agree_spec] Hfrag.
      assert (Hsource :
          proj_spec (mk_meta_frag k uid 1 meta ⋅ bf) !! (k', uid') =
            Some (dq, agree_spec)).
      { rewrite /proj_spec /mk_meta_frag /= lookup_op lookup_empty left_id.
        exact Hfrag. }
      destruct (Hspec _ _ Hsource) as
        (spec & Hagree0 & Huid & Hvdq0 & Hspec_obj).
      exists spec. split_and!; try done.
      intros obj' Hobj' Huid' Hliving'. simpl in Hobj'.
      destruct (decide (k' = k)) as [->|Hneq].
      * rewrite lookup_insert_eq in Hobj'. injection Hobj' as <-.
        exfalso. exact (Hnew_terminating Hliving').
      * rewrite lookup_insert_ne // in Hobj'. eapply Hspec_obj; done.
    + rewrite map_Forall_lookup.
      intros [k' uid'] [dq agree_status] Hfrag.
      assert (Hsource :
          proj_status (mk_meta_frag k uid 1 meta ⋅ bf) !! (k', uid') =
            Some (dq, agree_status)).
      { rewrite /proj_status /mk_meta_frag /= lookup_op lookup_empty left_id.
        exact Hfrag. }
      destruct (Hstatus _ _ Hsource) as
        (status & Hagree0 & Huid & Hvdq0 & Hstatus_obj).
      exists status. split_and!; try done.
      intros obj' Hobj' Huid' Hliving'. simpl in Hobj'.
      destruct (decide (k' = k)) as [->|Hneq].
      * rewrite lookup_insert_eq in Hobj'. injection Hobj' as <-.
        exfalso. exact (Hnew_terminating Hliving').
      * rewrite lookup_insert_ne // in Hobj'. eapply Hstatus_obj; done.
    + rewrite map_Forall_lookup.
      intros k' classification Hfrag.
      assert (Hsource :
          proj_key_classification (mk_meta_frag k uid 1 meta ⋅ bf) !! k' =
            Some classification).
      { rewrite /proj_key_classification /mk_meta_frag /= lookup_op lookup_empty
          left_id. exact Hfrag. }
      destruct (Hreservation _ _ Hsource) as
        [Hclassification_valid Hcompatible].
      split; [exact Hclassification_valid|].
      destruct classification as [agree|excl|]; [exact Hcompatible| |done].
      destruct excl as [reservation|]; [|done].
      destruct Hcompatible as [Hreserved Hstate].
      split; [exact Hreserved|].
      assert (k' ≠ k) as Hneq.
      { intros ->. exact (Hnot_reserved Hreserved). }
      destruct reservation as [|reserved_uid|reserved_uid].
      * rewrite lookup_insert_ne //.
      * destruct Hstate as (obj' & Hobj' & Huid' & Hliving).
        exists obj'. rewrite lookup_insert_ne //.
      * destruct Hstate as [Habsent|Hpresent].
        { left. rewrite lookup_insert_ne //. }
        { right. destruct Hpresent as (obj' & Hobj' & Huid' & Hterm').
          exists obj'. rewrite lookup_insert_ne //. }
Qed.

Lemma mark_terminating_reserved_kobj a k uid meta old_obj new_obj :
  valid_k_uid_obj k uid new_obj →
  (KObjectV.objectmeta new_obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
  no_speculative_parent_reference (KObjectV.objectmeta new_obj)
    (proj_used_uid a) →
  proj_state a !! k = Some old_obj →
  (●K a ⋅ ◯K (mk_meta_frag k uid 1 meta) ⋅
    ◯K (mk_reservation_frag k (Occupied uid))) ~~>
    (●K (<[k := new_obj]> (proj_state a), proj_used_uid a) ⋅
      ◯K (mk_reservation_frag k (Deleting uid))).
Proof.
  intros (Hkey_new & Huid_new & Hvalid_new)
    Hnew_terminating Hno_spec Hlookup.
  rewrite -!assoc -!view_frag_op.
  apply view_update.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  assert (Hmeta_source :
      proj_meta ((mk_meta_frag k uid 1 meta ⋅
        mk_reservation_frag k (Occupied uid)) ⋅ bf) =
      proj_meta (mk_meta_frag k uid 1 meta ⋅ bf)).
  { rewrite /proj_meta /mk_meta_frag /mk_reservation_frag /= !right_id //. }
  assert (Hspec_source :
      proj_spec ((mk_meta_frag k uid 1 meta ⋅
        mk_reservation_frag k (Occupied uid)) ⋅ bf) = proj_spec bf).
  { rewrite /proj_spec /mk_meta_frag /mk_reservation_frag /= !left_id //. }
  assert (Hstatus_source :
      proj_status ((mk_meta_frag k uid 1 meta ⋅
        mk_reservation_frag k (Occupied uid)) ⋅ bf) = proj_status bf).
  { rewrite /proj_status /mk_meta_frag /mk_reservation_frag /= !left_id //. }
  rewrite Hmeta_source in Hmeta.
  rewrite Hspec_source in Hspec.
  rewrite Hstatus_source in Hstatus.
  assert (Hmeta_bf_none : proj_meta bf !! (k, uid) = None).
  { destruct (proj_meta bf !! (k, uid)) as [[dqf agreef]|] eqn:Hbf;
      last done.
    exfalso.
    assert (Hsource :
        proj_meta (mk_meta_frag k uid 1 meta ⋅ bf) !! (k, uid) =
          Some ((DfracOwn 1,
            to_agree (A := leibnizO ObjectMetaV.t)
              (ObjectMetaV.without_resource_version meta)) ⋅
            (dqf, agreef))).
    { rewrite /proj_meta /mk_meta_frag /= lookup_op lookup_singleton_eq
        Hbf Some_op_opM //. }
    destruct (Hmeta _ _ Hsource) as (meta' & _ & Hvdq & _).
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dqf 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt. apply Hlt. done. }
  assert (Hreservation_bf_none : proj_key_classification bf !! k = None).
  { destruct (proj_key_classification bf !! k) as [classification_f|] eqn:Hbf;
      last done.
    exfalso.
    assert (Hsource :
        proj_key_classification ((mk_meta_frag k uid 1 meta ⋅
          mk_reservation_frag k (Occupied uid)) ⋅ bf) !! k =
          Some ((Cinr (Excl (Occupied uid)) : key_classificationR) ⋅
            classification_f)).
    { rewrite /proj_key_classification /mk_meta_frag /mk_reservation_frag /=
        !lookup_op !lookup_empty !left_id lookup_singleton_eq Hbf
        Some_op_opM //. }
    destruct (Hreservation _ _ Hsource) as [Hclassification_valid _].
    exact (exclusive_l (Cinr (Excl (Occupied uid)) : key_classificationR)
      classification_f Hclassification_valid). }
  assert (Hsource_meta :
      proj_meta (mk_meta_frag k uid 1 meta ⋅ bf) !! (k, uid) =
        Some (DfracOwn 1,
          to_agree (A := leibnizO ObjectMetaV.t)
            (ObjectMetaV.without_resource_version meta))).
  { rewrite /proj_meta /mk_meta_frag /= lookup_op lookup_singleton_eq
      Hmeta_bf_none right_id //. }
  destruct (Hmeta _ _ Hsource_meta) as
    (meta' & Hagree & Hvdq & old_obj' & Hold_lookup & Hold_uid &
      Hold_living & Hold_meta).
  rewrite Hlookup in Hold_lookup. injection Hold_lookup as <-.
  assert (Huid_old_new :
      (KObjectV.objectmeta old_obj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta new_obj).(ObjectMetaV.UID')).
  { rewrite Hold_uid -Huid_new //. }
  pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup) as
    (Hkey_old & Hvalid_old & Huid_in & Hno_spec_old & Hunique_old).
  split.
  - rewrite /valid_kauth map_Forall_lookup.
    intros k' obj' Hlookup_new. simpl in Hlookup_new.
    destruct (decide (k' = k)) as [->|Hneq].
    + rewrite lookup_insert_eq in Hlookup_new. injection Hlookup_new as <-.
      split_and!; try done.
      * rewrite -Huid_new -Hold_uid. exact Huid_in.
      * rewrite map_Forall_lookup. intros k'' obj'' Hlookup'' Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq'']; first done.
        rewrite lookup_insert_ne // in Hlookup''.
        eapply Hunique_old; [exact Hlookup''|].
        rewrite Huid_old_new. exact Huid_eq.
    + rewrite lookup_insert_ne // in Hlookup_new.
      pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup_new) as
        (Hkey & Hwf & Huid_in' & Hparent & Hunique).
      split_and!; try done.
      rewrite map_Forall_lookup. intros k'' obj'' Hlookup'' Huid_eq.
      destruct (decide (k'' = k)) as [->|Hneq''].
      * rewrite lookup_insert_eq in Hlookup''. injection Hlookup'' as <-.
        eapply Hunique; [exact Hlookup|].
        rewrite Huid_old_new. exact Huid_eq.
      * rewrite lookup_insert_ne // in Hlookup''.
        eapply Hunique; done.
  - split_and!.
    + rewrite /proj_meta /mk_reservation_frag /= left_id.
      rewrite map_Forall_lookup. intros [k' uid'] [dq agree_meta] Hfrag.
      assert ((k', uid') ≠ (k, uid)) as Hpair_ne.
      { intros Heq. inversion Heq; subst. rewrite Hmeta_bf_none in Hfrag. done. }
      assert (Hsource :
          proj_meta (mk_meta_frag k uid 1 meta ⋅ bf) !! (k', uid') =
            Some (dq, agree_meta)).
      { rewrite /proj_meta /mk_meta_frag /= lookup_op
          lookup_singleton_ne // Hfrag left_id //. }
      destruct (Hmeta _ _ Hsource) as
        (meta'0 & Hagree0 & Hvdq0 & obj' & Hobj' & Huid' & Hliving & Hmeta').
      assert (k' ≠ k) as Hkey_ne.
      { intros ->. rewrite Hlookup in Hobj'. injection Hobj' as <-.
        apply Hpair_ne. f_equal. congruence. }
      exists meta'0. split_and!; try done.
      exists obj'. split_and!; try done.
      simpl. rewrite lookup_insert_ne //.
    + rewrite /proj_spec /mk_reservation_frag /= left_id.
      rewrite map_Forall_lookup.
      intros [k' uid'] [dq agree_spec] Hfrag.
      destruct (Hspec _ _ Hfrag) as
        (spec & Hagree0 & Huid & Hvdq0 & Hspec_obj).
      exists spec. split_and!; try done.
      intros obj' Hobj' Huid' Hliving'. simpl in Hobj'.
      destruct (decide (k' = k)) as [->|Hneq].
      * rewrite lookup_insert_eq in Hobj'. injection Hobj' as <-.
        exfalso. exact (Hnew_terminating Hliving').
      * rewrite lookup_insert_ne // in Hobj'. eapply Hspec_obj; done.
    + rewrite /proj_status /mk_reservation_frag /= left_id.
      rewrite map_Forall_lookup.
      intros [k' uid'] [dq agree_status] Hfrag.
      destruct (Hstatus _ _ Hfrag) as
        (status & Hagree0 & Huid & Hvdq0 & Hstatus_obj).
      exists status. split_and!; try done.
      intros obj' Hobj' Huid' Hliving'. simpl in Hobj'.
      destruct (decide (k' = k)) as [->|Hneq].
      * rewrite lookup_insert_eq in Hobj'. injection Hobj' as <-.
        exfalso. exact (Hnew_terminating Hliving').
      * rewrite lookup_insert_ne // in Hobj'. eapply Hstatus_obj; done.
    + rewrite map_Forall_lookup.
      intros k' classification Hfrag.
      destruct (decide (k' = k)) as [->|Hneq].
      * rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
          lookup_singleton_eq Hreservation_bf_none right_id in Hfrag.
        inversion Hfrag. subst classification.
        split; [done|]. split.
        -- assert (Hsource :
              proj_key_classification ((mk_meta_frag k uid 1 meta ⋅
                mk_reservation_frag k (Occupied uid)) ⋅ bf) !! k =
                (Some (Cinr (Excl (Occupied uid))) :
                  option key_classificationR)).
           { rewrite /proj_key_classification /mk_meta_frag /mk_reservation_frag /=
               !lookup_op !lookup_empty !left_id lookup_singleton_eq
               Hreservation_bf_none right_id //. }
           destruct (Hreservation _ _ Hsource) as
             [_ [Hreserved _]]. exact Hreserved.
        -- right. exists new_obj. split_and!.
           ++ simpl. rewrite lookup_insert_eq //.
           ++ symmetry. exact Huid_new.
           ++ exact Hnew_terminating.
      * assert (Hlookup_bf : proj_key_classification bf !! k' =
            Some classification).
        { rewrite /proj_key_classification /mk_reservation_frag /= lookup_op
            lookup_singleton_ne // left_id in Hfrag. exact Hfrag. }
        assert (Hsource :
            proj_key_classification ((mk_meta_frag k uid 1 meta ⋅
              mk_reservation_frag k (Occupied uid)) ⋅ bf) !! k' =
              Some classification).
        { rewrite /proj_key_classification /mk_meta_frag /mk_reservation_frag /=
            !lookup_op !lookup_empty !left_id lookup_singleton_ne //
            Hlookup_bf left_id //. }
        destruct (Hreservation _ _ Hsource) as
          [Hclassification_valid Hcompatible].
        split; [exact Hclassification_valid|].
        destruct classification as [agree|excl|]; [exact Hcompatible| |done].
        destruct excl as [reservation|]; [|done].
        destruct Hcompatible as [Hreserved Hstate].
        split; [exact Hreserved|].
        destruct reservation as [|reserved_uid|reserved_uid].
        -- rewrite lookup_insert_ne //.
        -- destruct Hstate as (obj' & Hobj' & Huid' & Hliving).
           exists obj'. rewrite lookup_insert_ne //.
        -- destruct Hstate as [Habsent|Hpresent].
           ++ left. rewrite lookup_insert_ne //.
           ++ right. destruct Hpresent as (obj' & Hobj' & Huid' & Hterm').
              exists obj'. rewrite lookup_insert_ne //.
Qed.

Lemma update_meta_kobj a k uid meta prev_obj obj:
  valid_k_uid_obj k uid obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
  no_speculative_parent_reference (KObjectV.objectmeta obj) (proj_used_uid a) →
  (proj_state a) !! k = Some prev_obj →
  (KObjectV.spec prev_obj) = (KObjectV.spec obj) →
  (KObjectV.status prev_obj) = (KObjectV.status obj) →
  (●K a ⋅ ◯K (mk_meta_frag k uid 1 meta)) ~~>
    (●K ((<[k := obj]> (proj_state a)), proj_used_uid a) ⋅
      ◯K (mk_meta_frag k uid 1 (KObjectV.objectmeta obj))).
Proof.
  intros Hkuid_obj Hdeletion_timestamp Hno_spec Hak Hspec_eq Hstatus_eq.
  destruct Hkuid_obj as (Hkey_obj & Huid_obj & Hwf_obj).
  apply view_update.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  assert (Hmeta_bf_none : proj_meta bf !! (k, uid) = None).
  { destruct (proj_meta bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
	    assert (Hlookup :
	      (proj_meta (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k, uid) =
	      Some ((DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	        (ObjectMetaV.without_resource_version meta)) ⋅ (dqf, agf))).
    { rewrite /proj_meta /mk_meta_frag /= lookup_op.
      rewrite lookup_singleton_eq Hbf Some_op_opM //. }
    destruct (Hmeta _ _ Hlookup) as (meta0 & _ & Hvdq & _).
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dqf 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt.
    apply Hlt. done.
  }
	  assert (Hlookup_meta_k_old :
	    (proj_meta (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k, uid) =
	    Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	      (ObjectMetaV.without_resource_version meta))).
  { rewrite /proj_meta /mk_meta_frag /= lookup_op.
    rewrite lookup_singleton_eq Hmeta_bf_none right_id //. }
  destruct (Hmeta _ _ Hlookup_meta_k_old) as (meta0 & Hagree0 & _ & Hobj0).
  destruct Hobj0 as
    (obj0 & Hobj0_lookup & Hobj0_uid & Hprev_living & _).
	  assert (Hmeta_eqv : (ObjectMetaV.without_resource_version meta : leibnizO ObjectMetaV.t) ≡ meta0).
  { apply (inj (to_agree : leibnizO ObjectMetaV.t → agree (leibnizO ObjectMetaV.t))).
    by rewrite Hagree0.
  }
  apply leibniz_equiv in Hmeta_eqv. subst meta0.
  assert (Hobj0_eq_prev : obj0 = prev_obj).
  { rewrite Hak in Hobj0_lookup. inversion Hobj0_lookup. done. }
  subst obj0.
  assert (Huid_prev : (KObjectV.objectmeta prev_obj).(ObjectMetaV.UID') = uid).
  { done. }
  assert (Huid_obj_eq : (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid).
  { done. }
  assert (Huid_prev_obj :
    (KObjectV.objectmeta prev_obj).(ObjectMetaV.UID') =
    (KObjectV.objectmeta obj).(ObjectMetaV.UID')).
  { rewrite Huid_prev Huid_obj_eq. done. }
  assert (Huid_in_used : uid ∈ proj_used_uid a).
  { pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hak) as Hkobj_prev.
    destruct Hkobj_prev as (_ & _ & Huid_prev_in & _ & _).
    rewrite Huid_prev in Huid_prev_in. done.
  }

  split.
  - eapply map_Forall_lookup_2.
    intros k' obj' Hlookup_new.
    destruct (decide (k' = k)) as [->|Hneq_k'].
    + rewrite lookup_insert in Hlookup_new.
      destruct (decide (k = k)) as [_|Hneq_k]; [|done].
      inversion Hlookup_new; subst obj'.
      split_and!. all: try done.
      * rewrite Huid_obj_eq. done.
      * eapply map_Forall_lookup_2.
        intros k'' obj'' Hlookup_new2 Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq_k''].
        { done. }
        simpl in Hlookup_new2.
        apply lookup_insert_Some in Hlookup_new2.
        destruct Hlookup_new2 as [[Hk_eq _]|[Hk_neq Hlookup_old2]].
        { congruence. }
        pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hak) as Hkobj_prev.
        destruct Hkobj_prev as (_ & _ & _ & _ & Huniq_prev).
        eapply Huniq_prev; eauto.
        rewrite Huid_prev_obj. done.
    + simpl in Hlookup_new.
      apply lookup_insert_Some in Hlookup_new.
      destruct Hlookup_new as [[Hk_eq _]|[Hk_neq Hlookup_old]].
      { congruence. }
      pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup_old) as Hkobj_old.
      destruct Hkobj_old as (Hkey_old & Hwf_old & Huid_old_in & Hno_spec_old & Huniq_old).
      split_and!. all: try done.
      * eapply map_Forall_lookup_2.
        intros k'' obj'' Hlookup_new2 Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq_k''].
        { rewrite lookup_insert in Hlookup_new2.
          destruct (decide (k = k)) as [_|Hcontra]; [|done].
          inversion Hlookup_new2; subst obj''.
          eapply Huniq_old; [done|congruence].
        }
        simpl in Hlookup_new2.
        apply lookup_insert_Some in Hlookup_new2.
        destruct Hlookup_new2 as [[Hk_eq2 _]|[Hk_neq2 Hlookup_old2]].
        { congruence. }
        eapply Huniq_old; done.
  - split_and!.
    + intros [k' uid'] [dq' agree_meta'] Hlookup_new.
      destruct (decide ((k', uid') = (k, uid))) as [Heq_pair|Hneq_pair].
      * inversion Heq_pair. subst k' uid'.
	        assert (Hlookup_k :
	          (proj_meta (mk_meta_frag k uid 1 (KObjectV.objectmeta obj) ⋅ bf)) !! (k, uid) =
	          Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	            (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))).
        { rewrite /proj_meta /mk_meta_frag /= lookup_op.
          rewrite lookup_singleton_eq Hmeta_bf_none right_id //. }
        rewrite Hlookup_k in Hlookup_new. inversion Hlookup_new. subst dq' agree_meta'.
	        exists (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)).
	        split_and!. all: try done.
        exists obj. split_and!;
          [rewrite lookup_insert_eq; done
          |symmetry; done
          |exact Hdeletion_timestamp
          |done].
      * assert (Hlookup_old :
          (proj_meta (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k', uid') =
          Some (dq', agree_meta')).
        { rewrite /proj_meta /mk_meta_frag /= in Hlookup_new |- *.
          destruct (decide ((k, uid) = (k', uid'))) as [Heq|Hneq].
          { exfalso. apply Hneq_pair. done. }
	          assert (Hdrop_new :
	            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	              (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]}
	              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectMetaV.t))) ⋅ bf.1)
              !! (k', uid') = bf.1 !! (k', uid')).
          { rewrite lookup_op.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq'|Hneq']; [done|].
            simpl.
            rewrite ?lookup_singleton.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq''|Hneq'']; [done|].
            simpl.
            destruct (bf.1 !! (k', uid')) as [[dqf agf]|] eqn:Hbf_lookup.
            all: rewrite Hbf_lookup; done.
          }
	          assert (Hdrop_old :
	            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	              (ObjectMetaV.without_resource_version meta))]}
	              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectMetaV.t))) ⋅ bf.1)
              !! (k', uid') = bf.1 !! (k', uid')).
          { rewrite lookup_op.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq'|Hneq']; [done|].
            simpl.
            rewrite ?lookup_singleton.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq''|Hneq'']; [done|].
            simpl.
            destruct (bf.1 !! (k', uid')) as [[dqf agf]|] eqn:Hbf_lookup.
            all: rewrite Hbf_lookup; done.
          }
          rewrite Hdrop_new in Hlookup_new.
          rewrite Hdrop_old.
          done.
        }
        destruct (Hmeta _ _ Hlookup_old) as (meta' & Hagree' & Hvdq' & Hobj').
        destruct Hobj' as
          (obj' & Hlookup_obj' & Huid_obj' & Hliving_obj' & Hmeta_obj').
        assert (Hneq_k : k' ≠ k).
        { intros Hk'. subst k'.
          rewrite Hak in Hlookup_obj'. inversion Hlookup_obj'. subst obj'.
          exfalso. apply Hneq_pair. congruence.
        }
        exists meta'. split_and!. all: try done.
        exists obj'. split_and!. all: try done.
        rewrite lookup_insert_ne; done.
    + intros [k' uid'] [dq' agree_spec'] Hlookup_new.
      assert (Hlookup_old :
        (proj_spec (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k', uid') =
        Some (dq', agree_spec')).
      { rewrite /proj_spec /mk_meta_frag /= in Hlookup_new |- *.
        rewrite (lookup_op ∅ (proj_spec bf) (k', uid')) in Hlookup_new |- *.
        rewrite lookup_empty left_id in Hlookup_new |- *.
        exact Hlookup_new.
      }
      destruct (Hspec _ _ Hlookup_old) as
        (spec' & Hagree' & Huid' & Hvdq' & Hspec').
      exists spec'. split_and!. all: try done.
      intros obj0 Hlookup_obj0 Huid_obj0 Hliving_obj0.
      destruct (decide (k' = k)) as [->|Hneq_k'].
      * rewrite lookup_insert in Hlookup_obj0.
        destruct (decide (k = k)) as [_|Hneq_k]; [|done].
        inversion Hlookup_obj0. subst obj0.
        rewrite <- Hspec_eq.
        eapply Hspec'; [exact Hak| |exact Hprev_living].
        rewrite Huid_prev_obj. done.
      * simpl in Hlookup_obj0.
        apply lookup_insert_Some in Hlookup_obj0.
        destruct Hlookup_obj0 as [[Hk_eq _]|[Hk_neq Hlookup_old_obj0]].
        { congruence. }
        eapply Hspec'; done.
    + intros [k' uid'] [dq' agree_status'] Hlookup_new.
      assert (Hlookup_old :
        (proj_status (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k', uid') =
        Some (dq', agree_status')).
      { rewrite /proj_status /mk_meta_frag /= in Hlookup_new |- *.
        rewrite (lookup_op ∅ (proj_status bf) (k', uid')) in Hlookup_new |- *.
        rewrite lookup_empty left_id in Hlookup_new |- *.
        exact Hlookup_new.
      }
      destruct (Hstatus _ _ Hlookup_old) as
        (status' & Hagree' & Huid' & Hvdq' & Hstatus').
      exists status'. split_and!. all: try done.
      intros obj0 Hlookup_obj0 Huid_obj0 Hliving_obj0.
      destruct (decide (k' = k)) as [->|Hneq_k'].
      * rewrite lookup_insert in Hlookup_obj0.
        destruct (decide (k = k)) as [_|Hneq_k]; [|done].
        inversion Hlookup_obj0. subst obj0.
        rewrite <- Hstatus_eq.
        eapply Hstatus'; [exact Hak| |exact Hprev_living].
        rewrite Huid_prev_obj. done.
      * simpl in Hlookup_obj0.
        apply lookup_insert_Some in Hlookup_obj0.
        destruct Hlookup_obj0 as [[Hk_eq _]|[Hk_neq Hlookup_old_obj0]].
        { congruence. }
        eapply Hstatus'; done.
    + intros k' classification Hlookup_new.
      assert (Hlookup_old :
        proj_key_classification (mk_meta_frag k uid 1 meta ⋅ bf) !! k' =
          Some classification).
      { move: Hlookup_new.
        rewrite /proj_key_classification /mk_meta_frag /= !left_id. done. }
      destruct (Hreservation _ _ Hlookup_old) as
        [Hclassification_valid Hcompatible].
      split; [exact Hclassification_valid|].
      destruct classification as [agree|excl|]; [exact Hcompatible| |done].
      destruct excl as [reservation|]; [|done].
      destruct Hcompatible as [Hreserved Hreservation_state].
      split; [exact Hreserved|].
      destruct reservation as [|reserved_uid|reserved_uid].
      * assert (Hneq : k' ≠ k).
        { intros ->. rewrite Hak in Hreservation_state. done. }
        simpl. rewrite lookup_insert_ne //.
      * destruct Hreservation_state as
          (obj' & Hobj'_lookup & Hobj'_uid & Hobj'_living).
        destruct (decide (k' = k)) as [->|Hneq].
        { rewrite Hak in Hobj'_lookup. injection Hobj'_lookup as <-.
          exists obj. split_and!;
            [rewrite lookup_insert_eq; done
            |congruence
            |exact Hdeletion_timestamp]. }
        { exists obj'. split_and!; try done.
          rewrite lookup_insert_ne //. }
      * assert (Hneq : k' ≠ k).
        { intros ->.
          destruct Hreservation_state as
            [Habsent|(obj' & Hobj'_lookup & Hobj'_uid & Hobj'_terminating)].
          - rewrite Hak in Habsent. done.
          - rewrite Hak in Hobj'_lookup. injection Hobj'_lookup as <-.
            exact (Hobj'_terminating Hprev_living). }
        destruct Hreservation_state as [Habsent|Hpresent].
        { left. rewrite lookup_insert_ne //. }
        { right. destruct Hpresent as [obj' Hobj'].
          exists obj'. simpl. rewrite lookup_insert_ne //. }
Qed.

Lemma update_kobj a k uid meta spec prev_obj obj:
  valid_k_uid_obj k uid obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
  no_speculative_parent_reference (KObjectV.objectmeta obj) (proj_used_uid a) →
  (proj_state a) !! k = Some prev_obj →
  (KObjectV.status prev_obj) = (KObjectV.status obj) →
  (●K a ⋅
    ◯K (mk_meta_frag k uid 1 meta) ⋅
    ◯K (mk_spec_frag k uid 1 spec)) ~~>
    (●K ((<[k := obj]> (proj_state a)), proj_used_uid a) ⋅
      ◯K (mk_meta_frag k uid 1 (KObjectV.objectmeta obj)) ⋅
      ◯K (mk_spec_frag k uid 1 (KObjectV.spec obj))).
Proof.
  intros Hkuid_obj Hdeletion_timestamp Hno_spec Hak Hstatus_eq.
  destruct Hkuid_obj as (Hkey_obj & Huid_obj & Hwf_obj).
  rewrite -!assoc -!view_frag_op.
  apply view_update.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  assert (Hmeta_bf_none : proj_meta bf !! (k, uid) = None).
  { destruct (proj_meta bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
	    assert (Hlookup :
	      (proj_meta (mk_meta_frag k uid 1 meta ⋅ mk_spec_frag k uid 1 spec ⋅ bf)) !! (k, uid) =
	      Some ((DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	        (ObjectMetaV.without_resource_version meta)) ⋅ (dqf, agf))).
    { rewrite /proj_meta /mk_meta_frag /mk_spec_frag /=.
      rewrite ?lookup_op.
      rewrite lookup_singleton_eq lookup_empty right_id Hbf Some_op_opM //. }
    destruct (Hmeta _ _ Hlookup) as (meta0 & _ & Hvdq & _).
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dqf 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt.
    apply Hlt. done.
  }
  assert (Hspec_bf_none : proj_spec bf !! (k, uid) = None).
  { destruct (proj_spec bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    assert (Hlookup :
      (proj_spec (mk_meta_frag k uid 1 meta ⋅ mk_spec_frag k uid 1 spec ⋅ bf)) !! (k, uid) =
      Some ((DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t) spec) ⋅ (dqf, agf))).
    { rewrite /proj_spec /mk_meta_frag /mk_spec_frag /=.
      rewrite ?lookup_op.
      rewrite lookup_singleton_eq lookup_empty left_id Hbf Some_op_opM //. }
    destruct (Hspec _ _ Hlookup) as (spec0 & _ & _ & Hvdq & _).
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dqf 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt.
    apply Hlt. done.
  }
	  assert (Hlookup_meta_k_old :
	    (proj_meta (mk_meta_frag k uid 1 meta ⋅ mk_spec_frag k uid 1 spec ⋅ bf)) !! (k, uid) =
	    Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	      (ObjectMetaV.without_resource_version meta))).
  { rewrite /proj_meta /mk_meta_frag /mk_spec_frag /=.
    rewrite ?lookup_op.
    rewrite lookup_singleton_eq lookup_empty right_id Hmeta_bf_none right_id //. }
  destruct (Hmeta _ _ Hlookup_meta_k_old) as (meta0 & Hagree0 & _ & Hobj0).
  destruct Hobj0 as
    (obj0 & Hobj0_lookup & Hobj0_uid & Hprev_living & _).
	  assert (Hmeta_eqv : (ObjectMetaV.without_resource_version meta : leibnizO ObjectMetaV.t) ≡ meta0).
  { apply (inj (to_agree : leibnizO ObjectMetaV.t → agree (leibnizO ObjectMetaV.t))).
    by rewrite Hagree0.
  }
  apply leibniz_equiv in Hmeta_eqv. subst meta0.
  assert (Hobj0_eq_prev : obj0 = prev_obj).
  { rewrite Hak in Hobj0_lookup. inversion Hobj0_lookup. done. }
  subst obj0.
  assert (Huid_prev : (KObjectV.objectmeta prev_obj).(ObjectMetaV.UID') = uid).
  { done. }
  assert (Huid_obj_eq : (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid).
  { done. }
  assert (Huid_prev_obj :
    (KObjectV.objectmeta prev_obj).(ObjectMetaV.UID') =
    (KObjectV.objectmeta obj).(ObjectMetaV.UID')).
  { rewrite Huid_prev Huid_obj_eq. done. }
  assert (Huid_in_used : uid ∈ proj_used_uid a).
  { pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hak) as Hkobj_prev.
    destruct Hkobj_prev as (_ & _ & Huid_prev_in & _ & _).
    rewrite Huid_prev in Huid_prev_in. done.
  }

  split.
  - eapply map_Forall_lookup_2.
    intros k' obj' Hlookup_new.
    destruct (decide (k' = k)) as [->|Hneq_k'].
    + rewrite lookup_insert in Hlookup_new.
      destruct (decide (k = k)) as [_|Hneq_k]; [|done].
      inversion Hlookup_new; subst obj'.
      split_and!. all: try done.
      * rewrite Huid_obj_eq. done.
      * eapply map_Forall_lookup_2.
        intros k'' obj'' Hlookup_new2 Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq_k''].
        { done. }
        simpl in Hlookup_new2.
        apply lookup_insert_Some in Hlookup_new2.
        destruct Hlookup_new2 as [[Hk_eq _]|[Hk_neq Hlookup_old2]].
        { congruence. }
        pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hak) as Hkobj_prev.
        destruct Hkobj_prev as (_ & _ & _ & _ & Huniq_prev).
        eapply Huniq_prev; eauto.
        rewrite Huid_prev_obj. done.
    + simpl in Hlookup_new.
      apply lookup_insert_Some in Hlookup_new.
      destruct Hlookup_new as [[Hk_eq _]|[Hk_neq Hlookup_old]].
      { congruence. }
      pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup_old) as Hkobj_old.
      destruct Hkobj_old as (Hkey_old & Hwf_old & Huid_old_in & Hno_spec_old & Huniq_old).
      split_and!. all: try done.
      * eapply map_Forall_lookup_2.
        intros k'' obj'' Hlookup_new2 Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq_k''].
        { rewrite lookup_insert in Hlookup_new2.
          destruct (decide (k = k)) as [_|Hcontra]; [|done].
          inversion Hlookup_new2; subst obj''.
          eapply Huniq_old; [done|congruence].
        }
        simpl in Hlookup_new2.
        apply lookup_insert_Some in Hlookup_new2.
        destruct Hlookup_new2 as [[Hk_eq2 _]|[Hk_neq2 Hlookup_old2]].
        { congruence. }
        eapply Huniq_old; done.
  - split_and!.
    + intros [k' uid'] [dq' agree_meta'] Hlookup_new.
      destruct (decide ((k', uid') = (k, uid))) as [Heq_pair|Hneq_pair].
      * inversion Heq_pair. subst k' uid'.
	        assert (Hlookup_k :
	          (proj_meta (mk_meta_frag k uid 1 (KObjectV.objectmeta obj) ⋅
	                      mk_spec_frag k uid 1 (KObjectV.spec obj) ⋅ bf)) !! (k, uid) =
	          Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	            (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))).
        { rewrite /proj_meta /mk_meta_frag /mk_spec_frag /=.
          rewrite ?lookup_op.
          rewrite lookup_singleton_eq lookup_empty right_id Hmeta_bf_none right_id //. }
        rewrite Hlookup_k in Hlookup_new. inversion Hlookup_new. subst dq' agree_meta'.
	        exists (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)).
	        split_and!. all: try done.
        exists obj. split_and!;
          [rewrite lookup_insert_eq; done
          |symmetry; done
          |exact Hdeletion_timestamp
          |done].
      * assert (Hlookup_old :
          (proj_meta (mk_meta_frag k uid 1 meta ⋅ mk_spec_frag k uid 1 spec ⋅ bf)) !! (k', uid') =
          Some (dq', agree_meta')).
        { rewrite /proj_meta /mk_meta_frag /mk_spec_frag /= in Hlookup_new |- *.
          destruct (decide ((k, uid) = (k', uid'))) as [Heq|Hneq].
          { exfalso. apply Hneq_pair. done. }
	          assert (Hdrop_new :
	            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	              (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]}
	              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectMetaV.t))) ⋅ ∅ ⋅ bf.1)
              !! (k', uid') = bf.1 !! (k', uid')).
          { rewrite right_id.
            rewrite lookup_op.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq'|Hneq']; [done|].
            simpl.
            rewrite ?lookup_singleton.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq''|Hneq'']; [done|].
            simpl.
            destruct (bf.1 !! (k', uid')) as [[dqf agf]|] eqn:Hbf_lookup.
            all: rewrite Hbf_lookup; done.
          }
	          assert (Hdrop_old :
	            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	              (ObjectMetaV.without_resource_version meta))]}
	              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectMetaV.t))) ⋅ ∅ ⋅ bf.1)
              !! (k', uid') = bf.1 !! (k', uid')).
          { rewrite right_id.
            rewrite lookup_op.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq'|Hneq']; [done|].
            simpl.
            rewrite ?lookup_singleton.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq''|Hneq'']; [done|].
            simpl.
            destruct (bf.1 !! (k', uid')) as [[dqf agf]|] eqn:Hbf_lookup.
            all: rewrite Hbf_lookup; done.
          }
          rewrite Hdrop_new in Hlookup_new.
          rewrite Hdrop_old.
          done.
        }
        destruct (Hmeta _ _ Hlookup_old) as (meta' & Hagree' & Hvdq' & Hobj').
        destruct Hobj' as
          (obj' & Hlookup_obj' & Huid_obj' & Hliving_obj' & Hmeta_obj').
        assert (Hneq_k : k' ≠ k).
        { intros Hk'. subst k'.
          rewrite Hak in Hlookup_obj'. inversion Hlookup_obj'. subst obj'.
          exfalso. apply Hneq_pair. congruence.
        }
        exists meta'. split_and!. all: try done.
        exists obj'. split_and!. all: try done.
        rewrite lookup_insert_ne; done.
    + intros [k' uid'] [dq' agree_spec'] Hlookup_new.
      destruct (decide ((k', uid') = (k, uid))) as [Heq_pair|Hneq_pair].
      * inversion Heq_pair. subst k' uid'.
        assert (Hlookup_k :
          (proj_spec (mk_meta_frag k uid 1 (KObjectV.objectmeta obj) ⋅
                      mk_spec_frag k uid 1 (KObjectV.spec obj) ⋅ bf)) !! (k, uid) =
          Some (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t) (KObjectV.spec obj))).
        { rewrite /proj_spec /mk_meta_frag /mk_spec_frag /=.
          rewrite ?lookup_op.
          rewrite lookup_singleton_eq lookup_empty left_id Hspec_bf_none right_id //. }
        rewrite Hlookup_k in Hlookup_new. inversion Hlookup_new. subst dq' agree_spec'.
        exists (KObjectV.spec obj). split_and!. all: try done.
        intros obj0 Hlookup_obj0 Huid_obj0.
        rewrite lookup_insert in Hlookup_obj0.
        destruct (decide (k = k)) as [_|Hneq_k]; [|done].
        inversion Hlookup_obj0. subst obj0. done.
      * assert (Hlookup_old :
          (proj_spec (mk_meta_frag k uid 1 meta ⋅ mk_spec_frag k uid 1 spec ⋅ bf)) !! (k', uid') =
          Some (dq', agree_spec')).
        { rewrite /proj_spec /mk_meta_frag /mk_spec_frag /= in Hlookup_new |- *.
          destruct (decide ((k, uid) = (k', uid'))) as [Heq|Hneq].
          { exfalso. apply Hneq_pair. done. }
          assert (Hdrop_new :
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t) (KObjectV.spec obj))]}
              ⋅ proj_spec bf)
              ) !! (k', uid') = (proj_spec bf) !! (k', uid')).
          { rewrite lookup_op.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq'|Hneq']; [done|].
            simpl.
            rewrite ?lookup_singleton.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq''|Hneq'']; [done|].
            simpl.
            destruct (proj_spec bf !! (k', uid')) as [[dqf agf]|] eqn:Hbf_lookup.
            all: rewrite Hbf_lookup; done.
          }
          assert (Hdrop_old :
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectSpecV.t) spec)]}
              ⋅ proj_spec bf)
              ) !! (k', uid') = (proj_spec bf) !! (k', uid')).
          { rewrite lookup_op.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq'|Hneq']; [done|].
            simpl.
            rewrite ?lookup_singleton.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq''|Hneq'']; [done|].
            simpl.
            destruct (proj_spec bf !! (k', uid')) as [[dqf agf]|] eqn:Hbf_lookup.
            all: rewrite Hbf_lookup; done.
          }
          rewrite left_id in Hlookup_new.
          rewrite left_id.
          rewrite Hdrop_new in Hlookup_new.
          rewrite Hdrop_old.
          done.
        }
        destruct (Hspec _ _ Hlookup_old) as (spec' & Hagree' & Huid' & Hvdq' & Hspec').
        exists spec'. split_and!. all: try done.
        intros obj0 Hlookup_obj0 Huid_obj0.
        destruct (decide (k' = k)) as [->|Hneq_k'].
        { rewrite lookup_insert in Hlookup_obj0.
          destruct (decide (k = k)) as [_|Hneq_k]; [|done].
          inversion Hlookup_obj0. subst obj0.
          exfalso.
          apply Hneq_pair. congruence.
        }
        simpl in Hlookup_obj0.
        apply lookup_insert_Some in Hlookup_obj0.
        destruct Hlookup_obj0 as [[Hk_eq _]|[Hk_neq Hlookup_old_obj0]].
        { congruence. }
        eapply Hspec'; done.
    + intros [k' uid'] [dq' agree_status'] Hlookup_new.
      assert (Hlookup_old :
        (proj_status (mk_meta_frag k uid 1 meta ⋅ mk_spec_frag k uid 1 spec ⋅ bf)) !! (k', uid') =
        Some (dq', agree_status')).
      { rewrite /proj_status /mk_meta_frag /mk_spec_frag /= in Hlookup_new |- *.
        done.
      }
      destruct (Hstatus _ _ Hlookup_old) as
        (status' & Hagree' & Huid' & Hvdq' & Hstatus').
      exists status'. split_and!. all: try done.
      intros obj0 Hlookup_obj0 Huid_obj0 Hliving_obj0.
      destruct (decide (k' = k)) as [->|Hneq_k'].
      * rewrite lookup_insert in Hlookup_obj0.
        destruct (decide (k = k)) as [_|Hneq_k]; [|done].
        inversion Hlookup_obj0. subst obj0.
        rewrite <- Hstatus_eq.
        eapply Hstatus'; [exact Hak| |exact Hprev_living].
        rewrite Huid_prev_obj. done.
      * simpl in Hlookup_obj0.
        apply lookup_insert_Some in Hlookup_obj0.
        destruct Hlookup_obj0 as [[Hk_eq _]|[Hk_neq Hlookup_old_obj0]].
        { congruence. }
        eapply Hstatus'; done.
    + intros k' classification Hlookup_new.
      assert (Hlookup_old :
        proj_key_classification (mk_meta_frag k uid 1 meta ⋅
          mk_spec_frag k uid 1 spec ⋅ bf) !! k' =
          Some classification).
      { move: Hlookup_new.
        rewrite /proj_key_classification /mk_meta_frag /mk_spec_frag /= !left_id.
        done. }
      destruct (Hreservation _ _ Hlookup_old) as
        [Hclassification_valid Hcompatible].
      split; [exact Hclassification_valid|].
      destruct classification as [agree|excl|]; [exact Hcompatible| |done].
      destruct excl as [reservation|]; [|done].
      destruct Hcompatible as [Hreserved Hreservation_state].
      split; [exact Hreserved|].
      destruct reservation as [|reserved_uid|reserved_uid].
      * assert (Hneq : k' ≠ k).
        { intros ->. rewrite Hak in Hreservation_state. done. }
        simpl. rewrite lookup_insert_ne //.
      * destruct Hreservation_state as
          (obj' & Hobj'_lookup & Hobj'_uid & Hobj'_living).
        destruct (decide (k' = k)) as [->|Hneq].
        { rewrite Hak in Hobj'_lookup. injection Hobj'_lookup as <-.
          exists obj. split_and!;
            [rewrite lookup_insert_eq; done
            |congruence
            |exact Hdeletion_timestamp]. }
        { exists obj'. split_and!; try done.
          rewrite lookup_insert_ne //. }
      * assert (Hneq : k' ≠ k).
        { intros ->.
          destruct Hreservation_state as
            [Habsent|(obj' & Hobj'_lookup & Hobj'_uid & Hobj'_terminating)].
          - rewrite Hak in Habsent. done.
          - rewrite Hak in Hobj'_lookup. injection Hobj'_lookup as <-.
            exact (Hobj'_terminating Hprev_living). }
        destruct Hreservation_state as [Habsent|Hpresent].
        { left. rewrite lookup_insert_ne //. }
        { right. destruct Hpresent as [obj' Hobj'].
          exists obj'. simpl. rewrite lookup_insert_ne //. }
Qed.

Lemma update_status_kobj a k uid meta status prev_obj obj:
  valid_k_uid_obj k uid obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
  no_speculative_parent_reference (KObjectV.objectmeta obj) (proj_used_uid a) →
  (proj_state a) !! k = Some prev_obj →
  (KObjectV.spec prev_obj) = (KObjectV.spec obj) →
    (●K a ⋅
    ◯K (mk_meta_frag k uid 1 meta) ⋅
    ◯K (mk_status_frag k uid 1 status)) ~~>
    (●K ((<[k := obj]> (proj_state a)), proj_used_uid a) ⋅
      ◯K (mk_meta_frag k uid 1 (KObjectV.objectmeta obj)) ⋅
      ◯K (mk_status_frag k uid 1 (KObjectV.status obj))).
Proof.
  intros Hkuid_obj Hdeletion_timestamp Hno_spec Hak Hspec_eq.
  destruct Hkuid_obj as (Hkey_obj & Huid_obj & Hwf_obj).
  rewrite -!assoc -!view_frag_op.
  apply view_update.
  intros n bf [Hvalid [Hmeta [Hspec [Hstatus Hreservation]]]].
  assert (Hmeta_bf_none : proj_meta bf !! (k, uid) = None).
  { destruct (proj_meta bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
	    assert (Hlookup :
	      (proj_meta (mk_meta_frag k uid 1 meta ⋅ mk_status_frag k uid 1 status ⋅ bf)) !! (k, uid) =
	      Some ((DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	        (ObjectMetaV.without_resource_version meta)) ⋅ (dqf, agf))).
    { rewrite /proj_meta /mk_meta_frag /mk_status_frag /=.
      rewrite ?lookup_op.
      rewrite lookup_singleton_eq lookup_empty right_id Hbf Some_op_opM //. }
    destruct (Hmeta _ _ Hlookup) as (meta0 & _ & Hvdq & _).
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dqf 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt.
    apply Hlt. done.
  }
  assert (Hstatus_bf_none : proj_status bf !! (k, uid) = None).
  { destruct (proj_status bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    assert (Hlookup :
      (proj_status (mk_meta_frag k uid 1 meta ⋅ mk_status_frag k uid 1 status ⋅ bf)) !! (k, uid) =
      Some ((DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t) status) ⋅ (dqf, agf))).
    { rewrite /proj_status /mk_meta_frag /mk_status_frag /=.
      rewrite ?lookup_op.
      rewrite lookup_singleton_eq lookup_empty left_id Hbf Some_op_opM //. }
    destruct (Hstatus _ _ Hlookup) as (status0 & _ & _ & Hvdq & _).
    simpl in Hvdq.
    pose proof (dfrac_valid_own_l dqf 1 Hvdq) as Hlt.
    apply (Qp.lt_nge 1 1) in Hlt.
    apply Hlt. done.
  }
	  assert (Hlookup_meta_k_old :
	    (proj_meta (mk_meta_frag k uid 1 meta ⋅ mk_status_frag k uid 1 status ⋅ bf)) !! (k, uid) =
	    Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	      (ObjectMetaV.without_resource_version meta))).
  { rewrite /proj_meta /mk_meta_frag /mk_status_frag /=.
    rewrite ?lookup_op.
    rewrite lookup_singleton_eq lookup_empty right_id Hmeta_bf_none right_id //. }
  destruct (Hmeta _ _ Hlookup_meta_k_old) as (meta0 & Hagree0 & _ & Hobj0).
  destruct Hobj0 as
    (obj0 & Hobj0_lookup & Hobj0_uid & Hprev_living & _).
	  assert (Hmeta_eqv : (ObjectMetaV.without_resource_version meta : leibnizO ObjectMetaV.t) ≡ meta0).
  { apply (inj (to_agree : leibnizO ObjectMetaV.t → agree (leibnizO ObjectMetaV.t))).
    by rewrite Hagree0.
  }
  apply leibniz_equiv in Hmeta_eqv. subst meta0.
  assert (Hobj0_eq_prev : obj0 = prev_obj).
  { rewrite Hak in Hobj0_lookup. inversion Hobj0_lookup. done. }
  subst obj0.
  assert (Huid_prev : (KObjectV.objectmeta prev_obj).(ObjectMetaV.UID') = uid).
  { done. }
  assert (Huid_obj_eq : (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid).
  { done. }
  assert (Huid_prev_obj :
    (KObjectV.objectmeta prev_obj).(ObjectMetaV.UID') =
    (KObjectV.objectmeta obj).(ObjectMetaV.UID')).
  { rewrite Huid_prev Huid_obj_eq. done. }
  assert (Huid_in_used : uid ∈ proj_used_uid a).
  { pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hak) as Hkobj_prev.
    destruct Hkobj_prev as (_ & _ & Huid_prev_in & _ & _).
    rewrite Huid_prev in Huid_prev_in. done.
  }

  split.
  - eapply map_Forall_lookup_2.
    intros k' obj' Hlookup_new.
    destruct (decide (k' = k)) as [->|Hneq_k'].
    + rewrite lookup_insert in Hlookup_new.
      destruct (decide (k = k)) as [_|Hneq_k]; [|done].
      inversion Hlookup_new; subst obj'.
      split_and!. all: try done.
      * rewrite Huid_obj_eq. done.
      * eapply map_Forall_lookup_2.
        intros k'' obj'' Hlookup_new2 Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq_k''].
        { done. }
        simpl in Hlookup_new2.
        apply lookup_insert_Some in Hlookup_new2.
        destruct Hlookup_new2 as [[Hk_eq _]|[Hk_neq Hlookup_old2]].
        { congruence. }
        pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hak) as Hkobj_prev.
        destruct Hkobj_prev as (_ & _ & _ & _ & Huniq_prev).
        eapply Huniq_prev; eauto.
        rewrite Huid_prev_obj. done.
    + simpl in Hlookup_new.
      apply lookup_insert_Some in Hlookup_new.
      destruct Hlookup_new as [[Hk_eq _]|[Hk_neq Hlookup_old]].
      { congruence. }
      pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup_old) as Hkobj_old.
      destruct Hkobj_old as (Hkey_old & Hwf_old & Huid_old_in & Hno_spec_old & Huniq_old).
      split_and!. all: try done.
      * eapply map_Forall_lookup_2.
        intros k'' obj'' Hlookup_new2 Huid_eq.
        destruct (decide (k'' = k)) as [->|Hneq_k''].
        { rewrite lookup_insert in Hlookup_new2.
          destruct (decide (k = k)) as [_|Hcontra]; [|done].
          inversion Hlookup_new2; subst obj''.
          eapply Huniq_old; [done|congruence].
        }
        simpl in Hlookup_new2.
        apply lookup_insert_Some in Hlookup_new2.
        destruct Hlookup_new2 as [[Hk_eq2 _]|[Hk_neq2 Hlookup_old2]].
        { congruence. }
        eapply Huniq_old; done.
  - split_and!.
    + intros [k' uid'] [dq' agree_meta'] Hlookup_new.
      destruct (decide ((k', uid') = (k, uid))) as [Heq_pair|Hneq_pair].
      * inversion Heq_pair. subst k' uid'.
	        assert (Hlookup_k :
	          (proj_meta (mk_meta_frag k uid 1 (KObjectV.objectmeta obj) ⋅
	                      mk_status_frag k uid 1 (KObjectV.status obj) ⋅ bf)) !! (k, uid) =
	          Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	            (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))).
        { rewrite /proj_meta /mk_meta_frag /mk_status_frag /=.
          rewrite ?lookup_op.
          rewrite lookup_singleton_eq lookup_empty right_id Hmeta_bf_none right_id //. }
        rewrite Hlookup_k in Hlookup_new. inversion Hlookup_new. subst dq' agree_meta'.
	        exists (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)).
	        split_and!. all: try done.
        exists obj. split_and!;
          [rewrite lookup_insert_eq; done
          |symmetry; done
          |exact Hdeletion_timestamp
          |done].
      * assert (Hlookup_old :
          (proj_meta (mk_meta_frag k uid 1 meta ⋅ mk_status_frag k uid 1 status ⋅ bf)) !! (k', uid') =
          Some (dq', agree_meta')).
        { rewrite /proj_meta /mk_meta_frag /mk_status_frag /= in Hlookup_new |- *.
          destruct (decide ((k, uid) = (k', uid'))) as [Heq|Hneq].
          { exfalso. apply Hneq_pair. done. }
	          assert (Hdrop_new :
	            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	              (ObjectMetaV.without_resource_version (KObjectV.objectmeta obj)))]}
	              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectMetaV.t))) ⋅ ∅ ⋅ bf.1)
              !! (k', uid') = bf.1 !! (k', uid')).
          { rewrite right_id.
            rewrite lookup_op.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq'|Hneq']; [done|].
            simpl.
            rewrite ?lookup_singleton.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq''|Hneq'']; [done|].
            simpl.
            destruct (bf.1 !! (k', uid')) as [[dqf agf]|] eqn:Hbf_lookup.
            all: rewrite Hbf_lookup; done.
          }
	          assert (Hdrop_old :
	            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
	              (ObjectMetaV.without_resource_version meta))]}
	              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectMetaV.t))) ⋅ ∅ ⋅ bf.1)
              !! (k', uid') = bf.1 !! (k', uid')).
          { rewrite right_id.
            rewrite lookup_op.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq'|Hneq']; [done|].
            simpl.
            rewrite ?lookup_singleton.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq''|Hneq'']; [done|].
            simpl.
            destruct (bf.1 !! (k', uid')) as [[dqf agf]|] eqn:Hbf_lookup.
            all: rewrite Hbf_lookup; done.
          }
          rewrite Hdrop_new in Hlookup_new.
          rewrite Hdrop_old.
          done.
        }
        destruct (Hmeta _ _ Hlookup_old) as (meta' & Hagree' & Hvdq' & Hobj').
        destruct Hobj' as
          (obj' & Hlookup_obj' & Huid_obj' & Hliving_obj' & Hmeta_obj').
        assert (Hneq_k : k' ≠ k).
        { intros Hk'. subst k'.
          rewrite Hak in Hlookup_obj'. inversion Hlookup_obj'. subst obj'.
          exfalso. apply Hneq_pair. congruence.
        }
        exists meta'. split_and!. all: try done.
        exists obj'. split_and!. all: try done.
        rewrite lookup_insert_ne; done.
    + intros [k' uid'] [dq' agree_spec'] Hlookup_new.
      assert (Hlookup_old :
        (proj_spec (mk_meta_frag k uid 1 meta ⋅ mk_status_frag k uid 1 status ⋅ bf)) !! (k', uid') =
        Some (dq', agree_spec')).
      { rewrite /proj_spec /mk_meta_frag /mk_status_frag /= in Hlookup_new |- *.
        done.
      }
      destruct (Hspec _ _ Hlookup_old) as
        (spec' & Hagree' & Huid' & Hvdq' & Hspec').
      exists spec'. split_and!. all: try done.
      intros obj0 Hlookup_obj0 Huid_obj0 Hliving_obj0.
      destruct (decide (k' = k)) as [->|Hneq_k'].
      * rewrite lookup_insert in Hlookup_obj0.
        destruct (decide (k = k)) as [_|Hneq_k]; [|done].
        inversion Hlookup_obj0. subst obj0.
        rewrite <- Hspec_eq.
        eapply Hspec'; [exact Hak| |exact Hprev_living].
        rewrite Huid_prev_obj. done.
      * simpl in Hlookup_obj0.
        apply lookup_insert_Some in Hlookup_obj0.
        destruct Hlookup_obj0 as [[Hk_eq _]|[Hk_neq Hlookup_old_obj0]].
        { congruence. }
        eapply Hspec'; done.
    + intros [k' uid'] [dq' agree_status'] Hlookup_new.
      destruct (decide ((k', uid') = (k, uid))) as [Heq_pair|Hneq_pair].
      * inversion Heq_pair. subst k' uid'.
        assert (Hlookup_k :
          (proj_status (mk_meta_frag k uid 1 (KObjectV.objectmeta obj) ⋅
                        mk_status_frag k uid 1 (KObjectV.status obj) ⋅ bf)) !! (k, uid) =
          Some (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t) (KObjectV.status obj))).
        { rewrite /proj_status /mk_meta_frag /mk_status_frag /=.
          rewrite ?lookup_op.
          rewrite lookup_singleton_eq lookup_empty left_id Hstatus_bf_none right_id //. }
        rewrite Hlookup_k in Hlookup_new. inversion Hlookup_new. subst dq' agree_status'.
        exists (KObjectV.status obj). split_and!. all: try done.
        intros obj0 Hlookup_obj0 Huid_obj0 Hliving_obj0.
        rewrite lookup_insert in Hlookup_obj0.
        destruct (decide (k = k)) as [_|Hneq_k]; [|done].
        inversion Hlookup_obj0. subst obj0. done.
      * assert (Hlookup_old :
          (proj_status (mk_meta_frag k uid 1 meta ⋅ mk_status_frag k uid 1 status ⋅ bf)) !! (k', uid') =
          Some (dq', agree_status')).
        { rewrite /proj_status /mk_meta_frag /mk_status_frag /= in Hlookup_new |- *.
          destruct (decide ((k, uid) = (k', uid'))) as [Heq|Hneq].
          { exfalso. apply Hneq_pair. done. }
          assert (Hdrop_new :
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t) (KObjectV.status obj))]}
              ⋅ proj_status bf)
              ) !! (k', uid') = (proj_status bf) !! (k', uid')).
          { rewrite lookup_op.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq'|Hneq']; [done|].
            simpl.
            rewrite ?lookup_singleton.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq''|Hneq'']; [done|].
            simpl.
            destruct (proj_status bf !! (k', uid')) as [[dqf agf]|] eqn:Hbf_lookup.
            all: rewrite Hbf_lookup; done.
          }
          assert (Hdrop_old :
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t) status)]}
              ⋅ proj_status bf)
              ) !! (k', uid') = (proj_status bf) !! (k', uid')).
          { rewrite lookup_op.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq'|Hneq']; [done|].
            simpl.
            rewrite ?lookup_singleton.
            destruct (decide ((k, uid) = (k', uid'))) as [Heq''|Hneq'']; [done|].
            simpl.
            destruct (proj_status bf !! (k', uid')) as [[dqf agf]|] eqn:Hbf_lookup.
            all: rewrite Hbf_lookup; done.
          }
          rewrite left_id in Hlookup_new.
          rewrite left_id.
          rewrite Hdrop_new in Hlookup_new.
          rewrite Hdrop_old.
          done.
        }
        destruct (Hstatus _ _ Hlookup_old) as
          (status' & Hagree' & Huid' & Hvdq' & Hstatus').
        exists status'. split_and!. all: try done.
        intros obj0 Hlookup_obj0 Huid_obj0 Hliving_obj0.
        destruct (decide (k' = k)) as [->|Hneq_k'].
        { rewrite lookup_insert in Hlookup_obj0.
          destruct (decide (k = k)) as [_|Hneq_k]; [|done].
          inversion Hlookup_obj0. subst obj0.
          exfalso.
          apply Hneq_pair. congruence.
        }
        simpl in Hlookup_obj0.
        apply lookup_insert_Some in Hlookup_obj0.
        destruct Hlookup_obj0 as [[Hk_eq _]|[Hk_neq Hlookup_old_obj0]].
        { congruence. }
        eapply Hstatus'; done.
    + intros k' classification Hlookup_new.
      assert (Hlookup_old :
        proj_key_classification (mk_meta_frag k uid 1 meta ⋅
          mk_status_frag k uid 1 status ⋅ bf) !! k' =
          Some classification).
      { move: Hlookup_new.
        rewrite /proj_key_classification /mk_meta_frag /mk_status_frag /= !left_id.
        done. }
      destruct (Hreservation _ _ Hlookup_old) as
        [Hclassification_valid Hcompatible].
      split; [exact Hclassification_valid|].
      destruct classification as [agree|excl|]; [exact Hcompatible| |done].
      destruct excl as [reservation|]; [|done].
      destruct Hcompatible as [Hreserved Hreservation_state].
      split; [exact Hreserved|].
      destruct reservation as [|reserved_uid|reserved_uid].
      * assert (Hneq : k' ≠ k).
        { intros ->. rewrite Hak in Hreservation_state. done. }
        simpl. rewrite lookup_insert_ne //.
      * destruct Hreservation_state as
          (obj' & Hobj'_lookup & Hobj'_uid & Hobj'_living).
        destruct (decide (k' = k)) as [->|Hneq].
        { rewrite Hak in Hobj'_lookup. injection Hobj'_lookup as <-.
          exists obj. split_and!;
            [rewrite lookup_insert_eq; done
            |congruence
            |exact Hdeletion_timestamp]. }
        { exists obj'. split_and!; try done.
          rewrite lookup_insert_ne //. }
      * assert (Hneq : k' ≠ k).
        { intros ->.
          destruct Hreservation_state as
            [Habsent|(obj' & Hobj'_lookup & Hobj'_uid & Hobj'_terminating)].
          - rewrite Hak in Habsent. done.
          - rewrite Hak in Hobj'_lookup. injection Hobj'_lookup as <-.
            exact (Hobj'_terminating Hprev_living). }
        destruct Hreservation_state as [Habsent|Hpresent].
        { left. rewrite lookup_insert_ne //. }
        { right. destruct Hpresent as [obj' Hobj'].
          exists obj'. simpl. rewrite lookup_insert_ne //. }
Qed.

Class kviewG Σ :=
  { #[global] kview_inG :: inG Σ (viewR view_rel); }.

Definition kviewΣ :=
  #[GFunctor (viewR view_rel)].

#[global]
Instance subG_kviewG Σ :
  subG kviewΣ Σ → kviewG Σ.
Proof. solve_inG. Qed.

Context `{!kviewG Σ}.

Global Instance own_auth_timeless γ a : Timeless (own γ (●K a)).
Proof. apply _. Qed.

Global Instance own_frag_timeless γ b : Timeless (own γ (◯K b)).
Proof. apply _. Qed.

Definition own_auth γ (state: gmap KKey.t KObjectV.t) (used_uid: gsetO types.UID.t) : iProp Σ :=
  own γ (●K (state, used_uid)).

Definition own_meta_frag γ k uid dq m : iProp Σ :=
  own γ (◯K (mk_meta_frag k uid dq m)).

Definition own_spec_frag γ k uid dq sp : iProp Σ :=
  own γ (◯K (mk_spec_frag k uid dq sp)).

Definition own_status_frag γ k uid dq st : iProp Σ :=
  own γ (◯K (mk_status_frag k uid dq st)).

Definition own_reservation_frag γ k status : iProp Σ :=
  own γ (◯K (mk_reservation_frag k status)).

Definition own_unreserved_frag γ k : iProp Σ :=
  own γ (◯K (mk_unreserved_frag k)).

Global Instance own_unreserved_frag_persistent γ k :
  Persistent (own_unreserved_frag γ k).
Proof. apply _. Qed.

Lemma init :
  ⊢ |==> ∃ γ,
    own_auth γ (∅ : gmap KKey.t KObjectV.t)
      (∅ : gset types.UID.t).
Proof.
  unfold own_auth.
  iMod (own_alloc (●K
    ((∅ : gmap KKey.t KObjectV.t),
      (∅ : gset types.UID.t)))) as (γ) "Hauth".
  { apply (proj2 (view_auth_dfrac_valid view_rel 1
      ((∅ : gmap KKey.t KObjectV.t),
        (∅ : gset types.UID.t)))).
    split; [done|].
    intros n.
    change (view_rel_raw n
      ((∅ : gmap KKey.t KObjectV.t),
        (∅ : gset types.UID.t)) ε).
    split.
    { rewrite /valid_kauth map_Forall_lookup /=.
      intros i x Hlookup. rewrite lookup_empty in Hlookup. done. }
    rewrite /compatible_kfrag.
    split.
    { rewrite map_Forall_lookup. intros i x Hlookup.
      rewrite lookup_empty in Hlookup. done. }
    split.
    { rewrite map_Forall_lookup. intros i x Hlookup.
      rewrite lookup_empty in Hlookup. done. }
    split.
    { rewrite map_Forall_lookup. intros i x Hlookup.
      rewrite lookup_empty in Hlookup. done. }
    { rewrite map_Forall_lookup. intros i x Hlookup.
      rewrite lookup_empty in Hlookup. done. } }
  iModIntro. iExists γ. iExact "Hauth".
Qed.

Lemma own_auth_valid {γ state used_uid} k obj:
  own_auth γ state used_uid -∗
  ⌜ state !! k = Some obj →
  k = KObjectV.key obj ∧
  KObjectV.valid obj ∧
  (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∈ used_uid ∧
  no_speculative_parent_reference (KObjectV.objectmeta obj) used_uid ∧
  map_Forall (λ k' obj',
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta obj').(ObjectMetaV.UID') → k = k'
  ) state ⌝.
Proof.
  iIntros "Hauth".
  iDestruct (own_valid with "Hauth") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  intros Hlookup.
  pose proof (proj1 (view_auth_dfrac_validN view_rel 0%nat 1
    (state, used_uid)) Hvalid0) as [_ Hrel0].
  assert (Hvalid : ✓ (●K (state, used_uid))).
  { rewrite /kview_auth.
    apply (proj2 (view_auth_dfrac_valid view_rel 1 (state, used_uid))).
    split; [done|].
    intros n.
    change (view_rel_raw n (state, used_uid) ε).
    exact Hrel0.
  }
  eapply (auth_valid (state, used_uid) k obj).
  - exact Hvalid.
  - simpl. exact Hlookup.
Qed.

Lemma own_auth_valid2 {γ state used_uid} k obj:
  state !! k = Some obj →
  own_auth γ state used_uid -∗
  ⌜ k = KObjectV.key obj ∧
  KObjectV.valid obj ∧
  (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∈ used_uid ∧
  no_speculative_parent_reference (KObjectV.objectmeta obj) used_uid ∧
  map_Forall (λ k' obj',
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta obj').(ObjectMetaV.UID') → k = k'
  ) state ⌝.
Proof.
  iIntros (Hlookup) "Hauth".
  iDestruct (own_auth_valid k obj with "Hauth") as %Hvalid.
  iPureIntro.
  exact (Hvalid Hlookup).
Qed.

Lemma own_auth_valid_forall {γ state used_uid}:
  own_auth γ state used_uid -∗
  ⌜ ∀ k obj,
  state !! k = Some obj →
  k = KObjectV.key obj ∧
  KObjectV.valid obj ∧
  (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∈ used_uid ∧
  no_speculative_parent_reference (KObjectV.objectmeta obj) used_uid ∧
  map_Forall (λ k' obj',
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta obj').(ObjectMetaV.UID') → k = k'
  ) state ⌝.
Proof.
  iIntros "Hauth".
  iDestruct (own_valid with "Hauth") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  pose proof (proj1 (view_auth_dfrac_validN view_rel 0%nat 1 (state, used_uid)) Hvalid0)
    as [_ Hrel0].
  assert (Hvalid : ✓ (●K (state, used_uid))).
  { rewrite /kview_auth.
    apply (proj2 (view_auth_dfrac_valid view_rel 1 (state, used_uid))).
    split; [done|].
    intros n.
    change (view_rel_raw n (state, used_uid) ε).
    exact Hrel0.
  }
  exact (auth_valid_forall (state, used_uid) Hvalid).
Qed.

Lemma own_reservation_valid {γ state used_uid k status}:
  own_auth γ state used_uid -∗
  own_reservation_frag γ k status -∗
  ⌜ reserved_key_pred k ∧
    match status with
    | Available => state !! k = None
    | Occupied uid =>
        ∃ obj,
          state !! k = Some obj ∧
          (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid ∧
          (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None
    | Deleting uid =>
        state !! k = None ∨
        ∃ obj,
          state !! k = Some obj ∧
          (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid ∧
          (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') ≠ None
    end ⌝.
Proof.
  iIntros "Hauth Hreservation".
  iDestruct (own_valid_2 with "Hauth Hreservation") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  rewrite /own_auth /own_reservation_frag /kview_auth /kview_frag in Hvalid0.
  pose proof (proj1 (view_both_validN view_rel 0%nat
    (state, used_uid) (mk_reservation_frag k status)) Hvalid0) as Hrel0.
  assert (Hvalid :
    ✓ (●K (state, used_uid) ⋅ ◯K (mk_reservation_frag k status))).
  { rewrite /kview_auth /kview_frag.
    apply (proj2 (view_both_valid view_rel
      (state, used_uid) (mk_reservation_frag k status))).
    intros n. exact Hrel0. }
  apply (auth_reservation_valid (state, used_uid) k status).
  exact Hvalid.
Qed.

Lemma own_meta_reservation_valid {γ k uid dq meta status} :
  own_meta_frag γ k uid dq meta -∗
  own_reservation_frag γ k status -∗
  ⌜ status = Occupied uid ⌝.
Proof.
  iIntros "Hmeta Hreservation".
  iDestruct (own_valid_2 with "Hmeta Hreservation") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid.
  iPureIntro.
  exact (meta_reservation_valid k uid dq meta status Hvalid).
Qed.

Lemma own_unreserved_frag_valid {γ k} :
  own_unreserved_frag γ k -∗
  ⌜¬ reserved_key_pred k⌝.
Proof.
  iIntros "Hunreserved".
  iDestruct (own_valid with "Hunreserved") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid.
  iPureIntro.
  exact (unreserved_frag_valid 0%nat k Hvalid).
Qed.

Lemma own_meta_valid {γ k uid dq meta}:
  own_meta_frag γ k uid dq meta -∗
    ⌜ k.(KKey.Name') = meta.(ObjectMetaV.Name') ∧
    k.(KKey.Namespace') = meta.(ObjectMetaV.Namespace') ∧
    uid = meta.(ObjectMetaV.UID') ∧
    ObjectMetaV.valid k.(KKey.Kind') meta ∧
    meta.(ObjectMetaV.DeletionTimestamp') = None ⌝.
Proof.
  iIntros "Hmeta".
  iDestruct (own_valid with "Hmeta") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  rewrite /kview_frag in Hvalid0.
  destruct (proj1 (view_frag_validN view_rel 0%nat (mk_meta_frag k uid dq meta)) Hvalid0)
    as [a Hrel0].
  assert (Hvalid : ✓ (◯K (mk_meta_frag k uid dq meta))).
  { rewrite /kview_frag.
    apply (proj2 (view_frag_valid view_rel (mk_meta_frag k uid dq meta))).
    intros n. exists a. exact Hrel0.
  }
  eapply meta_valid.
  done.
Qed.

Lemma own_meta_meta_false {γ k1 uid1 meta1 k2 uid2 meta2} :
  k1 = k2 →
  own_meta_frag γ k1 uid1 1 meta1 -∗
  own_meta_frag γ k2 uid2 1 meta2 -∗
  False.
Proof.
  iIntros (Hk_eq) "Hmeta1 Hmeta2".
  iDestruct (own_valid_2 with "Hmeta1 Hmeta2") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  assert (Hvalid :
    ✓ (◯K (mk_meta_frag k1 uid1 1 meta1) ⋅ ◯K (mk_meta_frag k2 uid2 1 meta2))).
  { rewrite /kview_frag -view_frag_op in Hvalid0 |- *.
    destruct (proj1 (view_frag_validN view_rel 0%nat
      (mk_meta_frag k1 uid1 1 meta1 ⋅ mk_meta_frag k2 uid2 1 meta2)) Hvalid0)
      as [a Hrel0].
    apply (proj2 (view_frag_valid view_rel
      (mk_meta_frag k1 uid1 1 meta1 ⋅ mk_meta_frag k2 uid2 1 meta2))).
    intros n.
    exists a.
    exact Hrel0.
  }
  exact (meta_meta_false k1 uid1 meta1 k2 uid2 meta2 Hk_eq Hvalid).
Qed.

Lemma own_meta_exists {γ state used_uid k uid dq meta}:
	  own_auth γ state used_uid -∗
	  own_meta_frag γ k uid dq meta -∗
	    ⌜ ∃ obj, state !! k = Some obj ∧
	    (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid ∧
	    ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta obj) meta ∧
	    meta.(ObjectMetaV.UID') ∈ used_uid ⌝.
Proof.
  iIntros "Hauth Hmeta".
  iDestruct (own_valid_2 with "Hauth Hmeta") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  rewrite /kview_auth /kview_frag in Hvalid0.
  pose proof (proj1 (view_both_validN view_rel 0%nat
    (state, used_uid) (mk_meta_frag k uid dq meta)) Hvalid0) as Hrel0.
  assert (Hvalid : ✓ (●K (state, used_uid) ⋅ ◯K (mk_meta_frag k uid dq meta))).
  { rewrite /kview_auth /kview_frag.
    apply (proj2 (view_both_valid view_rel (state, used_uid) (mk_meta_frag k uid dq meta))).
    intros n. exact Hrel0.
  }
  pose proof (auth_meta_valid (state, used_uid) k uid dq meta Hvalid) as Hexists.
  exact Hexists.
Qed.

Lemma own_meta_exists2 {γ state used_uid obj k uid dq meta}:
	  state !! k = Some obj →
	  own_auth γ state used_uid -∗
	  own_meta_frag γ k uid dq meta -∗
	    ⌜ (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid ∧
	    ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta obj) meta ∧
	    meta.(ObjectMetaV.UID') ∈ used_uid ⌝.
Proof.
  iIntros (Hlookup) "Hauth Hmeta".
	  iDestruct (own_meta_exists with "Hauth Hmeta") as %(obj' & Hlookup' & Huid_obj & Hmeta_eq & Huid_in).
  iPureIntro.
  rewrite Hlookup in Hlookup'.
  injection Hlookup' as <-.
	  split_and!; done.
Qed.

Lemma own_meta_living {γ state used_uid obj k uid dq meta} :
  state !! k = Some obj →
  own_auth γ state used_uid -∗
  own_meta_frag γ k uid dq meta -∗
    ⌜ (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None ⌝.
Proof.
  iIntros (Hlookup) "Hauth Hmeta".
  iDestruct (own_valid_2 with "Hauth Hmeta") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  rewrite /kview_auth /kview_frag in Hvalid0.
  pose proof (proj1 (view_both_validN view_rel 0%nat
    (state, used_uid) (mk_meta_frag k uid dq meta)) Hvalid0) as Hrel0.
  assert (Hvalid :
      ✓ (●K (state, used_uid) ⋅ ◯K (mk_meta_frag k uid dq meta))).
  { rewrite /kview_auth /kview_frag.
    apply (proj2 (view_both_valid view_rel
      (state, used_uid) (mk_meta_frag k uid dq meta))).
    intros n. exact Hrel0. }
  destruct (auth_meta_living (state, used_uid) k uid dq meta Hvalid) as
    (obj' & Hlookup' & Huid & Hliving).
  rewrite Hlookup in Hlookup'. injection Hlookup' as <-.
  exact Hliving.
Qed.

Lemma own_meta_map_exists {γ state used_uid K A} `{Countable K}
  (key_of : K → A → KKey.t) (meta_of : K → A → ObjectMetaV.t) (m : gmap K A) dq :
  own_auth γ state used_uid -∗
  ([∗ map] k↦x ∈ m, own_meta_frag γ (key_of k x) (meta_of k x).(ObjectMetaV.UID') dq (meta_of k x)) -∗
	  ⌜ map_Forall (λ k x, ∃ obj, state !! key_of k x = Some obj ∧
	    (KObjectV.objectmeta obj).(ObjectMetaV.UID') = (meta_of k x).(ObjectMetaV.UID') ∧
	    ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta obj) (meta_of k x)) m ⌝ ∗
    ⌜ map_Forall (λ k x, (meta_of k x).(ObjectMetaV.UID') ∈ used_uid) m ⌝.
Proof.
  iIntros "Hauth Hm".
  iInduction m as [|k x m Hnotin] "IH" using map_ind.
  - rewrite big_sepM_empty.
    iFrame.
    iPureIntro.
    split; apply map_Forall_empty.
  - rewrite big_sepM_insert //.
    iDestruct "Hm" as "[Hx Hm]".
    iPoseProof (own_meta_exists with "Hauth Hx") as "%Hhead".
    iDestruct ("IH" with "Hauth Hm") as "(%Hmeta_forall & %Huid_forall)".
    iFrame.
    iPureIntro.
	    destruct Hhead as (obj & Hlookup & Huid_obj & Hmeta_eq & Huid_in).
    split.
    + apply map_Forall_insert_2.
	      * exists obj. split_and!; done.
      * exact Hmeta_forall.
    + apply map_Forall_insert_2.
      * exact Huid_in.
      * exact Huid_forall.
Qed.

Lemma own_meta_list_no_dup {γ A} (key_of : A → KKey.t) (meta_of : A → ObjectMetaV.t) xs:
  ([∗ list] x ∈ xs, own_meta_frag γ (key_of x) (meta_of x).(ObjectMetaV.UID') 1 (meta_of x)) -∗
    ⌜ NoDup (key_of <$> xs) ⌝.
Proof.
  iIntros "Hxs".
  iInduction xs as [|x xs] "IH".
  - rewrite big_sepL_nil.
    iPureIntro.
    constructor.
  - rewrite big_sepL_cons.
    iDestruct "Hxs" as "[Hx Hxs]".
    destruct (decide (key_of x ∈ key_of <$> xs)) as [Hin|Hnotin].
    + apply list_elem_of_fmap_1 in Hin as (y & Hkey_eq & Hyin).
      iDestruct (big_sepL_elem_of_acc with "Hxs") as "[Hy _]"; first exact Hyin.
      iExFalso.
      iApply (own_meta_meta_false Hkey_eq with "Hx Hy").
    + iDestruct ("IH" with "Hxs") as %Hnodup.
      iPureIntro.
      constructor; done.
Qed.

Lemma own_meta_list_exists {γ state used_uid A} (key_of : A → KKey.t) (meta_of : A → ObjectMetaV.t) xs dq :
  own_auth γ state used_uid -∗
  ([∗ list] x ∈ xs, own_meta_frag γ (key_of x) (meta_of x).(ObjectMetaV.UID') dq (meta_of x)) -∗
	  ⌜ Forall (λ x, ∃ obj, state !! key_of x = Some obj ∧
	    (KObjectV.objectmeta obj).(ObjectMetaV.UID') = (meta_of x).(ObjectMetaV.UID') ∧
	    ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta obj) (meta_of x)) xs ⌝ ∗
    ⌜ Forall (λ x, (meta_of x).(ObjectMetaV.UID') ∈ used_uid) xs ⌝.
Proof.
  iIntros "Hauth Hxs".
  iInduction xs as [|x xs] "IH".
  - rewrite !big_sepL_nil.
    iFrame.
    iPureIntro.
    split; constructor.
  - rewrite !big_sepL_cons.
    iDestruct "Hxs" as "[Hmeta Hxs]".
    iPoseProof (own_meta_exists with "Hauth Hmeta") as "%Hhead".
    iDestruct ("IH" with "Hauth Hxs") as "(%Hmeta_forall & %Huid_forall)".
    iFrame.
    iPureIntro.
	    destruct Hhead as (obj & Hlookup & Huid_obj & Hmeta_eq & Huid_in).
    split.
    + constructor.
	      * exists obj. split_and!; done.
      * exact Hmeta_forall.
    + constructor.
      * exact Huid_in.
      * exact Huid_forall.
Qed.

Lemma own_meta_list_exists_dqs {γ state used_uid A}
    (key_of : A → KKey.t) (meta_of : A → ObjectMetaV.t)
    xs dqs :
  own_auth γ state used_uid -∗
  ([∗ list] x;dq ∈ xs;dqs,
    own_meta_frag γ (key_of x) (meta_of x).(ObjectMetaV.UID')
      dq (meta_of x)) -∗
    ⌜ Forall (λ x, ∃ obj, state !! key_of x = Some obj ∧
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
        (meta_of x).(ObjectMetaV.UID') ∧
      ObjectMetaV.equiv_except_resource_version
        (KObjectV.objectmeta obj) (meta_of x)) xs ⌝ ∗
    ⌜ Forall (λ x,
      (meta_of x).(ObjectMetaV.UID') ∈ used_uid) xs ⌝.
Proof.
  iIntros "Hauth Hxs".
  iInduction xs as [|x xs] "IH" forall (dqs).
  - iDestruct (big_sepL2_length with "Hxs") as %Hlen.
    destruct dqs; simpl in Hlen; last congruence.
    rewrite big_sepL2_nil.
    iFrame.
    iPureIntro.
    split; constructor.
  - iDestruct (big_sepL2_length with "Hxs") as %Hlen.
    destruct dqs as [|dq dqs]; simpl in Hlen; first congruence.
    rewrite big_sepL2_cons.
    iDestruct "Hxs" as "[Hmeta Hxs]".
    iPoseProof (own_meta_exists with "Hauth Hmeta") as "%Hhead".
    iDestruct ("IH" with "Hauth Hxs") as
      "(%Hmeta_forall & %Huid_forall)".
    iFrame.
    iPureIntro.
    destruct Hhead as
      (obj & Hlookup & Huid_obj & Hmeta_eq & Huid_in).
    split.
    + constructor.
      * exists obj. split_and!; done.
      * exact Hmeta_forall.
    + constructor.
      * exact Huid_in.
      * exact Huid_forall.
Qed.

Lemma own_spec_exists {γ state used_uid k uid dq spec}:
  own_auth γ state used_uid -∗
  own_spec_frag γ k uid dq spec -∗
    ⌜ ∀ obj, state !! k = Some obj →
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
    (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
    (KObjectV.spec obj) = spec ⌝.
Proof.
  iIntros "Hauth Hspec".
  iDestruct (own_valid_2 with "Hauth Hspec") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  rewrite /kview_auth /kview_frag in Hvalid0.
  pose proof (proj1 (view_both_validN view_rel 0%nat
    (state, used_uid) (mk_spec_frag k uid dq spec)) Hvalid0) as Hrel0.
  assert (Hvalid : ✓ (●K (state, used_uid) ⋅ ◯K (mk_spec_frag k uid dq spec))).
  { rewrite /kview_auth /kview_frag.
    apply (proj2 (view_both_valid view_rel (state, used_uid) (mk_spec_frag k uid dq spec))).
    intros n. exact Hrel0.
  }
  intros obj Hlookup_obj Huid_obj Hliving.
  eapply (auth_spec_valid (state, used_uid) k uid dq spec Hvalid obj); simpl; eauto.
Qed.

Lemma own_meta_spec_list_exists {γ state used_uid A}
    (key_of : A → KKey.t) (meta_of : A → ObjectMetaV.t)
    (spec_of : A → ObjectSpecV.t) xs dq :
  own_auth γ state used_uid -∗
  ([∗ list] x ∈ xs,
    own_meta_frag γ (key_of x) (meta_of x).(ObjectMetaV.UID') dq
      (meta_of x) ∗
    own_spec_frag γ (key_of x) (meta_of x).(ObjectMetaV.UID') dq
      (spec_of x)) -∗
  ⌜ Forall (λ x, ∃ obj,
      state !! key_of x = Some obj ∧
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
        (meta_of x).(ObjectMetaV.UID') ∧
      ObjectMetaV.equiv_except_resource_version
        (KObjectV.objectmeta obj) (meta_of x) ∧
      KObjectV.spec obj = spec_of x) xs ⌝.
Proof.
  iIntros "Hauth Hxs".
  iInduction xs as [|x xs] "IH".
  - rewrite big_sepL_nil.
    iPureIntro. constructor.
  - rewrite big_sepL_cons.
    iDestruct "Hxs" as "[[Hmeta Hspec] Hxs]".
    iPoseProof (own_meta_exists with "Hauth Hmeta") as "%Hmeta".
    destruct Hmeta as (obj & Hlookup & Huid & Hmeta_eq & Huid_in).
    iPoseProof (own_meta_living Hlookup with "Hauth Hmeta") as "%Hliving".
    iPoseProof (own_spec_exists with "Hauth Hspec") as "%Hspec".
    iDestruct ("IH" with "Hauth Hxs") as "%Htail".
    iPureIntro. constructor; last exact Htail.
    exists obj. split_and!; try done.
    by eapply Hspec.
Qed.

Lemma own_meta_spec_list_exists_dqs {γ state used_uid A}
    (key_of : A → KKey.t) (meta_of : A → ObjectMetaV.t)
    (spec_of : A → ObjectSpecV.t) xs dqs :
  own_auth γ state used_uid -∗
  ([∗ list] x;dq ∈ xs;dqs,
    own_meta_frag γ (key_of x) (meta_of x).(ObjectMetaV.UID') dq
      (meta_of x) ∗
    own_spec_frag γ (key_of x) (meta_of x).(ObjectMetaV.UID') dq
      (spec_of x)) -∗
  ⌜ Forall (λ x, ∃ obj,
      state !! key_of x = Some obj ∧
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
        (meta_of x).(ObjectMetaV.UID') ∧
      ObjectMetaV.equiv_except_resource_version
        (KObjectV.objectmeta obj) (meta_of x) ∧
      KObjectV.spec obj = spec_of x) xs ⌝.
Proof.
  iIntros "Hauth Hxs".
  iInduction xs as [|x xs] "IH" forall (dqs).
  - iDestruct (big_sepL2_length with "Hxs") as %Hlen.
    destruct dqs; simpl in Hlen; last congruence.
    iPureIntro. constructor.
  - iDestruct (big_sepL2_length with "Hxs") as %Hlen.
    destruct dqs as [|dq dqs]; simpl in Hlen; first congruence.
    rewrite big_sepL2_cons.
    iDestruct "Hxs" as "[[Hmeta Hspec] Hxs]".
    iPoseProof (own_meta_exists with "Hauth Hmeta") as "%Hmeta".
    destruct Hmeta as (obj & Hlookup & Huid & Hmeta_eq & Huid_in).
    iPoseProof (own_meta_living Hlookup with "Hauth Hmeta") as "%Hliving".
    iPoseProof (own_spec_exists with "Hauth Hspec") as "%Hspec".
    iDestruct ("IH" with "Hauth Hxs") as "%Htail".
    iPureIntro. constructor; last exact Htail.
    exists obj. split_and!; try done.
    by eapply Hspec.
Qed.

Lemma own_meta_spec_list_exists_dqs_sep {γ state used_uid A}
    (key_of : A → KKey.t) (meta_of : A → ObjectMetaV.t)
    (spec_of : A → ObjectSpecV.t) xs dqs :
  own_auth γ state used_uid -∗
  ([∗ list] x;dq ∈ xs;dqs,
    own_meta_frag γ (key_of x) (meta_of x).(ObjectMetaV.UID') dq
      (meta_of x)) -∗
  ([∗ list] x;dq ∈ xs;dqs,
    own_spec_frag γ (key_of x) (meta_of x).(ObjectMetaV.UID') dq
      (spec_of x)) -∗
  ⌜ Forall (λ x, ∃ obj,
      state !! key_of x = Some obj ∧
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
        (meta_of x).(ObjectMetaV.UID') ∧
      ObjectMetaV.equiv_except_resource_version
        (KObjectV.objectmeta obj) (meta_of x) ∧
      KObjectV.spec obj = spec_of x) xs ⌝.
Proof.
  iIntros "Hauth Hmeta Hspec".
  iApply (own_meta_spec_list_exists_dqs with "Hauth").
  rewrite big_sepL2_sep. iFrame.
Qed.

Lemma own_status_exists {γ state used_uid k uid dq status}:
  own_auth γ state used_uid -∗
  own_status_frag γ k uid dq status -∗
    ⌜ ∀ obj, state !! k = Some obj →
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
    (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
    (KObjectV.status obj) = status ⌝.
Proof.
  iIntros "Hauth Hstatus_frag".
  iDestruct (own_valid_2 with "Hauth Hstatus_frag") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  rewrite /kview_auth /kview_frag in Hvalid0.
  pose proof (proj1 (view_both_validN view_rel 0%nat
    (state, used_uid) (mk_status_frag k uid dq status)) Hvalid0) as Hrel0.
  assert (Hvalid : ✓ (●K (state, used_uid) ⋅ ◯K (mk_status_frag k uid dq status))).
  { rewrite /kview_auth /kview_frag.
    apply (proj2 (view_both_valid view_rel (state, used_uid) (mk_status_frag k uid dq status))).
    intros n. exact Hrel0.
  }
  intros obj Hlookup_obj Huid_obj Hliving.
  pose proof (auth_frag_valid 0%nat (state, used_uid) (mk_status_frag k uid dq status) Hvalid 0%nat)
    as Hrel.
  destruct Hrel as [_ [_ [_ [Hstatus _]]]].
  assert (Hlookup :
    proj_status (mk_status_frag k uid dq status) !! (k, uid) =
    Some (dq, to_agree (A := leibnizO ObjectStatusV.t) status)).
  { rewrite /proj_status /mk_status_frag /= lookup_singleton_eq //. }
  destruct (Hstatus _ _ Hlookup) as (status0 & Hagree & _ & _ & Hstatus_obj).
  assert (Hstatus_eqv : (status : leibnizO ObjectStatusV.t) ≡ status0).
  { apply (inj (to_agree : leibnizO ObjectStatusV.t → agree (leibnizO ObjectStatusV.t))).
    exact Hagree.
  }
  apply leibniz_equiv in Hstatus_eqv.
  subst status0.
  eapply Hstatus_obj; eauto.
Qed.

Lemma extend_used_uid_vs {γ state used_uid} uid :
  own_auth γ state used_uid ==∗
    own_auth γ state (used_uid ∪ {[uid]}).
Proof.
  iIntros "Hauth".
  iMod (own_update with "Hauth") as "Hauth".
  { apply extend_used_uid. }
  iModIntro. iExact "Hauth".
Qed.

Lemma create_kobj_vs {γ state used_uid} k uid obj:
  state !! k = None →
  ¬ reserved_key_pred k →
  uid ∉ used_uid →
  valid_k_uid_obj k uid obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
  no_speculative_parent_reference (KObjectV.objectmeta obj) used_uid →
  own_auth γ state used_uid ==∗
    own_auth γ ((<[k := obj]> state)) (used_uid ∪ {[uid]}) ∗
    own_meta_frag γ k uid 1 (KObjectV.objectmeta obj) ∗
    own_spec_frag γ k uid 1 (KObjectV.spec obj) ∗
    own_status_frag γ k uid 1 (KObjectV.status obj) ∗
    own_unreserved_frag γ k.
Proof.
  iIntros (Hak Hnot_reserved Hfresh Hkuid_obj Hdeletion_timestamp Hno_spec) "Hauth".
  iMod (own_update with "Hauth") as "H".
  { eapply create_kobj; done. }
  iDestruct (own_op with "H") as "[H Hstatus]".
  iDestruct (own_op with "H") as "[H Hspec]".
  iDestruct (own_op with "H") as "[Hauth Hmeta]".
  iMod (own_update with "Hauth") as "H".
  { apply alloc_unreserved. exact Hnot_reserved. }
  iModIntro.
  iDestruct (own_op with "H") as "[Hauth Hunreserved]".
  iFrame.
Qed.

Lemma create_reserved_kobj_vs {γ state used_uid} k uid obj:
  state !! k = None →
  uid ∉ used_uid →
  valid_k_uid_obj k uid obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
  no_speculative_parent_reference (KObjectV.objectmeta obj) used_uid →
  own_auth γ state used_uid -∗
  own_reservation_frag γ k Available ==∗
    own_auth γ (<[k := obj]> state) (used_uid ∪ {[uid]}) ∗
    own_meta_frag γ k uid 1 (KObjectV.objectmeta obj) ∗
    own_spec_frag γ k uid 1 (KObjectV.spec obj) ∗
    own_status_frag γ k uid 1 (KObjectV.status obj) ∗
    own_reservation_frag γ k (Occupied uid).
Proof.
  iIntros (Hak Hfresh Hkuid_obj Hdeletion_timestamp Hno_spec) "Hauth Hreservation".
  iMod (own_update_2 with "Hauth Hreservation") as "H".
  { eapply create_reserved_kobj; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[H Hreservation]".
  iDestruct (own_op with "H") as "[H Hstatus]".
  iDestruct (own_op with "H") as "[H Hspec]".
  iDestruct (own_op with "H") as "[Hauth Hmeta]".
  iFrame.
Qed.

Lemma delete_kobj_vs {γ state used_uid k uid meta}:
  own_auth γ state used_uid -∗
  own_meta_frag γ k uid 1 meta -∗
  own_unreserved_frag γ k ==∗
    own_auth γ (delete k state) used_uid ∗
    own_unreserved_frag γ k.
Proof.
  iIntros "Hauth Hmeta #Hunreserved".
  iDestruct (own_unreserved_frag_valid with "Hunreserved") as %Hnot_reserved.
  iMod (own_update_2 with "Hauth Hmeta") as "Hauth".
  { eapply delete_kobj_raw; done. }
  iModIntro. iFrame "Hauth Hunreserved".
Qed.

Lemma delete_reserved_kobj_vs {γ state used_uid k uid meta}:
  own_auth γ state used_uid -∗
  own_meta_frag γ k uid 1 meta -∗
    own_reservation_frag γ k (Occupied uid) ==∗
    own_auth γ (delete k state) used_uid ∗
    own_reservation_frag γ k (Deleting uid).
Proof.
  iIntros "Hauth Hmeta Hreservation".
  iMod (own_update_3 with "Hauth Hmeta Hreservation") as "H".
  { eapply delete_reserved_kobj; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[Hauth Hreservation]".
  iFrame.
Qed.

Lemma recover_available_vs {γ state used_uid k uid} :
  state !! k = None →
  own_auth γ state used_uid -∗
  own_reservation_frag γ k (Deleting uid) ==∗
    own_auth γ state used_uid ∗
    own_reservation_frag γ k Available.
Proof.
  iIntros (Habsent) "Hauth Hreservation".
  iMod (own_update_2 with "Hauth Hreservation") as "H".
  { eapply recover_available. exact Habsent. }
  iModIntro.
  iDestruct (own_op with "H") as "[Hauth Hreservation]".
  iFrame.
Qed.

Lemma create_reserved_from_deleting_kobj_vs
    {γ state used_uid k old_uid new_uid obj} :
  state !! k = None →
  new_uid ∉ used_uid →
  valid_k_uid_obj k new_uid obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
  no_speculative_parent_reference (KObjectV.objectmeta obj) used_uid →
  own_auth γ state used_uid -∗
  own_reservation_frag γ k (Deleting old_uid) ==∗
    own_auth γ (<[k := obj]> state) (used_uid ∪ {[new_uid]}) ∗
    own_meta_frag γ k new_uid 1 (KObjectV.objectmeta obj) ∗
    own_spec_frag γ k new_uid 1 (KObjectV.spec obj) ∗
    own_status_frag γ k new_uid 1 (KObjectV.status obj) ∗
    own_reservation_frag γ k (Occupied new_uid).
Proof.
  iIntros (Habsent Hfresh Hvalid Hliving Hno_spec) "Hauth Hdeleting".
  iMod (recover_available_vs Habsent with "Hauth Hdeleting") as
    "(Hauth & Havailable)".
  iMod (create_reserved_kobj_vs k new_uid obj Habsent Hfresh Hvalid
    Hliving Hno_spec with "Hauth Havailable") as "H".
  iModIntro. iExact "H".
Qed.

Lemma delete_terminating_kobj_vs {γ state used_uid k obj} :
  state !! k = Some obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
  own_auth γ state used_uid ==∗
    own_auth γ (delete k state) used_uid.
Proof.
  iIntros (Hlookup Hterminating) "Hauth".
  iMod (own_update with "Hauth") as "Hauth".
  { eapply delete_terminating_kobj; done. }
  iModIntro. iExact "Hauth".
Qed.

Lemma update_terminating_kobj_vs
    {γ state used_uid k uid old_obj new_obj} :
  valid_k_uid_obj k uid new_obj →
  (KObjectV.objectmeta new_obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
  no_speculative_parent_reference (KObjectV.objectmeta new_obj) used_uid →
  state !! k = Some old_obj →
  (KObjectV.objectmeta old_obj).(ObjectMetaV.UID') = uid →
  (KObjectV.objectmeta old_obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
  own_auth γ state used_uid ==∗
    own_auth γ (<[k := new_obj]> state) used_uid.
Proof.
  iIntros (Hvalid Hnew_terminating Hno_spec Hlookup Hold_uid
    Hold_terminating) "Hauth".
  iMod (own_update with "Hauth") as "Hauth".
  { eapply update_terminating_kobj; done. }
  iModIntro. iExact "Hauth".
Qed.

Lemma mark_terminating_kobj_vs
    {γ state used_uid k uid meta old_obj new_obj} :
  valid_k_uid_obj k uid new_obj →
  (KObjectV.objectmeta new_obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
  no_speculative_parent_reference (KObjectV.objectmeta new_obj) used_uid →
  state !! k = Some old_obj →
  own_auth γ state used_uid -∗
  own_meta_frag γ k uid 1 meta -∗
  own_unreserved_frag γ k ==∗
    own_auth γ (<[k := new_obj]> state) used_uid ∗
    own_unreserved_frag γ k.
Proof.
  iIntros (Hvalid Hterminating Hno_spec Hlookup)
    "Hauth Hmeta #Hunreserved".
  iDestruct (own_unreserved_frag_valid with "Hunreserved") as %Hnot_reserved.
  iMod (own_update_2 with "Hauth Hmeta") as "Hauth".
  { eapply mark_terminating_kobj_raw; done. }
  iModIntro. iFrame "Hauth Hunreserved".
Qed.

Lemma mark_terminating_reserved_kobj_vs
    {γ state used_uid k uid meta old_obj new_obj} :
  valid_k_uid_obj k uid new_obj →
  (KObjectV.objectmeta new_obj).(ObjectMetaV.DeletionTimestamp') ≠ None →
  no_speculative_parent_reference (KObjectV.objectmeta new_obj) used_uid →
  state !! k = Some old_obj →
  own_auth γ state used_uid -∗
  own_meta_frag γ k uid 1 meta -∗
  own_reservation_frag γ k (Occupied uid) ==∗
    own_auth γ (<[k := new_obj]> state) used_uid ∗
    own_reservation_frag γ k (Deleting uid).
Proof.
  iIntros (Hvalid Hterminating Hno_spec Hlookup)
    "Hauth Hmeta Hreservation".
  iMod (own_update_3 with "Hauth Hmeta Hreservation") as "H".
  { eapply mark_terminating_reserved_kobj; done. }
  iModIntro. iDestruct (own_op with "H") as "[$ $]".
Qed.

Lemma update_meta_kobj_vs {γ state used_uid k uid meta} prev_obj obj:
  valid_k_uid_obj k uid obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
  no_speculative_parent_reference (KObjectV.objectmeta obj) used_uid →
  state !! k = Some prev_obj →
  (KObjectV.spec prev_obj) = (KObjectV.spec obj) →
  (KObjectV.status prev_obj) = (KObjectV.status obj) →
  own_auth γ state used_uid -∗
  own_meta_frag γ k uid 1 meta ==∗
    own_auth γ (<[k := obj]> state) used_uid ∗
    own_meta_frag γ k uid 1 (KObjectV.objectmeta obj).
Proof.
  iIntros (Hkuid_obj Hdeletion_timestamp Hno_spec Hak Hspec_eq Hstatus_eq)
    "Hauth Hmeta".
  iMod (own_update_2 with "Hauth Hmeta") as "H".
  { eapply update_meta_kobj; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[Hauth Hmeta]".
  iFrame.
Qed.

Lemma update_kobj_vs {γ state used_uid k uid meta spec} prev_obj obj:
  valid_k_uid_obj k uid obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
  no_speculative_parent_reference (KObjectV.objectmeta obj) used_uid →
  state !! k = Some prev_obj →
  (KObjectV.status prev_obj) = (KObjectV.status obj) →
  own_auth γ state used_uid -∗
  own_meta_frag γ k uid 1 meta -∗
  own_spec_frag γ k uid 1 spec ==∗
    own_auth γ (<[k := obj]> state) used_uid ∗
    own_meta_frag γ k uid 1 (KObjectV.objectmeta obj) ∗
    own_spec_frag γ k uid 1 (KObjectV.spec obj).
Proof.
  iIntros (Hkuid_obj Hdeletion_timestamp Hno_spec Hak Hstatus_eq)
    "Hauth Hmeta Hspec".
  iMod (own_update_3 with "Hauth Hmeta Hspec") as "H".
  { eapply update_kobj; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[H Hspec]".
  iDestruct (own_op with "H") as "[Hauth Hmeta]".
  iFrame.
Qed.

Lemma update_status_kobj_vs {γ state used_uid k uid meta status} prev_obj obj:
  valid_k_uid_obj k uid obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp') = None →
  no_speculative_parent_reference (KObjectV.objectmeta obj) used_uid →
  state !! k = Some prev_obj →
  (KObjectV.spec prev_obj) = (KObjectV.spec obj) →
  own_auth γ state used_uid -∗
  own_meta_frag γ k uid 1 meta -∗
  own_status_frag γ k uid 1 status ==∗
    own_auth γ (<[k := obj]> state) used_uid ∗
    own_meta_frag γ k uid 1 (KObjectV.objectmeta obj) ∗
    own_status_frag γ k uid 1 (KObjectV.status obj).
Proof.
  iIntros (Hkuid_obj Hdeletion_timestamp Hno_spec Hak Hspec_eq)
    "Hauth Hmeta Hstatus".
  iMod (own_update_3 with "Hauth Hmeta Hstatus") as "H".
  { eapply update_status_kobj; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[H Hstatus]".
  iDestruct (own_op with "H") as "[Hauth Hmeta]".
  iFrame.
Qed.

End kview.
