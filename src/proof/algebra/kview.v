From New.proof Require Import prelude.
From New.proof Require Export pure_objects.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From iris.algebra Require Import cmra gset gmap.


Section kview.

Definition authO : ofe := prodO (gmapO KKey.t (leibnizO KObjectV.t)) (gsetO (leibnizO types.UID.t)).

Definition metaUR : ucmra := gmapUR (KKey.t * types.UID.t) (prodR dfracR (agreeR (leibnizO ObjectMetaV.t))).
Definition specUR : ucmra := gmapUR (KKey.t * types.UID.t) (prodR dfracR (agreeR (leibnizO ObjectSpecV.t))).
Definition statusUR : ucmra := gmapUR (KKey.t * types.UID.t) (prodR dfracR (agreeR (leibnizO ObjectStatusV.t))).
Definition fragUR : ucmra := prodUR metaUR (prodUR specUR statusUR).

Implicit Types (a : authO) (b : fragUR).

Local Definition proj_state a : gmap KKey.t KObjectV.t := fst a.
Local Definition proj_used_uids a : gset types.UID.t := snd a.

Local Definition proj_meta b : metaUR := fst b.
Local Definition proj_spec b : specUR := fst (snd b).
Local Definition proj_status b : statusUR := snd (snd b).

Definition meta_is_child_of meta key uid: Prop :=
  meta.(ObjectMetaV.Namespace') = key.(KKey.Namespace') ∧
  match meta.(ObjectMetaV.OwnerReferences') with
  | Some os => os_has_controller_parent_of os key.(KKey.Kind') key.(KKey.Name') uid
  | None => False
  end.

Definition no_speculative_parent_reference meta (used_uids: gset types.UID.t): Prop :=
  ∀ parent_key uid, meta_is_child_of meta parent_key uid → uid ∈ used_uids.

Local Definition valid_kauth a : Prop :=
  map_Forall (λ k obj,
    k = KObjectV.key obj ∧
    KObjectV.well_formed obj ∧
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∈ proj_used_uids a ∧
    (* No object's parent reference can speculatively point to uid that has never existed *)
    no_speculative_parent_reference (KObjectV.objectmeta obj) (proj_used_uids a) ∧
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
        KObjectV.objectmeta obj = meta
  ) (proj_meta b) ∧
  map_Forall (λ '(k, uid) '(dq, agree_spec),
    ∃ spec, agree_spec ≡ to_agree (A := leibnizO ObjectSpecV.t) spec ∧
      uid ∈ proj_used_uids a ∧
      ✓ dq ∧
      ∀ obj, proj_state a !! k = Some obj →
        (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
        KObjectV.spec obj = spec
  ) (proj_spec b) ∧
  map_Forall (λ '(k, uid) '(dq, agree_status),
    ∃ status, agree_status ≡ to_agree (A := leibnizO ObjectStatusV.t) status ∧
      uid ∈ proj_used_uids a ∧
      ✓ dq ∧
      ∀ obj, proj_state a !! k = Some obj →
        (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
        KObjectV.status obj = status
  ) (proj_status b).

Local Definition view_rel_raw (n: nat) a b :=
  valid_kauth a ∧ compatible_kfrag b a.

Local Lemma view_rel_raw_mono n1 n2 a1 a2 b1 b2 :
  view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  (n2 ≤ n1)%nat →
  view_rel_raw n2 a2 b2.
Proof.
  intros [Hvalid [Hmeta [Hspec Hstatus]]] Ha Hb _.
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
  apply pair_includedN in Hrest as [Hspec_incl Hstatus_incl].
  split.
  { rewrite /valid_kauth.
    rewrite map_Forall_lookup.
    intros k obj Hlookup.
    pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup) as Hobj_valid.
    destruct Hobj_valid as (Hkey & Hwf & Huid_in & Hno_spec & Huniq).
    split_and!; [done|done| | |done].
    - apply (proj1 (Hused_elem _)). done.
    - intros parent_key uid Hchild.
      apply (proj1 (Hused_elem _)).
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
    + rewrite map_Forall_lookup.
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
      * apply (proj2 (discrete_iff n2 agree2
          (to_agree (A := leibnizO ObjectStatusV.t) status))).
        etrans; [exact Hagree2_n2|exact (Hagree1 n2)].
      * split.
        { apply (proj1 (Hused_elem _)). exact Huid_in. }
        { split; [exact Hvdq2|exact Hstatus_obj]. }
Qed.

Local Lemma view_rel_raw_valid n a b :
  view_rel_raw n a b → ✓{n} b.
Proof.
  intros [_ [Hmeta [Hspec Hstatus]]].
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
    + intros [k uid].
      destruct (proj_status b !! (k, uid)) as [[dq agree_status]|] eqn:Hlookup.
      * pose proof (map_Forall_lookup_1 _ _ _ _ Hstatus Hlookup) as Hstatus_i.
        simpl in Hstatus_i.
        destruct Hstatus_i as (status & Hagree & _ & Hvdq & _).
        rewrite Hlookup.
        apply pair_validN. split.
        { apply cmra_valid_validN. done. }
        { rewrite Hagree. done. }
      * rewrite Hlookup. done.
Qed.

Local Lemma view_rel_raw_unit n :
  ∃ a, view_rel_raw n a ε.
Proof.
  exists ((∅ : gmap KKey.t KObjectV.t), (∅ : gset types.UID.t)).
  split.
  1: rewrite /valid_kauth /=.
  2: split_and!.
  all: rewrite map_Forall_lookup; intros i x Hlookup;
    rewrite lookup_empty in Hlookup; done.
Qed.

Local Canonical Structure view_rel : view_rel authO fragUR :=
  ViewRel view_rel_raw view_rel_raw_mono
          view_rel_raw_valid view_rel_raw_unit.

Definition kview_auth dq a : viewR view_rel := ●V{dq} a.
Definition kview_frag b : viewR view_rel := ◯V b.
Notation "●K a" := (kview_auth 1 a) (at level 20).
Notation "◯K b" := (kview_frag b) (at level 20).

Definition mk_meta_frag (k: KKey.t) (uid: types.UID.t) (dq: dfrac) (m: ObjectMetaV.t) : fragUR :=
  ({[(k, uid) := (dq, to_agree m)]}, (∅, ∅)).
Definition mk_spec_frag (k: KKey.t) (uid: types.UID.t) (dq: dfrac) (s: ObjectSpecV.t) : fragUR :=
  (∅, ({[(k, uid) := (dq, to_agree s)]}, ∅)).
Definition mk_status_frag (k: KKey.t) (uid: types.UID.t) (dq: dfrac) (s: ObjectStatusV.t) : fragUR :=
  (∅, (∅, {[(k, uid) := (dq, to_agree s)]})).

Lemma auth_valid a k obj:
✓ (●K a) →
(proj_state a) !! k = Some obj →
k = KObjectV.key obj ∧
KObjectV.well_formed obj.
Proof.
  intros Hvalid Hlookup.
  rewrite /kview_auth in Hvalid.
  pose proof (proj1 (view_auth_dfrac_valid view_rel 1 a) Hvalid) as [_ Hrel].
  specialize (Hrel 0%nat).
  change (view_rel_raw 0%nat a ε) in Hrel.
  destruct Hrel as [Hvalid_a _].
  rewrite /valid_kauth in Hvalid_a.
  pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid_a Hlookup) as Hobj_valid.
  destruct Hobj_valid as (Hkey_obj & Hwf_obj & _ & _ & _).
  split; [done|done].
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
ObjectMetaV.well_formed meta.
Proof.
  intros Hvalid.
  rewrite /kview_frag in Hvalid.
  pose proof (proj1 (view_frag_valid view_rel (mk_meta_frag k uid dq meta)) Hvalid 0%nat)
    as [a Hrel].
  destruct Hrel as [Hvalid_a [Hmeta _]].
  assert (Hlookup :
    proj_meta (mk_meta_frag k uid dq meta) !! (k, uid) =
    Some (dq, to_agree (A := leibnizO ObjectMetaV.t) meta)).
  { rewrite /proj_meta /mk_meta_frag /= lookup_singleton_eq //. }
  destruct (Hmeta _ _ Hlookup) as (meta0 & Hagree & _ & Hobj).
  destruct Hobj as (obj & Hlookup_obj & Huid_obj & Hobj_meta).
  pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid_a Hlookup_obj) as Hobj_valid.
  destruct Hobj_valid as (Hkey_obj & Hwf_obj & _ & _ & _).
  assert (Hmeta_eqv : (meta : leibnizO ObjectMetaV.t) ≡ meta0).
  { apply (inj (to_agree : leibnizO ObjectMetaV.t → agree (leibnizO ObjectMetaV.t))).
    exact Hagree.
  }
  apply leibniz_equiv in Hmeta_eqv.
  assert (Hobj_meta_eq : KObjectV.objectmeta obj = meta).
  { rewrite <- Hmeta_eqv in Hobj_meta. exact Hobj_meta. }
  split.
  - subst k. rewrite /KObjectV.key /= Hobj_meta_eq //.
  - split.
    + subst k. rewrite /KObjectV.key /= Hobj_meta_eq //.
    + split.
      * rewrite Hobj_meta_eq in Huid_obj. symmetry. exact Huid_obj.
      * apply well_formed_object_has_well_formed_objectmeta in Hwf_obj.
        by rewrite Hobj_meta_eq in Hwf_obj.
Qed.

Lemma auth_meta_valid a k uid dq meta:
✓ (●K a ⋅ ◯K (mk_meta_frag k uid dq meta)) →
∃ obj, (proj_state a) !! k = Some obj ∧
  (KObjectV.objectmeta obj) = meta ∧
  meta.(ObjectMetaV.UID') ∈ proj_used_uids a.
Proof.
  intros Hvalid.
  pose proof (auth_frag_valid 0%nat a (mk_meta_frag k uid dq meta) Hvalid 0%nat)
    as Hrel.
  destruct Hrel as [Hvalid_a [Hmeta _]].
  assert (Hlookup :
    proj_meta (mk_meta_frag k uid dq meta) !! (k, uid) =
    Some (dq, to_agree (A := leibnizO ObjectMetaV.t) meta)).
  { rewrite /proj_meta /mk_meta_frag /= lookup_singleton_eq //. }
  destruct (Hmeta _ _ Hlookup) as (meta0 & Hagree & _ & Hobj).
  destruct Hobj as (obj & Hlookup_obj & _ & Hobj_meta).
  pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid_a Hlookup_obj) as Hobj_valid.
  destruct Hobj_valid as (_ & _ & Huid_in & _ & _).
  assert (Hmeta_eqv : (meta : leibnizO ObjectMetaV.t) ≡ meta0).
  { apply (inj (to_agree : leibnizO ObjectMetaV.t → agree (leibnizO ObjectMetaV.t))).
    exact Hagree.
  }
  apply leibniz_equiv in Hmeta_eqv.
  assert (Hobj_meta_eq : KObjectV.objectmeta obj = meta).
  { rewrite <- Hmeta_eqv in Hobj_meta. exact Hobj_meta. }
  exists obj. split_and!.
  - exact Hlookup_obj.
  - exact Hobj_meta_eq.
  - by rewrite <- Hobj_meta_eq.
Qed.

Lemma meta_meta_valid k uid dq1 meta1 dq2 meta2:
✓ (◯K (mk_meta_frag k uid dq1 meta1) ⋅
   ◯K (mk_meta_frag k uid dq2 meta2)) →
✓ (dq1 ⋅ dq2) ∧ meta1 = meta2.
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
    Some ((dq1, to_agree (A := leibnizO ObjectMetaV.t) meta1) ⋅
          (dq2, to_agree (A := leibnizO ObjectMetaV.t) meta2))).
  { rewrite /proj_meta /mk_meta_frag /= lookup_op.
    rewrite lookup_singleton_eq lookup_singleton_eq Some_op_opM //. }
  destruct (Hmeta _ _ Hlookup) as (meta & Hagree & Hvdq & _).
  split.
  - exact Hvdq.
  - change ((meta1 : leibnizO ObjectMetaV.t) = (meta2 : leibnizO ObjectMetaV.t)).
    apply to_agree_op_inv_L.
    rewrite Hagree. done.
Qed.

Lemma auth_spec_valid a k uid dq spec:
✓ (●K a ⋅ ◯K (mk_spec_frag k uid dq spec)) →
∀ obj, (proj_state a) !! k = Some obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
  (KObjectV.spec obj) = spec.
Proof.
  intros Hvalid obj Hlookup_obj Huid_obj.
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

Definition valid_k_uid_obj k uid obj: Prop :=
  k = KObjectV.key obj ∧
  uid = (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∧
  KObjectV.well_formed obj.

Lemma create_kobj a k uid obj:
(proj_state a) !! k = None →
uid ∉ (proj_used_uids a) →
valid_k_uid_obj k uid obj →
no_speculative_parent_reference (KObjectV.objectmeta obj) (proj_used_uids a) →
●K a ~~>
  (●K ((<[k := obj]> (proj_state a)), ((proj_used_uids a) ∪ {[uid]})) ⋅
      ◯K (mk_meta_frag k uid 1 (KObjectV.objectmeta obj)) ⋅
      ◯K (mk_spec_frag k uid 1 (KObjectV.spec obj)) ⋅
      ◯K (mk_status_frag k uid 1 (KObjectV.status obj))).
Proof.
  intros Hak Huid_fresh Hkuid_obj Hno_spec.
  destruct Hkuid_obj as (Hkey_obj & Huid_obj & Hwf_obj).
  rewrite -!assoc -!view_frag_op.
  apply view_update_alloc.
  intros n bf [Hvalid [Hmeta [Hspec Hstatus]]].
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
      * rewrite Huid_obj. set_solver.
      * intros parent_key uid0 Hchild.
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
      * set_solver.
      * intros parent_key uid0 Hchild.
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
             (KObjectV.objectmeta obj))]} : metaUR) ⋅ ∅)
          bf.1 (k, uid)) in Hlookup_new.
        rewrite (lookup_op
          ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
             (KObjectV.objectmeta obj))]} : metaUR)
          (∅ : metaUR) (k, uid)) in Hlookup_new.
        rewrite lookup_singleton_eq lookup_empty right_id Hmeta_bf_none right_id in Hlookup_new.
        inversion Hlookup_new. subst dq' agree_meta'.
        exists (KObjectV.objectmeta obj). split_and!. all: try done.
        exists obj. split_and!. all: try done.
        rewrite lookup_insert. destruct (decide (k = k)); done.
      * assert (Hlookup_old : proj_meta bf !! (k', uid') = Some (dq', agree_meta')).
        { rewrite /proj_meta /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
          rewrite (right_id (A := metaUR) (∅ : metaUR)) in Hlookup_new.
          assert (Hsingle_none :
            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
              (KObjectV.objectmeta obj))]}
              : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectMetaV.t))) !!
            (k', uid') = None).
          { apply lookup_singleton_ne. done. }
          rewrite (lookup_op
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
               (KObjectV.objectmeta obj))]} : metaUR) ⋅ ∅)
            bf.1 (k', uid')) in Hlookup_new.
          rewrite (lookup_op
            ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
               (KObjectV.objectmeta obj))]} : metaUR)
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
        destruct Hobj' as (obj0 & Hlookup_obj0 & Huid_obj0 & Hmeta_obj0).
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
    + intros [k' uid'] [dq' agree_status'] Hlookup_new.
      destruct (decide ((k', uid') = (k, uid))) as [Heq_pair|Hneq_pair].
      * inversion Heq_pair. subst k' uid'.
        rewrite /proj_status /mk_meta_frag /mk_spec_frag /mk_status_frag /kview_frag /= in Hlookup_new.
        rewrite (lookup_op
          ((∅ : statusUR) ⋅
            ((∅ : statusUR) ⋅
              ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectStatusV.t)
                 (KObjectV.status obj))]} : statusUR)))
          bf.2.2 (k, uid)) in Hlookup_new.
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
            bf.2.2 (k', uid')) in Hlookup_new.
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
Qed.

Lemma delete_kobj a k uid meta:
●K a ⋅ ◯K (mk_meta_frag k uid 1 meta) ~~>
  ●K (delete k (proj_state a), proj_used_uids a).
Proof.
  apply view_update_dealloc.
  intros n bf [Hvalid [Hmeta [Hspec Hstatus]]].
  assert (Hbf_none : proj_meta bf !! (k, uid) = None).
  { destruct (proj_meta bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    assert (Hlookup :
      (proj_meta (mk_meta_frag k uid 1 meta ⋅ bf)) !! (k, uid) =
      Some ((DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t) meta) ⋅ (dqf, agf))).
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
    Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t) meta)).
  { rewrite /proj_meta /mk_meta_frag /= lookup_op.
    rewrite lookup_singleton_eq Hbf_none right_id //. }
  destruct (Hmeta _ _ Hlookup_k) as (meta0 & Hagree0 & _ & Hobj0).
  destruct Hobj0 as (obj0 & Hobj0_lookup & Hobj0_uid & Hobj0_meta).
  assert (Hmeta_eqv : (meta : leibnizO ObjectMetaV.t) ≡ meta0).
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
          ({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t) meta)]})
          (proj_meta bf) (k', uid')).
        assert (Hsingle_none :
          (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t) meta)]}
            : gmap (KKey.t * types.UID.t) (dfrac * agree (leibnizO ObjectMetaV.t))) !!
            (k', uid')) = None).
        { apply lookup_singleton_ne. done. }
        rewrite Hsingle_none.
        rewrite Hlookup_bf left_id //. }
      destruct (Hmeta _ _ Hlookup_old) as (meta' & Hagree' & Hvdq' & Hobj').
      destruct Hobj' as (obj' & Hobj'_lookup & Hobj'_uid & Hobj'_meta).
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
Qed.

Lemma update_kobj a k uid meta spec prev_obj obj:
valid_k_uid_obj k uid obj →
no_speculative_parent_reference (KObjectV.objectmeta obj) (proj_used_uids a) →
(proj_state a) !! k = Some prev_obj →
(KObjectV.status prev_obj) = (KObjectV.status obj) →
(●K a ⋅
  ◯K (mk_meta_frag k uid 1 meta) ⋅
  ◯K (mk_spec_frag k uid 1 spec)) ~~>
  (●K ((<[k := obj]> (proj_state a)), proj_used_uids a) ⋅
    ◯K (mk_meta_frag k uid 1 (KObjectV.objectmeta obj)) ⋅
    ◯K (mk_spec_frag k uid 1 (KObjectV.spec obj))).
Proof.
  intros Hkuid_obj Hno_spec Hak Hstatus_eq.
  destruct Hkuid_obj as (Hkey_obj & Huid_obj & Hwf_obj).
  rewrite -!assoc -!view_frag_op.
  apply view_update.
  intros n bf [Hvalid [Hmeta [Hspec Hstatus]]].
  assert (Hmeta_bf_none : proj_meta bf !! (k, uid) = None).
  { destruct (proj_meta bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    assert (Hlookup :
      (proj_meta (mk_meta_frag k uid 1 meta ⋅ mk_spec_frag k uid 1 spec ⋅ bf)) !! (k, uid) =
      Some ((DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t) meta) ⋅ (dqf, agf))).
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
    Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t) meta)).
  { rewrite /proj_meta /mk_meta_frag /mk_spec_frag /=.
    rewrite ?lookup_op.
    rewrite lookup_singleton_eq lookup_empty right_id Hmeta_bf_none right_id //. }
  destruct (Hmeta _ _ Hlookup_meta_k_old) as (meta0 & Hagree0 & _ & Hobj0).
  destruct Hobj0 as (obj0 & Hobj0_lookup & Hobj0_uid & _).
  assert (Hmeta_eqv : (meta : leibnizO ObjectMetaV.t) ≡ meta0).
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
  assert (Huid_in_used : uid ∈ proj_used_uids a).
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
          Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t) (KObjectV.objectmeta obj))).
        { rewrite /proj_meta /mk_meta_frag /mk_spec_frag /=.
          rewrite ?lookup_op.
          rewrite lookup_singleton_eq lookup_empty right_id Hmeta_bf_none right_id //. }
        rewrite Hlookup_k in Hlookup_new. inversion Hlookup_new. subst dq' agree_meta'.
        exists (KObjectV.objectmeta obj). split_and!. all: try done.
        exists obj. split_and!. all: try done.
        rewrite lookup_insert. destruct (decide (k = k)); done.
      * assert (Hlookup_old :
          (proj_meta (mk_meta_frag k uid 1 meta ⋅ mk_spec_frag k uid 1 spec ⋅ bf)) !! (k', uid') =
          Some (dq', agree_meta')).
        { rewrite /proj_meta /mk_meta_frag /mk_spec_frag /= in Hlookup_new |- *.
          destruct (decide ((k, uid) = (k', uid'))) as [Heq|Hneq].
          { exfalso. apply Hneq_pair. done. }
          assert (Hdrop_new :
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
              (KObjectV.objectmeta obj))]}
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
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t) meta)]}
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
        destruct Hobj' as (obj' & Hlookup_obj' & Huid_obj' & Hmeta_obj').
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
      intros obj0 Hlookup_obj0 Huid_obj0.
      destruct (decide (k' = k)) as [->|Hneq_k'].
      * rewrite lookup_insert in Hlookup_obj0.
        destruct (decide (k = k)) as [_|Hneq_k]; [|done].
        inversion Hlookup_obj0. subst obj0.
        rewrite <- Hstatus_eq.
        eapply Hstatus'; eauto.
        rewrite Huid_prev_obj. done.
      * simpl in Hlookup_obj0.
        apply lookup_insert_Some in Hlookup_obj0.
        destruct Hlookup_obj0 as [[Hk_eq _]|[Hk_neq Hlookup_old_obj0]].
        { congruence. }
        eapply Hstatus'; done.
Qed.

Lemma update_status_kobj a k uid meta status prev_obj obj:
valid_k_uid_obj k uid obj →
no_speculative_parent_reference (KObjectV.objectmeta obj) (proj_used_uids a) →
(proj_state a) !! k = Some prev_obj →
(KObjectV.spec prev_obj) = (KObjectV.spec obj) →
  (●K a ⋅
  ◯K (mk_meta_frag k uid 1 meta) ⋅
  ◯K (mk_status_frag k uid 1 status)) ~~>
  (●K ((<[k := obj]> (proj_state a)), proj_used_uids a) ⋅
    ◯K (mk_meta_frag k uid 1 (KObjectV.objectmeta obj)) ⋅
    ◯K (mk_status_frag k uid 1 (KObjectV.status obj))).
Proof.
  intros Hkuid_obj Hno_spec Hak Hspec_eq.
  destruct Hkuid_obj as (Hkey_obj & Huid_obj & Hwf_obj).
  rewrite -!assoc -!view_frag_op.
  apply view_update.
  intros n bf [Hvalid [Hmeta [Hspec Hstatus]]].
  assert (Hmeta_bf_none : proj_meta bf !! (k, uid) = None).
  { destruct (proj_meta bf !! (k, uid)) as [[dqf agf]|] eqn:Hbf; [|done].
    exfalso.
    assert (Hlookup :
      (proj_meta (mk_meta_frag k uid 1 meta ⋅ mk_status_frag k uid 1 status ⋅ bf)) !! (k, uid) =
      Some ((DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t) meta) ⋅ (dqf, agf))).
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
    Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t) meta)).
  { rewrite /proj_meta /mk_meta_frag /mk_status_frag /=.
    rewrite ?lookup_op.
    rewrite lookup_singleton_eq lookup_empty right_id Hmeta_bf_none right_id //. }
  destruct (Hmeta _ _ Hlookup_meta_k_old) as (meta0 & Hagree0 & _ & Hobj0).
  destruct Hobj0 as (obj0 & Hobj0_lookup & Hobj0_uid & _).
  assert (Hmeta_eqv : (meta : leibnizO ObjectMetaV.t) ≡ meta0).
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
  assert (Huid_in_used : uid ∈ proj_used_uids a).
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
          Some (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t) (KObjectV.objectmeta obj))).
        { rewrite /proj_meta /mk_meta_frag /mk_status_frag /=.
          rewrite ?lookup_op.
          rewrite lookup_singleton_eq lookup_empty right_id Hmeta_bf_none right_id //. }
        rewrite Hlookup_k in Hlookup_new. inversion Hlookup_new. subst dq' agree_meta'.
        exists (KObjectV.objectmeta obj). split_and!. all: try done.
        exists obj. split_and!. all: try done.
        rewrite lookup_insert. destruct (decide (k = k)); done.
      * assert (Hlookup_old :
          (proj_meta (mk_meta_frag k uid 1 meta ⋅ mk_status_frag k uid 1 status ⋅ bf)) !! (k', uid') =
          Some (dq', agree_meta')).
        { rewrite /proj_meta /mk_meta_frag /mk_status_frag /= in Hlookup_new |- *.
          destruct (decide ((k, uid) = (k', uid'))) as [Heq|Hneq].
          { exfalso. apply Hneq_pair. done. }
          assert (Hdrop_new :
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t)
              (KObjectV.objectmeta obj))]}
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
            (({[(k, uid) := (DfracOwn 1, to_agree (A := leibnizO ObjectMetaV.t) meta)]}
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
        destruct Hobj' as (obj' & Hlookup_obj' & Huid_obj' & Hmeta_obj').
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
      intros obj0 Hlookup_obj0 Huid_obj0.
      destruct (decide (k' = k)) as [->|Hneq_k'].
      * rewrite lookup_insert in Hlookup_obj0.
        destruct (decide (k = k)) as [_|Hneq_k]; [|done].
        inversion Hlookup_obj0. subst obj0.
        rewrite <- Hspec_eq.
        eapply Hspec'; eauto.
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
        intros obj0 Hlookup_obj0 Huid_obj0.
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
        eapply Hstatus'; done.
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

Definition own_auth γ (state: gmap KKey.t KObjectV.t) (used_uids: gsetO types.UID.t) : iProp Σ :=
  own γ (●K (state, used_uids)).

Definition own_meta_frag γ k uid dq m : iProp Σ :=
  own γ (◯K (mk_meta_frag k uid dq m)).

Definition own_spec_frag γ k uid dq sp : iProp Σ :=
  own γ (◯K (mk_spec_frag k uid dq sp)).

Definition own_status_frag γ k uid dq st : iProp Σ :=
  own γ (◯K (mk_status_frag k uid dq st)).

Lemma own_auth_valid {γ state used_uids} k obj:
own_auth γ state used_uids -∗
⌜ state !! k = Some obj →
k = KObjectV.key obj ∧
KObjectV.well_formed obj ⌝.
Proof.
  iIntros "Hauth".
  iDestruct (own_valid with "Hauth") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  intros Hlookup.
  pose proof (proj1 (view_auth_dfrac_validN view_rel 0%nat 1 (state, used_uids)) Hvalid0)
    as [_ Hrel0].
  assert (Hvalid : ✓ (●K (state, used_uids))).
  { rewrite /kview_auth.
    apply (proj2 (view_auth_dfrac_valid view_rel 1 (state, used_uids))).
    split; [done|].
    intros n.
    change (view_rel_raw n (state, used_uids) ε).
    exact Hrel0.
  }
  eapply (auth_valid (state, used_uids) k obj).
  - exact Hvalid.
  - simpl. exact Hlookup.
Qed.

Lemma own_meta_valid {γ} k uid dq meta:
own_meta_frag γ k uid dq meta -∗
  ⌜ k.(KKey.Name') = meta.(ObjectMetaV.Name') ∧
  k.(KKey.Namespace') = meta.(ObjectMetaV.Namespace') ∧
  uid = meta.(ObjectMetaV.UID') ∧
  ObjectMetaV.well_formed meta ⌝.
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

Lemma own_meta_exists {γ state used_uids} k uid dq meta:
own_auth γ state used_uids -∗
own_meta_frag γ k uid dq meta -∗
  ⌜ ∃ obj, state !! k = Some obj ∧
  (KObjectV.objectmeta obj) = meta ∧
  meta.(ObjectMetaV.UID') ∈ used_uids ⌝.
Proof.
  iIntros "Hauth Hmeta".
  iDestruct (own_valid_2 with "Hauth Hmeta") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  rewrite /kview_auth /kview_frag in Hvalid0.
  pose proof (proj1 (view_both_validN view_rel 0%nat
    (state, used_uids) (mk_meta_frag k uid dq meta)) Hvalid0) as Hrel0.
  assert (Hvalid : ✓ (●K (state, used_uids) ⋅ ◯K (mk_meta_frag k uid dq meta))).
  { rewrite /kview_auth /kview_frag.
    apply (proj2 (view_both_valid view_rel (state, used_uids) (mk_meta_frag k uid dq meta))).
    intros n. exact Hrel0.
  }
  pose proof (auth_meta_valid (state, used_uids) k uid dq meta Hvalid) as Hexists.
  exact Hexists.
Qed.

Lemma own_spec_exists {γ state used_uids} k uid dq spec:
own_auth γ state used_uids -∗
own_spec_frag γ k uid dq spec -∗
  ⌜ ∀ obj, state !! k = Some obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
  (KObjectV.spec obj) = spec ⌝.
Proof.
  iIntros "Hauth Hspec".
  iDestruct (own_valid_2 with "Hauth Hspec") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  rewrite /kview_auth /kview_frag in Hvalid0.
  pose proof (proj1 (view_both_validN view_rel 0%nat
    (state, used_uids) (mk_spec_frag k uid dq spec)) Hvalid0) as Hrel0.
  assert (Hvalid : ✓ (●K (state, used_uids) ⋅ ◯K (mk_spec_frag k uid dq spec))).
  { rewrite /kview_auth /kview_frag.
    apply (proj2 (view_both_valid view_rel (state, used_uids) (mk_spec_frag k uid dq spec))).
    intros n. exact Hrel0.
  }
  intros obj Hlookup_obj Huid_obj.
  eapply (auth_spec_valid (state, used_uids) k uid dq spec Hvalid obj); simpl; eauto.
Qed.

Lemma own_status_exists {γ state used_uids} k uid dq status:
own_auth γ state used_uids -∗
own_status_frag γ k uid dq status -∗
  ⌜ ∀ obj, state !! k = Some obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
  (KObjectV.status obj) = status ⌝.
Proof.
  iIntros "Hauth Hstatus_frag".
  iDestruct (own_valid_2 with "Hauth Hstatus_frag") as "Hvalid".
  iDestruct (internal_cmra_valid_elim with "Hvalid") as %Hvalid0.
  iPureIntro.
  rewrite /kview_auth /kview_frag in Hvalid0.
  pose proof (proj1 (view_both_validN view_rel 0%nat
    (state, used_uids) (mk_status_frag k uid dq status)) Hvalid0) as Hrel0.
  assert (Hvalid : ✓ (●K (state, used_uids) ⋅ ◯K (mk_status_frag k uid dq status))).
  { rewrite /kview_auth /kview_frag.
    apply (proj2 (view_both_valid view_rel (state, used_uids) (mk_status_frag k uid dq status))).
    intros n. exact Hrel0.
  }
  intros obj Hlookup_obj Huid_obj.
  pose proof (auth_frag_valid 0%nat (state, used_uids) (mk_status_frag k uid dq status) Hvalid 0%nat)
    as Hrel.
  destruct Hrel as [_ [_ [_ Hstatus]]].
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

Lemma create_kobj_vs {γ state used_uids} k uid obj:
state !! k = None →
uid ∉ used_uids →
valid_k_uid_obj k uid obj →
no_speculative_parent_reference (KObjectV.objectmeta obj) used_uids →
own_auth γ state used_uids ==∗
  own_auth γ ((<[k := obj]> state)) (used_uids ∪ {[uid]}) ∗
  own_meta_frag γ k uid 1 (KObjectV.objectmeta obj) ∗
  own_spec_frag γ k uid 1 (KObjectV.spec obj) ∗
  own_status_frag γ k uid 1 (KObjectV.status obj).
Proof.
  iIntros (Hak Hfresh Hkuid_obj Hno_spec) "Hauth".
  iMod (own_update with "Hauth") as "H".
  { eapply create_kobj; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[H Hstatus]".
  iDestruct (own_op with "H") as "[H Hspec]".
  iDestruct (own_op with "H") as "[Hauth Hmeta]".
  iFrame.
Qed.

Lemma delete_kobj_vs {γ state used_uids k uid meta}:
own_auth γ state used_uids -∗ own_meta_frag γ k uid 1 meta ==∗
  own_auth γ (delete k state) used_uids.
Proof.
  iIntros "Hauth Hmeta".
  iMod (own_update_2 with "Hauth Hmeta") as "Hauth".
  { eapply delete_kobj; done. }
  iModIntro. done.
Qed.

Lemma update_kobj_vs {γ state used_uids k uid meta spec} prev_obj obj:
valid_k_uid_obj k uid obj →
no_speculative_parent_reference (KObjectV.objectmeta obj) used_uids →
state !! k = Some prev_obj →
(KObjectV.status prev_obj) = (KObjectV.status obj) →
own_auth γ state used_uids -∗
own_meta_frag γ k uid 1 meta -∗
own_spec_frag γ k uid 1 spec ==∗
  own_auth γ (<[k := obj]> state) used_uids ∗
  own_meta_frag γ k uid 1 (KObjectV.objectmeta obj) ∗
  own_spec_frag γ k uid 1 (KObjectV.spec obj).
Proof.
  iIntros (Hkuid_obj Hno_spec Hak Hstatus_eq) "Hauth Hmeta Hspec".
  iMod (own_update_3 with "Hauth Hmeta Hspec") as "H".
  { eapply update_kobj; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[H Hspec]".
  iDestruct (own_op with "H") as "[Hauth Hmeta]".
  iFrame.
Qed.

Lemma update_status_kobj_vs {γ state used_uids k uid meta status} prev_obj obj:
valid_k_uid_obj k uid obj →
no_speculative_parent_reference (KObjectV.objectmeta obj) used_uids →
state !! k = Some prev_obj →
(KObjectV.spec prev_obj) = (KObjectV.spec obj) →
own_auth γ state used_uids -∗
own_meta_frag γ k uid 1 meta -∗
own_status_frag γ k uid 1 status ==∗
  own_auth γ (<[k := obj]> state) used_uids ∗
  own_meta_frag γ k uid 1 (KObjectV.objectmeta obj) ∗
  own_status_frag γ k uid 1 (KObjectV.status obj).
Proof.
  iIntros (Hkuid_obj Hno_spec Hak Hspec_eq) "Hauth Hmeta Hstatus".
  iMod (own_update_3 with "Hauth Hmeta Hstatus") as "H".
  { eapply update_status_kobj; done. }
  iModIntro.
  iDestruct (own_op with "H") as "[H Hstatus]".
  iDestruct (own_op with "H") as "[Hauth Hmeta]".
  iFrame.
Qed.

End kview.
