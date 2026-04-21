From New.proof Require Export pure_objects.
From New.proof.algebra Require Export reversed_reference.

Section cview.

Class cviewG Σ :=
  { #[global] cview_reversed_referenceG ::
      @reversed_reference.reversed_referenceG
        KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ; }.

Definition cviewΣ :=
  @reversed_reference.reversed_referenceΣ
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref.

#[global]
Instance subG_cviewG Σ :
  subG cviewΣ Σ → cviewG Σ.
Proof.
  intros Hsub.
  constructor.
  exact (@reversed_reference.subG_reversed_referenceG
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ Hsub).
Qed.

Context `{!cviewG Σ}.

Definition own_auth γ (state: gmap KKey.t KObjectV.t)
    (used_reference: gset (KKey.t * types.UID.t)) : iProp Σ :=
  @reversed_reference.own_auth
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ _
    γ state used_reference.

Definition mk_frag (key: KKey.t) (uid: types.UID.t) (dq: dfrac) (ks: gset KKey.t) :=
  @reversed_reference.mk_frag
    KKey.t _ _ (KKey.t * types.UID.t) _ _
    (key, uid) dq ks.

Definition own_frag γ (key: KKey.t) (uid: types.UID.t) dq (ks: gset KKey.t) : iProp Σ :=
  @reversed_reference.own_frag
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ _
    γ (key, uid) dq ks.

Global Instance own_auth_timeless γ state used_reference :
  Timeless (own_auth γ state used_reference).
Proof. unfold own_auth. apply _. Qed.

Global Instance own_frag_timeless γ key uid dq ks :
  Timeless (own_frag γ key uid dq ks).
Proof. unfold own_frag. apply _. Qed.

Lemma own_auth_frag_valid {γ state used_reference pk puid dq ks}:
  own_auth γ state used_reference -∗
  own_frag γ pk puid dq ks -∗
  ⌜ ks = dom (filter (λ '(_, v), obj_parent_ref v = Some (pk, puid)) state) ⌝ ∗
  ⌜ (pk, puid) ∈ used_reference ⌝.
Proof.
  unfold own_auth, own_frag.
  apply (@reversed_reference.own_auth_frag_valid
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ _
    γ state used_reference (pk, puid) dq ks).
Qed.

Lemma own_auth_frag_valid2 {γ state used_reference pk puid dq ks}:
  map_Forall (λ k obj, k.(KKey.Namespace') = (KObjectV.objectmeta obj).(ObjectMetaV.Namespace')) state →
  own_auth γ state used_reference -∗
  own_frag γ pk puid dq ks -∗
  ⌜ set_Forall (λ k, k.(KKey.Namespace') = pk.(KKey.Namespace')) ks ⌝.
Proof.
  iIntros (Hkey_namespace) "Hauth Hfrag".
  iDestruct (own_auth_frag_valid with "Hauth Hfrag") as %[Hks _].
  iPureIntro.
  unfold set_Forall.
  intros k Hk.
  rewrite Hks in Hk.
  apply elem_of_dom in Hk as [obj Hlookup].
  apply map_lookup_filter_Some in Hlookup as [Hlookup Hparent].
  rewrite (map_Forall_lookup_1 _ _ _ _ Hkey_namespace Hlookup).
  unfold obj_parent_ref, meta_parent_ref in Hparent.
  destruct ((KObjectV.objectmeta obj).(ObjectMetaV.OwnerReferences')) as [orefs|]
    eqn:Horefs; simpl in Hparent; [|discriminate].
  destruct (list_find (λ oref : OwnerReferenceV.t, oref.(OwnerReferenceV.Controller') = Some true) orefs)
    as [[idx oref]|] eqn:Hfind; simpl in Hparent; [|discriminate].
  inversion Hparent; done.
Qed.


Lemma create_child_vs {γ state used_reference pk puid ks} k uid v cks:
  uid = (KObjectV.objectmeta v).(ObjectMetaV.UID') →
  state !! k = None →
  obj_parent_ref v = Some (pk, puid) →
  dom (filter (λ '(_, v'), obj_parent_ref v' = Some (k, uid)) state) = cks →
  uid ∉ (set_map snd used_reference : gset types.UID.t) →
  own_auth γ state used_reference -∗
  own_frag γ pk puid 1 ks ==∗
    own_auth γ (<[k := v]> state) (used_reference ∪ {[(k, uid)]}) ∗
    own_frag γ pk puid 1 (ks ∪ {[k]}) ∗
    own_frag γ k uid 1 cks.
Proof.
  iIntros (Huid Hak Hparent Hcks Hfresh_uid) "Hauth Hfrag".
  iAssert (⌜ (pk, puid) ∈ used_reference ⌝)%I as %Hparent_used.
  { iPoseProof (own_auth_frag_valid with "[$Hauth] [$Hfrag]") as "[_ $]". }
  subst uid.
  assert (Hself : obj_ref k v ≠ (pk, puid)).
  { intros Heq.
    unfold obj_ref in Heq.
    injection Heq as _ Huid_eq.
    apply Hfresh_uid.
    rewrite Huid_eq.
    change (snd (pk, puid) ∈
      (set_map (λ ku : KKey.t * types.UID.t, snd ku) used_reference : gset types.UID.t)).
    eapply (elem_of_map_2 (λ ku : KKey.t * types.UID.t, snd ku)).
    exact Hparent_used.
  }
  assert (Hpairfresh : obj_ref k v ∉ used_reference).
  { intros Hin.
    apply Hfresh_uid.
    change (snd (obj_ref k v) ∈
      (set_map (λ ku : KKey.t * types.UID.t, snd ku) used_reference : gset types.UID.t)).
    eapply (elem_of_map_2 (λ ku : KKey.t * types.UID.t, snd ku)).
    exact Hin.
  }
  unfold own_auth, own_frag.
  iMod (@reversed_reference.create_reference_vs
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ _
    γ state used_reference (pk, puid) ks k v cks
    with "Hauth Hfrag") as "(Hauth & Hfrag & Hchildfrag)".
  - exact Hak.
  - exact Hparent.
  - exact Hself.
  - unfold obj_ref. exact Hcks.
  - exact Hpairfresh.
  - iModIntro. iFrame.
Qed.

Lemma create_child_vs2 {γ state used_reference pk puid ks} k uid v:
  uid = (KObjectV.objectmeta v).(ObjectMetaV.UID') →
  state !! k = None →
  obj_parent_ref v = Some (pk, puid) →
  map_Forall (λ k v,
    no_speculative_parent_reference (KObjectV.objectmeta v) (set_map snd used_reference : gset types.UID.t)
  ) state →
  uid ∉ (set_map snd used_reference : gset types.UID.t) →
  own_auth γ state used_reference -∗
  own_frag γ pk puid 1 ks ==∗
    own_auth γ (<[k := v]> state) (used_reference ∪ {[(k, uid)]}) ∗
    own_frag γ pk puid 1 (ks ∪ {[k]}) ∗
    own_frag γ k uid 1 ∅.
Proof.
  iIntros (Huid Hak Hparent Hvalid Hfresh_uid) "Hauth Hfrag".
  subst uid.
  assert (Hcks :
    dom (filter (λ '(_, v'), obj_parent_ref v' = Some (k, obj_ref k v).2) state) = (∅ : gset KKey.t)).
  { apply dom_empty_iff_L.
    apply map_empty.
    intros k'.
    rewrite map_lookup_filter.
    destruct (state !! k') as [obj|] eqn:Hlookup; [|done].
    simpl.
    case_decide as Hparent_to_new.
    - exfalso.
      pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup) as Hno_spec.
      apply Hfresh_uid.
      unfold no_speculative_parent_reference in Hno_spec.
      unfold obj_parent_ref, meta_parent_ref in Hparent_to_new.
      destruct ((KObjectV.objectmeta obj).(ObjectMetaV.OwnerReferences')) as [orefs|] eqn:Horefs; [|done].
      destruct (list_find (λ oref : OwnerReferenceV.t, oref.(OwnerReferenceV.Controller') = Some true) orefs)
        as [[idx oref]|] eqn:Hfind; [|done].
      injection Hparent_to_new as _ Huid_eq.
      rewrite <- Huid_eq.
      eapply Hno_spec.
      unfold meta_parent_ref_is, meta_parent_ref.
      rewrite Horefs Hfind.
      done.
    - done.
  }
  iMod (create_child_vs k (obj_ref k v).2 v ∅ with "Hauth Hfrag")
    as "(Hauth & Hfrag & Hchildfrag)".
  - reflexivity.
  - exact Hak.
  - exact Hparent.
  - rewrite /obj_ref /=. exact Hcks.
  - exact Hfresh_uid.
  - iModIntro. iFrame.
Qed.

Lemma adopt_orphan_vs {γ state used_reference pk puid ks} k v v':
  state !! k = Some v →
  obj_parent_ref v = None →
  obj_parent_ref v' = Some (pk, puid) →
  (KObjectV.objectmeta v).(ObjectMetaV.UID') = (KObjectV.objectmeta v').(ObjectMetaV.UID') →
  own_auth γ state used_reference -∗
  own_frag γ pk puid 1 ks ==∗
    own_auth γ (<[k := v']> state) used_reference ∗
    own_frag γ pk puid 1 (ks ∪ {[k]}).
Proof.
  intros Hak Hnone Hparent Huid.
  assert (Hg : obj_ref k v = obj_ref k v').
  { unfold obj_ref.
    simpl.
    rewrite Huid.
    done.
  }
  unfold own_auth, own_frag.
  eapply (@reversed_reference.set_reference_vs
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ _
    γ state used_reference (pk, puid) ks); eauto.
Qed.

Lemma release_child_vs {γ state used_reference pk puid ks} k v v':
  state !! k = Some v →
  obj_parent_ref v = Some (pk, puid) →
  obj_parent_ref v' = None →
  (KObjectV.objectmeta v).(ObjectMetaV.UID') = (KObjectV.objectmeta v').(ObjectMetaV.UID') →
  own_auth γ state used_reference -∗
  own_frag γ pk puid 1 ks ==∗
    own_auth γ (<[k := v']> state) used_reference ∗
    own_frag γ pk puid 1 (ks ∖ {[k]}).
Proof.
  intros Hak Hparent Hnone Hg.
  assert (Hobj_ref : obj_ref k v = obj_ref k v').
  { unfold obj_ref.
    simpl.
    rewrite Hg.
    done.
  }
  unfold own_auth, own_frag.
  eapply (@reversed_reference.unset_reference_vs
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ _
    γ state used_reference (pk, puid) ks); eauto.
Qed.

Lemma delete_child_vs {γ state used_reference pk puid ks} k v:
  state !! k = Some v →
  obj_parent_ref v = Some (pk, puid) →
  own_auth γ state used_reference -∗
  own_frag γ pk puid 1 ks ==∗
    own_auth γ (delete k state) used_reference ∗
    own_frag γ pk puid 1 (ks ∖ {[k]}).
Proof.
  intros Hak Hparent.
  unfold own_auth, own_frag.
  eapply (@reversed_reference.delete_reference_vs
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ _
    γ state used_reference (pk, puid) ks); eauto.
Qed.

Lemma delete_child_vs2 {γ state used_reference pk puid ks} k:
  k ∈ ks →
  own_auth γ state used_reference -∗
  own_frag γ pk puid 1 ks ==∗
    own_auth γ (delete k state) used_reference ∗
    own_frag γ pk puid 1 (ks ∖ {[k]}).
Proof.
  intros Hk.
  unfold own_auth, own_frag.
  eapply (@reversed_reference.delete_reference_vs2
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ _
    γ state used_reference (pk, puid) ks); eauto.
Qed.

Lemma simple_update_vs {γ state used_reference} k v v':
  state !! k = Some v →
  obj_parent_ref v = obj_parent_ref v' →
  (KObjectV.objectmeta v).(ObjectMetaV.UID') = (KObjectV.objectmeta v').(ObjectMetaV.UID') →
  own_auth γ state used_reference ==∗
    own_auth γ (<[k := v']> state) used_reference.
Proof.
  intros Hak Hparent Href.
  assert (Hobj_ref : obj_ref k v = obj_ref k v').
  { unfold obj_ref.
    simpl.
    rewrite Href.
    done.
  }
  unfold own_auth.
  eapply (@reversed_reference.simple_update_vs
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ _
    γ state used_reference); eauto.
Qed.

Lemma create_orphan_vs {γ state used_reference} k uid v cks:
  uid = (KObjectV.objectmeta v).(ObjectMetaV.UID') →
  state !! k = None →
  obj_parent_ref v = None →
  dom (filter (λ '(_, v'), obj_parent_ref v' = Some (obj_ref k v)) state) = cks →
  uid ∉ (set_map snd used_reference : gset types.UID.t) →
  own_auth γ state used_reference ==∗
    own_auth γ (<[k := v]> state) (used_reference ∪ {[obj_ref k v]}) ∗
    own_frag γ k uid 1 cks.
Proof.
  intros Huid Hak Hnone Hcks Hfresh.
  subst uid.
  assert (Hpairfresh : obj_ref k v ∉ used_reference).
  { intros Hin.
    apply Hfresh.
    change (snd (obj_ref k v) ∈
      (set_map (λ ku : KKey.t * types.UID.t, snd ku) used_reference : gset types.UID.t)).
    eapply (elem_of_map_2 (λ ku : KKey.t * types.UID.t, snd ku)).
    exact Hin.
  }
  unfold own_auth, own_frag.
  eapply (@reversed_reference.simple_create_vs
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ _
    γ state used_reference); eauto.
Qed.

Lemma create_orphan_vs2 {γ state used_reference} k uid v:
  uid = (KObjectV.objectmeta v).(ObjectMetaV.UID') →
  state !! k = None →
  obj_parent_ref v = None →
  map_Forall (λ k v,
    no_speculative_parent_reference (KObjectV.objectmeta v) (set_map snd used_reference : gset types.UID.t)
  ) state →
  uid ∉ (set_map snd used_reference : gset types.UID.t) →
  own_auth γ state used_reference ==∗
    own_auth γ (<[k := v]> state) (used_reference ∪ {[obj_ref k v]}) ∗
    own_frag γ k uid 1 ∅.
Proof.
  iIntros (Huid Hak Hnone Hvalid Hfresh) "Hauth".
  subst uid.
  assert (Hcks :
    dom (filter (λ '(_, v'), obj_parent_ref v' = Some (obj_ref k v)) state) = (∅ : gset KKey.t)).
  { apply dom_empty_iff_L.
    apply map_empty.
    intros k'.
    rewrite map_lookup_filter.
    destruct (state !! k') as [obj|] eqn:Hlookup; [|done].
    simpl.
    case_decide as Hparent_to_new.
    - exfalso.
      pose proof (map_Forall_lookup_1 _ _ _ _ Hvalid Hlookup) as Hno_spec.
      apply Hfresh.
      unfold no_speculative_parent_reference in Hno_spec.
      unfold obj_parent_ref, meta_parent_ref in Hparent_to_new.
      destruct ((KObjectV.objectmeta obj).(ObjectMetaV.OwnerReferences')) as [orefs|] eqn:Horefs; [|done].
      destruct (list_find (λ oref : OwnerReferenceV.t, oref.(OwnerReferenceV.Controller') = Some true) orefs)
        as [[idx oref]|] eqn:Hfind; [|done].
      injection Hparent_to_new as _ Huid_eq.
      rewrite <- Huid_eq.
      eapply Hno_spec.
      unfold meta_parent_ref_is, meta_parent_ref.
      rewrite Horefs Hfind.
      done.
    - done.
  }
  iMod (create_orphan_vs k (obj_ref k v).2 v ∅ with "Hauth") as "(Hauth & Hfrag)".
  - reflexivity.
  - exact Hak.
  - exact Hnone.
  - exact Hcks.
  - exact Hfresh.
  - iModIntro. iFrame.
Qed.

Lemma delete_orphan_vs {γ state used_reference} k v:
  state !! k = Some v →
  obj_parent_ref v = None →
  own_auth γ state used_reference ==∗
    own_auth γ (delete k state) used_reference.
Proof.
  intros Hak Hnone.
  unfold own_auth.
  eapply (@reversed_reference.simple_delete_vs
    KKey.t _ _ (KKey.t * types.UID.t) _ _ KObjectV.t obj_parent_ref obj_ref Σ _
    γ state used_reference); eauto.
Qed.

End cview.
