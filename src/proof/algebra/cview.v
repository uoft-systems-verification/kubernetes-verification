From New.proof Require Export pure_objects.
From New.proof.algebra Require Export reversed_reference.

Section cview.

Class cviewG Σ :=
  { #[global] cview_reversed_referenceG ::
      reversed_reference.reversed_referenceG
        (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
        (f:=obj_parent_ref) (g:=obj_ref) Σ; }.

Definition cviewΣ :=
  reversed_reference.reversed_referenceΣ
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref).

#[global]
Instance subG_cviewG Σ :
  subG cviewΣ Σ → cviewG Σ.
Proof.
  intros Hsub.
  constructor.
  exact (reversed_reference.subG_reversed_referenceG
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref)
    Σ Hsub).
Qed.

Context `{!cviewG Σ}.

Definition own_auth γ (state: gmap KKey.t KObjectV.t)
    (used_reference: gset (KKey.t * types.UID.t)) : iProp Σ :=
  reversed_reference.own_auth
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref)
    γ state used_reference.

Definition mk_frag (r: KKey.t * types.UID.t) (dq: dfrac) (ks: gset KKey.t) :=
  reversed_reference.mk_frag
    (K:=KKey.t) (R:=KKey.t * types.UID.t)
    r dq ks.

Definition own_frag γ (r: KKey.t * types.UID.t) dq (ks: gset KKey.t) : iProp Σ :=
  reversed_reference.own_frag
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref)
    γ r dq ks.

Global Instance own_auth_timeless γ state used_reference :
  Timeless (own_auth γ state used_reference).
Proof. unfold own_auth. apply _. Qed.

Global Instance own_frag_timeless γ r dq ks :
  Timeless (own_frag γ r dq ks).
Proof. unfold own_frag. apply _. Qed.

Lemma own_auth_frag_valid {γ state used_reference r dq ks}:
  own_auth γ state used_reference -∗
  own_frag γ r dq ks -∗
  ⌜ ks = dom (filter (λ '(_, v), obj_parent_ref v = Some r) state) ⌝ ∗
  ⌜ r ∈ used_reference ⌝.
Proof.
  unfold own_auth, own_frag.
  apply (reversed_reference.own_auth_frag_valid
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref)).
Qed.

Lemma create_child_vs {γ state used_reference r ks} k v cks:
  state !! k = None →
  obj_parent_ref v = Some r →
  obj_ref k v ≠ r →
  dom (filter (λ '(_, v'), obj_parent_ref v' = Some (obj_ref k v)) state) = cks →
  obj_ref k v ∉ used_reference →
  own_auth γ state used_reference -∗
  own_frag γ r 1 ks ==∗
    own_auth γ (<[k := v]> state) (used_reference ∪ {[obj_ref k v]}) ∗
    own_frag γ r 1 (ks ∪ {[k]}) ∗
    own_frag γ (obj_ref k v) 1 cks.
Proof.
  intros Hak Hparent Hself Hcks Hfresh.
  unfold own_auth, own_frag.
  eapply (reversed_reference.create_child_vs
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref)); eauto.
Qed.

Lemma adopt_orphan_vs {γ state used_reference r ks} k v v':
  state !! k = Some v →
  obj_parent_ref v = None →
  obj_parent_ref v' = Some r →
  obj_ref k v = obj_ref k v' →
  own_auth γ state used_reference -∗
  own_frag γ r 1 ks ==∗
    own_auth γ (<[k := v']> state) used_reference ∗
    own_frag γ r 1 (ks ∪ {[k]}).
Proof.
  intros Hak Hnone Hparent Hg.
  unfold own_auth, own_frag.
  eapply (reversed_reference.adopt_orphan_vs
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref)); eauto.
Qed.

Lemma release_child_vs {γ state used_reference r ks} k v v':
  state !! k = Some v →
  obj_parent_ref v = Some r →
  obj_parent_ref v' = None →
  obj_ref k v = obj_ref k v' →
  own_auth γ state used_reference -∗
  own_frag γ r 1 ks ==∗
    own_auth γ (<[k := v']> state) used_reference ∗
    own_frag γ r 1 (ks ∖ {[k]}).
Proof.
  intros Hak Hparent Hnone Hg.
  unfold own_auth, own_frag.
  eapply (reversed_reference.release_child_vs
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref)); eauto.
Qed.

Lemma delete_child_vs {γ state used_reference r ks} k v:
  state !! k = Some v →
  obj_parent_ref v = Some r →
  own_auth γ state used_reference -∗
  own_frag γ r 1 ks ==∗
    own_auth γ (delete k state) used_reference ∗
    own_frag γ r 1 (ks ∖ {[k]}).
Proof.
  intros Hak Hparent.
  unfold own_auth, own_frag.
  eapply (reversed_reference.delete_child_vs
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref)); eauto.
Qed.

Lemma delete_child_vs2 {γ state used_reference r ks} k:
  k ∈ ks →
  own_auth γ state used_reference -∗
  own_frag γ r 1 ks ==∗
    own_auth γ (delete k state) used_reference ∗
    own_frag γ r 1 (ks ∖ {[k]}).
Proof.
  intros Hk.
  unfold own_auth, own_frag.
  eapply (reversed_reference.delete_child_vs2
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref)); eauto.
Qed.

Lemma simple_update_vs {γ state used_reference} k v v':
  state !! k = Some v →
  obj_parent_ref v = obj_parent_ref v' →
  obj_ref k v = obj_ref k v' →
  own_auth γ state used_reference ==∗
    own_auth γ (<[k := v']> state) used_reference.
Proof.
  intros Hak Hparent Href.
  unfold own_auth.
  eapply (reversed_reference.simple_update_vs
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref)); eauto.
Qed.

Lemma create_orphan_vs {γ state used_reference} k v cks:
  state !! k = None →
  obj_parent_ref v = None →
  dom (filter (λ '(_, v'), obj_parent_ref v' = Some (obj_ref k v)) state) = cks →
  obj_ref k v ∉ used_reference →
  own_auth γ state used_reference ==∗
    own_auth γ (<[k := v]> state) (used_reference ∪ {[obj_ref k v]}) ∗
    own_frag γ (obj_ref k v) 1 cks.
Proof.
  intros Hak Hnone Hcks Hfresh.
  unfold own_auth, own_frag.
  eapply (reversed_reference.create_orphan_vs
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref)); eauto.
Qed.

Lemma delete_orphan_vs {γ state used_reference} k v:
  state !! k = Some v →
  obj_parent_ref v = None →
  own_auth γ state used_reference ==∗
    own_auth γ (delete k state) used_reference.
Proof.
  intros Hak Hnone.
  unfold own_auth.
  eapply (reversed_reference.delete_orphan_vs
    (K:=KKey.t) (R:=KKey.t * types.UID.t) (V:=KObjectV.t)
    (f:=obj_parent_ref) (g:=obj_ref)); eauto.
Qed.

End cview.
